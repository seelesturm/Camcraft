//! The trochoidal fallback's plan (issue #5 round 2; the loops and the
//! medial line in `trochoid` and `medial`, provenance there): where the
//! HSM spiral refuses a channel, one descent at the medial line's start
//! (the entry law's helix, then an opening spiral out to the loop
//! radius), the front arcs along the line - each reached from the last
//! by a microlift return lifted over the cleared floor (Otkur & Lazoglu
//! 2007, the trochoid's non-cutting return), so no feed crosses another
//! (the verifier's crossing law) - and the wall laps last: the arcs'
//! end flows tangentially onto the center area's own boundary, lapped
//! with its corners rounded from the tool radius down (`wall`), so the
//! walls are cut to size. Every cut is read on the planner's stock
//! against the spiral's load bound before it is kept; anything that
//! does not hold is refused by name. Ours, no vendor material.

use crate::geo2d::{Point2, Region};
use crate::load::{deg_at_rim, load_at_rim};
use crate::machining2d::slots::chord_clears;

use super::front::{dist, rotate_to, tail};
use super::lift_link::{GRAZE, LIFTS, Leg, Return, crosses_any, legs};
use super::lift_split::seg_dist;
use super::loops::boundary_dist;
use super::medial::{Spine, spine};
use super::raster::Raster;
use super::rings::circle;
use super::spiral::revolution;
use super::star::orbit_radius;
use super::trochoid::choose_step;
use super::{AdaptivePlan, AdaptiveSpec, BITE_LOAD, GRID_PER_D, GenError, SPIRAL_STEPS, lift, wall};

/// A trochoid of more loops a level than this is impractical (the
/// user's 14 mm band reads 2575 at its load): refused by name, the
/// Offset rings cut the area (a practical band step is a follow-up).
pub(crate) const LOOP_CAP: usize = 600;

/// The trochoid's entry helix takes at most this share of the medial
/// line start's clearance (the seed sits a helix radius behind it).
pub(crate) const HELIX_SHARE: f64 = 0.375;

/// The seed sits this much (mm) further behind the line's start than
/// the helix radius.
const SEED_GAP: f64 = 0.1;

/// The opening grows about the seed to this share of its clearance,
/// then shifts onto the loop circle about the line's start.
const OPEN_SHARE: f64 = 0.8;

/// The loop radius stays this share of the half-width inside the least
/// clearance along the medial line (the tool center never leaves the
/// center area).
const RHO_MARGIN: f64 = 0.05;

/// The front arcs' chord sagitta (mm): about 3 degrees a joint on a
/// D10's loops, under the 5-degree break law.
const ARC_SAG: f64 = 0.002;

/// The blend from the last arc onto the wall lap joins the lap this far
/// (mm) along it from the arc's end.
const BLEND_RUN: f64 = 3.0;

/// The wall laps' corner radii, as shares of the half-width: each lap
/// rounds the corners tighter, the corner stock eased off lap by lap ...
const LAP_SHARES: [f64; 6] = [1.0, 0.8, 0.65, 0.5, 0.4, 0.3];

/// The laps' nesting step (mm) and the run (mm) the hop from one lap
/// onto the next takes along them.
const LAP_EPS: f64 = 0.002;
const LAP_HOP: f64 = 1.0;

/// ... down to this share of the tool radius (the corner scallop left
/// for the finishing pass).
const LAP_MIN_PER_R: f64 = 0.25;

/// The laps' corner arcs turn at most this much a joint (degrees).
const LAP_DEG: f64 = 3.0;

/// A return keeps this far off the entry helix's circle (mm).
const ORBIT_GAP: f64 = 0.05;

/// Opening revolutions at most (the Prime Directive's "never hang").
const MAX_OPEN: usize = 400;

/// Keep the worse of two readings.
fn up(worst: &mut (f64, Point2), w: (f64, Point2)) {
    if w.0 > worst.0 {
        *worst = w;
    }
}

/// The entry: on the medial line's axis, behind its start by the helix
/// radius and a margin, so the first returns (about one and a half
/// steps past the start) pass clear of the helix circle every level's
/// descent sweeps; the helix at most [`HELIX_SHARE`] of the start's
/// clearance. Returns the spot and the helix radius, or why not.
pub(crate) fn seed(center: &Region, helix_r: f64) -> Result<Result<(Point2, f64), String>, GenError> {
    let sp = match spine(center)? {
        Ok((sp, _)) => sp,
        Err(why) => return Ok(Err(why)),
    };
    let pts = sp.points();
    let len = super::medial::lengths(pts);
    let total = len.last().copied().unwrap_or(0.0);
    let (Some(&c0), ahead) = (pts.first(), super::medial::at_len(pts, &len, total.min(2.0))) else {
        return Ok(Err("its medial line is empty".into()));
    };
    let l = dist(c0, ahead);
    if l < 1e-6 {
        return Ok(Err("its medial line is degenerate".into()));
    }
    let tg = Point2::new((ahead.x - c0.x) / l, (ahead.y - c0.y) / l);
    let hr = helix_r.max(0.0).min(HELIX_SHARE * boundary_dist(center, c0));
    let back = hr + SEED_GAP;
    let sd = Point2::new(c0.x - back * tg.x, c0.y - back * tg.y);
    if !center.contains(sd) || boundary_dist(center, sd) < hr + 0.5 * SEED_GAP {
        return Ok(Err("has no entry room behind its medial line's start".into()));
    }
    Ok(Ok((sd, hr)))
}

/// What a trochoid return is proved against: inside the center area,
/// its swept disc on no stock but a graze (lifted, it never cuts),
/// landing where the tool disc holds no stock, off the entry orbit, and
/// - at the lowest lift that does - crossing no earlier return.
struct Law<'a> {
    ras: &'a Raster,
    center: &'a Region,
    r: f64,
    orbit: (Point2, f64),
    /// The landing law (rim, step, bite): the ramp's last run reads air
    /// - a descent onto stock is one more descent into it.
    land: Option<(f64, f64, f64)>,
}

impl Law<'_> {
    /// Why the leg `l` is illegal, or `None`.
    fn leg_bad(&self, l: &Leg) -> Option<&'static str> {
        let (a, b) = (l.0, l.1);
        if dist(a, b) >= 1e-9 && !chord_clears(self.center, a, b) {
            return Some("leaves the center area");
        }
        if dist(a, b) >= 1e-9 && !self.ras.capsule_clear(a, b, self.r - GRAZE - self.ras.h) {
            return Some("sweeps standing stock");
        }
        (self.orbit.1 > 1e-6 && seg_dist(self.orbit.0, a, b) <= self.orbit.1 + ORBIT_GAP).then_some("sweeps the entry helix")
    }

    /// The return from `a` onto `b`, or why none is legal.
    fn ret(&self, a: Point2, b: Point2, links: &[Vec<Leg>]) -> Result<Return, &'static str> {
        if !self.ras.stock_clear(b, self.r - GRAZE - self.ras.h) {
            return Err("lands on standing stock");
        }
        let mut ret = Return { lift: LIFTS[0], high: false, up: Vec::new(), via: Vec::new(), down: vec![b] };
        if let Some(why) = legs(a, &ret).iter().find_map(|l| self.leg_bad(l)) {
            return Err(why);
        }
        if let (Some((rim, step, bite)), Some(l)) = (self.land, legs(a, &ret).last())
            && self.ras.peek(&[l.0, l.1], rim, step) > bite
        {
            return Err("lands on a loop start already in cut (a descent into stock every loop, over the one-descent law)");
        }
        for lift in LIFTS {
            ret.lift = lift;
            if !crosses_any(&legs(a, &ret), links) {
                return Ok(ret);
            }
        }
        Err("crosses an earlier return at every lift")
    }
}

/// The trochoid's plan for the channel `center` (reach: what the cutter
/// can reach), entered as `s` says at the medial line's start; refused
/// by name (`AdaptivePlan::refused`) where any law does not hold.
pub(crate) fn plan(reach: &Region, center: &Region, s: &AdaptiveSpec) -> Result<AdaptivePlan, GenError> {
    plan_with(reach, center, s, true)
}

/// [`plan`], the landing law held or (`landing` false: the unit test
/// that pins the rest of the plan while the law is owed) not.
pub(super) fn plan_with(reach: &Region, center: &Region, s: &AdaptiveSpec, landing: bool) -> Result<AdaptivePlan, GenError> {
    let refuse = |why: String| Ok(AdaptivePlan { refused: Some(why), ..AdaptivePlan::default() });
    if !(s.r > 0.0 && s.load > 0.0) {
        return Err(GenError::Invalid("trochoid plan needs positive radius and load".into()));
    }
    let (sp, c) = match spine(center)? {
        Ok(v) => v,
        Err(why) => return refuse(why),
    };
    let rho = sp.points().iter().map(|&p| boundary_dist(center, p)).fold(c, f64::min) - RHO_MARGIN * c;
    if !(rho > 0.6 * c && rho > s.helix_r + 0.1 * s.r) {
        return refuse(format!("has only {rho:.2} mm of loop radius along its medial line"));
    }
    let d = 2.0 * s.r;
    let mut ras = Raster::from_region(reach, d / GRID_PER_D, s.r)?;
    let rim = crate::quality::rim_for(d, ras.h);
    let bound = deg_at_rim(s.load * (1.0 + s.tol), d, rim);
    let bite = deg_at_rim(BITE_LOAD, d, rim);
    let (step, seg) = (s.r / 10.0, s.r / 8.0);
    let ladder: Vec<f64> = SPIRAL_STEPS.iter().map(|f| d * s.load * f).collect();
    let spine_len = super::medial::lengths(sp.points()).last().copied().unwrap_or(0.0);
    if spine_len / ladder[0] > LOOP_CAP as f64 {
        return refuse(format!("would cut over {LOOP_CAP} loops a level along its {spine_len:.0} mm medial line"));
    }
    if s.bore > 0.0 {
        ras.cut(s.seed, s.seed, s.bore);
    }
    let ras0 = ras.clone();
    let mut worst = (0.0f64, s.start);
    // The opening: the helix's orbit walked flat, then revolutions out
    // to the loop radius, each step the largest the load holds.
    let mut walk = vec![s.start];
    let mut prev = circle(s.seed, orbit_radius(s), s.start, s.climb, seg);
    if s.helix_r > 1e-6 {
        walk.extend(prev.iter().skip(1).copied());
    }
    up(&mut worst, ras.walk(&prev, s.r, rim, step));
    // About the seed to `ro`, then the center shifts onto the line's
    // start `c0` while the radius grows to `rho` (each ring nested in
    // the next: the radius grows faster than the center moves).
    let Some(&c0) = sp.points().first() else { return refuse("its medial line is empty".into()) };
    let shift = dist(s.seed, c0);
    let ro = (OPEN_SHARE * boundary_dist(center, s.seed)).min(rho).max(orbit_radius(s));
    if rho - ro <= shift + 0.1 {
        return refuse("has no room to open out to its loops".into());
    }
    let (mut rr, mut t) = (orbit_radius(s), 0.0f64);
    let ring_at = |rr: f64, t: f64| -> (Point2, f64) {
        if t <= 0.0 {
            (s.seed, rr)
        } else {
            (Point2::new(s.seed.x + t * (c0.x - s.seed.x), s.seed.y + t * (c0.y - s.seed.y)), ro + t * (rho - ro))
        }
    };
    for _ in 0..MAX_OPEN {
        if t >= 1.0 - 1e-12 {
            break;
        }
        let mut kept = None;
        for (i, &w) in ladder.iter().enumerate() {
            let (nr, nt) = if rr < ro - 1e-9 { ((rr + w).min(ro), 0.0) } else { (ro, (t + w / (shift + rho - ro)).min(1.0)) };
            let (cc, rad) = ring_at(nr, nt);
            let ring = circle(cc, rad, prev[0], s.climb, seg);
            let rev = revolution(&prev, &ring);
            let mut trial = ras.clone();
            let w = trial.walk(&rev, s.r, rim, step);
            if w.0 <= bound || i + 1 == ladder.len() {
                kept = Some((nr, nt, ring, rev, trial, w));
                break;
            }
        }
        let Some((nr, nt, ring, rev, trial, w)) = kept else { break };
        up(&mut worst, w);
        ras = trial;
        walk.extend(rev.iter().skip(1).copied());
        (prev, rr, t) = (ring, nr, nt);
    }
    up(&mut worst, ras.walk(&prev, s.r, rim, step));
    walk.extend(prev.iter().skip(1).copied());
    if worst.0 > bound {
        return refuse(format!("its opening reads {:.1}% of D at its entry", load_at_rim(worst.0, d, rim) * 100.0));
    }
    // The loops: the largest step whose first loops hold the load.
    let Some((st, arcs)) = choose_step(&ras, &sp, (rho, s.climb, ARC_SAG), &ladder, (s.r, rim, step, bound)) else {
        return refuse("holds the load at no step of the ladder".into());
    };
    if arcs.len() > LOOP_CAP {
        return refuse(format!("would cut {} loops a level at a {st:.3} mm step (over the {LOOP_CAP} cap)", arcs.len()));
    }
    if matches!(sp, Spine::Closed(_)) || center.loops().len() != 1 {
        return refuse("is a closed band (its trochoid is not wired yet)".into());
    }
    if !arcs.iter().flatten().all(|&p| center.contains(p) || boundary_dist(center, p) < 1e-6) {
        return refuse("has loops leaving the center area".into());
    }
    // The opening's last ring is the first loop whole (the first arc is
    // its front: cut already); the first return leaves from its seam.
    let mut passes = vec![walk];
    let mut joins: Vec<Option<Return>> = vec![None];
    let mut links: Vec<Vec<Leg>> = Vec::new();
    for (k, arc) in arcs.iter().enumerate().skip(1) {
        let (Some(&at), Some(&b)) = (passes.last().and_then(|p| p.last()), arc.first()) else { continue };
        let law = Law { ras: &ras, center, r: s.r, orbit: (s.seed, s.helix_r), land: landing.then_some((rim, step, bite)) };
        let ret = match law.ret(at, b, &links) {
            Ok(r) => r,
            Err(why) => return refuse(format!("has no lifted return onto loop {k} at ({:.2}, {:.2}): it {why}", b.x, b.y)),
        };
        let w = ras.walk(arc, s.r, rim, step);
        if w.0 > bound {
            return refuse(format!("loop {k} reads {:.1}% of D at ({:.2}, {:.2})", load_at_rim(w.0, d, rim) * 100.0, w.1.x, w.1.y));
        }
        up(&mut worst, w);
        links.push(legs(at, &ret));
        passes.push(arc.clone());
        joins.push(Some(ret));
    }
    // The wall laps: the last arc's end blended onto the lap ahead.
    let Some(last) = passes.last().cloned() else { return refuse("has no loops".into()) };
    let (Some(&e), hd) = (last.last(), tail(&last)) else { return refuse("has no loops".into()) };
    // The first lap rounds the corners at the half-width (a channel's
    // ends: semicircles about the loops' own ends); each lap after it
    // the tightest radius of the ladder that holds the load.
    let mut radii: Vec<f64> = LAP_SHARES.iter().map(|f| f * c).collect();
    radii.push(LAP_MIN_PER_R * s.r);
    radii.retain(|&rr| rr >= LAP_MIN_PER_R * s.r - 1e-9);
    // Lap k runs `LAP_EPS` per rung inside the next (all nested, none
    // touching another: shared straights would cross on round-off).
    let n = radii.len();
    let mut ladder_laps = Vec::with_capacity(n);
    for (k, &rr) in radii.iter().enumerate() {
        let inset = center.offset(-LAP_EPS * (n - 1 - k) as f64)?;
        ladder_laps.push(wall::laps_at(&inset, s.climb, rr, seg, LAP_DEG));
    }
    let Some((j, tj)) = ladder_laps[0].0.first().and_then(|l| wall::along(&rotate_to(l, e), BLEND_RUN)) else {
        return refuse("has no room to blend onto its wall lap".into());
    };
    let lead = wall::blend(e, hd, j, tj);
    if !lead.iter().all(|&p| center.contains(p) || boundary_dist(center, p) < 1e-6) {
        return refuse("has no blend onto its wall lap inside the center area".into());
    }
    let mut fin: Vec<Point2> = Vec::new();
    let mut pulled = None;
    let mut at = 0usize;
    let mut first = true;
    // Where the next lap is joined: a hair ahead of the last one's seam,
    // so the hop between two nested laps runs along them, not across.
    let mut join = j;
    while first || at + 1 < radii.len() {
        let order: Vec<usize> = if first { vec![0] } else { (at + 1..radii.len()).rev().collect() };
        let mut kept = None;
        for k in order {
            let (laps, pull) = &ladder_laps[k];
            let Some(lap) = laps.first().map(|l| rotate_to(l, join)) else { continue };
            let mut run = if first { lead.clone() } else { Vec::new() };
            run.extend(lap.iter().skip(usize::from(first)).copied());
            let mut from = vec![fin.last().copied().unwrap_or(e)];
            from.extend(run.iter().copied());
            let mut trial = ras.clone();
            let w = trial.walk(&from, s.r, rim, step);
            if w.0 <= bound {
                kept = Some((k, run, trial, w, pull.clone()));
                break;
            }
            if first {
                return refuse(format!("its wall lap reads {:.1}% of D at ({:.2}, {:.2})", load_at_rim(w.0, d, rim) * 100.0, w.1.x, w.1.y));
            }
        }
        let Some((k, run, trial, w, pull)) = kept else { break };
        up(&mut worst, w);
        ras = trial;
        fin.extend(run);
        pulled = pull.iter().copied().max_by(|a, b| a.1.total_cmp(&b.1)).map(|p| (radii[k], p));
        (at, first) = (k, false);
        if let Some(l) = ladder_laps[k].0.first() {
            join = wall::along(&rotate_to(l, j), LAP_HOP).map_or(j, |q| q.0);
        }
    }
    if let Some(p) = passes.last_mut() {
        p.extend(fin);
        p.dedup_by(|a, b| dist(*a, *b) <= 1e-9);
    }
    let mut out = AdaptivePlan { travel: lift::travel(&ras0, &passes, &joins, (s.r, rim, step, bite)), ..AdaptivePlan::default() };
    out.notes.push(format!(
        "adaptive: trochoidal loops - {} front arcs of radius {rho:.2} mm at a {st:.3} mm step along the channel's medial line, each reached by a microlift return; worst planned load {:.1}% of D",
        arcs.len().saturating_sub(1),
        load_at_rim(worst.0, d, rim) * 100.0
    ));
    if let Some((rr, (v, e))) = pulled.filter(|p| p.1.1 > 1e-3) {
        out.notes.push(format!(
            "adaptive: the trochoid's wall laps round the corners at {rr:.2} mm - up to {e:.2} mm corner scallop (worst at ({:.2}, {:.2})) left for the finishing pass",
            v.x, v.y
        ));
    }
    out.rest = ras.standing() as f64 * ras.h * ras.h;
    (out.passes, out.joins) = (passes, joins);
    Ok(out)
}

#[cfg(test)]
#[path = "troch_recovery.rs"]
mod recovery;
