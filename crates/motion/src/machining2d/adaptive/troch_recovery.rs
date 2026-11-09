//! Local-only #47 F0/F1 falsification: existing stock, Hermite blend and
//! emitted microlift APIs; no replacement production geometry or law.
use super::super::front::unit;
use super::super::{BITE_LOAD, GRID_PER_D, SPIRAL_STEPS, first_crossing};
use super::*;
use crate::cl::{MoveKind, PathBuilder};
use crate::entry::Entry3D;
use crate::geometry::Point3;
use crate::machining2d::levels::{Cert, Motion, run_levels};
use crate::quality::{QualitySpec, measure, stock_for};

fn rect(x0: f64, y0: f64, x1: f64, y1: f64) -> crate::geo2d::Loop {
    crate::geo2d::Loop::new(vec![Point2::new(x0, y0), Point2::new(x1, y0), Point2::new(x1, y1), Point2::new(x0, y1)]).unwrap()
}
fn region(x0: f64, y0: f64, x1: f64, y1: f64) -> Region {
    Region::new(vec![rect(x0, y0, x1, y1)]).unwrap()
}
fn spec(center: &Region) -> AdaptiveSpec {
    let (seed, hr) = seed(center, 2.0).unwrap().unwrap();
    AdaptiveSpec {
        r: 5.0,
        load: crate::load::DEFAULT_OPTIMAL_LOAD,
        tol: 0.05,
        climb: true,
        seed,
        start: Point2::new(seed.x - hr, seed.y),
        bore: 5.0 + hr,
        helix_r: hr,
        smooth: 2.5,
    }
}

// The opening block is copied verbatim by the task's preparation script
// from the pinned canonical plan_with, not from a failed experiment.
// It returns the generated walk and its genuine last ring, not a disk.
struct Opening {
    ras: Raster,
    walk: Vec<Point2>,
    prev: Vec<Point2>,
    rho: f64,
    worst: (f64, Point2),
}

fn opening(center: &Region, s: &AdaptiveSpec) -> Result<Opening, String> {
    let refuse = |why: String| Err(why);
    let (sp, c) = spine(center).map_err(|e| format!("{e:?}"))??;
    let rho = sp.points().iter().map(|&p| boundary_dist(center, p)).fold(c, f64::min) - RHO_MARGIN * c;
    let reach_owned = center.offset(s.r).map_err(|e| format!("{e:?}"))?;
    let reach = &reach_owned;
    let d = 2.0 * s.r;
    let mut ras = Raster::from_region(reach, d / GRID_PER_D, s.r).map_err(|e| format!("{e:?}"))?;
    let rim = crate::quality::rim_for(d, ras.h);
    let bound = deg_at_rim(s.load * (1.0 + s.tol), d, rim);
    let _bite = deg_at_rim(BITE_LOAD, d, rim);
    let (step, seg) = (s.r / 10.0, s.r / 8.0);
    let ladder: Vec<f64> = SPIRAL_STEPS.iter().map(|f| d * s.load * f).collect();
    let spine_len = super::super::medial::lengths(sp.points()).last().copied().unwrap_or(0.0);
    if spine_len / ladder[0] > LOOP_CAP as f64 {
        return refuse(format!("would cut over {LOOP_CAP} loops a level along its {spine_len:.0} mm medial line"));
    }
    if s.bore > 0.0 {
        ras.cut(s.seed, s.seed, s.bore);
    }
    let _ras0 = ras.clone();
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
    let Some(&c0) = sp.points().first() else {
        return refuse("its medial line is empty".into());
    };
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
            let (nr, nt) = if rr < ro - 1e-9 {
                ((rr + w).min(ro), 0.0)
            } else {
                (ro, (t + w / (shift + rho - ro)).min(1.0))
            };
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
    Ok(Opening { ras, walk, prev, rho, worst })
}

// A sufficient continuous-envelope certificate only. The 0.012 mm
// contraction pays two 0.005 mm polygon buffers plus two quantizations
// and the posted lattice; it never changes a measuring/engagement law.
// Failure is unknown, not a proof that wall-only contact is unsafe.
const ENVELOPE_ERROR: f64 = 0.012;
fn covered(cleared: &Region, path: &[Point2], radius: f64) -> bool {
    if cleared.is_empty() || path.len() < 2 || path.iter().any(|p| !p.x.is_finite() || !p.y.is_finite()) || path.windows(2).all(|w| dist(w[0], w[1]) <= 1e-12) {
        return false;
    }
    let Ok(envelope) = Region::sweep(&[path.to_vec()], radius + ENVELOPE_ERROR) else {
        return false;
    };
    envelope.difference(cleared).is_ok_and(|missing| missing.is_empty())
}

fn replay(center: &Region, s: &AdaptiveSpec, o: &Opening) -> (Raster, Vec<Vec<Point2>>, crate::cl::Toolpath) {
    let tess = crate::machining2d::pocket_hsm::triangle_about(s.seed, s.helix_r + 0.01).unwrap();
    let cert = Cert::Region(&tess);
    let motion = Motion::new(10.0, Some(2.0), 1000.0, 300.0)
        .with_entry(Entry3D::Helix, s.helix_r)
        .with_top(5.0)
        .with_arc_radius(10.0);
    let mut builder = PathBuilder::new(Point3::new(0.0, 0.0, 10.0));
    run_levels(&mut builder, &[o.walk.clone()], &[0.0], &motion, None, Some(&cert), Some(&Cert::Region(center)));
    let path = builder.finish();
    assert!(path.all_finite() && path.is_chained());
    assert!(path.moves.iter().any(|m| m.arc.is_some() && m.to.z < m.from.z));
    let reach = center.offset(s.r).unwrap();
    let mut ras = Raster::from_region(&reach, 10.0 / GRID_PER_D, s.r).unwrap();
    let mut floor = Vec::new();
    for m in &path.moves {
        if m.kind == MoveKind::Rapid {
            continue;
        }
        for (a, b) in m.segments3(crate::machining2d::PLAN_SAG) {
            let q = Point2::new(b.x, b.y);
            if a.z <= 0.0 && b.z <= 0.0 {
                let p = Point2::new(a.x, a.y);
                ras.cut(p, q, s.r);
                floor.push(vec![p, q]);
            } else if b.z <= 0.0 {
                ras.cut(q, q, s.r);
                floor.push(vec![q]);
            }
        }
    }
    let mut qs = QualitySpec::new(10.0);
    qs.cell = 10.0 / GRID_PER_D;
    qs.break_deg = 5.0;
    qs.wall_below = Some(-0.5);
    let mut dex = stock_for(&reach, 5.0, 0.0, 5.0, &qs).unwrap();
    let q = measure(&path, &mut dex, &qs);
    let (nx, ny) = ras.dims();
    let different = (0..nx * ny).filter(|&i| ras.mat(ras.center(i)) != o.ras.mat(ras.center(i))).count();
    eprintln!(
        "F0 entry/opening: seed={:?} hr={} rho={} moves={} descents={} real_stock_cells={} planner_stock_cells={} mismatched_cells={} max_load={} bound={} opening_peak={:?}",
        s.seed,
        s.helix_r,
        o.rho,
        path.moves.len(),
        q.descents,
        ras.standing(),
        o.ras.standing(),
        different,
        q.max_load(),
        s.load * (1.0 + s.tol),
        o.worst
    );
    // Use the real posted stock even if the idealized planner differs.
    (ras, floor, path)
}

#[test]
fn recovery_f1_stock_conditioned_prefix_and_floor_suffix() {
    let channel = region(5.0, 5.0, 55.0, 17.0);
    let part = region(0.0, 0.0, 60.0, 50.0);
    let band = part.offset(9.0).unwrap().difference(&part.offset(5.0).unwrap()).unwrap();
    for (name, center) in [("channel", channel), ("band14", band)] {
        let s = spec(&center);
        let o = opening(&center, &s).unwrap_or_else(|why| panic!("F0 {name}: real opening prerequisite failed: {why}; no invented precleared band"));
        let (mut ras, mut floors, _entry) = replay(&center, &s, &o);
        let cleared = Region::sweep(&floors, s.r).unwrap();
        let (sp, c) = spine(&center).unwrap().unwrap();
        let mut points = sp.points().to_vec();
        let closed = matches!(sp, Spine::Closed(_));
        if closed {
            points.push(points[0]);
        }
        let lens = super::super::medial::lengths(&points);
        let total = *lens.last().unwrap();
        let practical = 10.0 * s.load * 0.35;
        let n = (total / practical).ceil() as usize;
        let pitch = total / n as f64;
        let count = n + usize::from(!closed);
        assert!(count <= LOOP_CAP);
        eprintln!("F1 {name}: practical_pitch={pitch:.12} full_count={count} closed={closed}; fixed family, no aspect/phase/lift/step pool");
        // One stock-conditioned seed and heading, independently of the
        // full-width front circle. Walk back from its desired start
        // along the medial-start radial chord until BOTH ends of the
        // straight descent have a conservative full-rim certificate.
        // This is a seed construction, not a universal air predicate.
        let cc = super::super::medial::at_len(&points, &lens, pitch);
        let tg = unit(points[0], cc);
        let nm = Point2::new(-tg.y, tg.x);
        let rho = sp.points().iter().map(|&p| boundary_dist(&center, p)).fold(c, f64::min) - 1e-6;
        let b = Point2::new(cc.x - rho * nm.x, cc.y - rho * nm.y);
        let heading = unit(points[0], b);
        let rim = crate::quality::rim_for(10.0, ras.h);
        let bite = deg_at_rim(BITE_LOAD, 10.0, rim);
        let bound = deg_at_rim(s.load * (1.0 + s.tol), 10.0, rim);
        let run = super::super::lift_link::RAMP_RUN;
        let length = dist(points[0], b);
        let subdivisions = (length / ras.h).ceil() as usize;
        let mut chosen = None;
        for k in 0..=subdivisions {
            let v = length * (1.0 - k as f64 / subdivisions as f64);
            let p = Point2::new(points[0].x + v * heading.x, points[0].y + v * heading.y);
            let a = Point2::new(p.x - run * heading.x, p.y - run * heading.y);
            let down = vec![a, p];
            if covered(&cleared, &down, rim) && crate::machining2d::slots::chord_clears(&center, a, p) && ras.peek(&down, rim, s.r / 10.0) <= bite {
                chosen = Some((p, down));
                break;
            }
        }
        let (p, down) = chosen.expect("F1 no certified point AND heading on this fixed seed chord");
        let from = *o.walk.last().unwrap();
        // Route at the lift along the real final opening ring, rather
        // than cut a new disc or take a chord through the entry orbit.
        let j = o
            .prev
            .iter()
            .enumerate()
            .min_by(|(_, a), (_, b)| dist(**a, down[0]).total_cmp(&dist(**b, down[0])))
            .unwrap()
            .0;
        let ret = Return {
            lift: LIFTS[0],
            high: false,
            up: vec![],
            via: o.prev[..=j].to_vec(),
            down,
        };
        let emitted = legs(from, &ret);
        let law = Law {
            ras: &ras,
            center: &center,
            r: s.r,
            orbit: (s.seed, s.helix_r),
            land: Some((rim, s.r / 10.0, bite)),
        };
        let mut bad = None;
        let mut worst = 0.0f64;
        for (i, l) in emitted.iter().enumerate() {
            let reason = law.leg_bad(l);
            let physical = covered(&cleared, &[l.0, l.1], s.r);
            // A zero-XY climb needs a disc certificate rather than an
            // invented direction; it is already the previous floor end.
            let physical = physical || dist(l.0, l.1) <= 1e-12;
            let reading = if l.3 < l.2 { ras.peek(&[l.0, l.1], rim, s.r / 10.0) } else { 0.0 };
            worst = worst.max(reading);
            eprintln!("F1 {name} emitted_leg={i} leg={l:?} physical={physical} reason={reason:?} descent_deg={reading:.6}/{bite:.6}");
            if bad.is_none() && (reason.is_some() || !physical || reading > bite) {
                bad = Some(i);
            }
        }
        eprintln!("F1 prefix/traverse first uncertified leg={bad:?}; no floor mutation before all gates");
        assert!(!crosses_any(&emitted, &[]));
        assert!(worst <= bite);
        let mut suffix = vec![p];
        suffix.extend(wall::blend(p, heading, b, tg));
        let segments = ((std::f64::consts::PI * rho / 0.1).ceil() as usize).max(4);
        suffix.extend((1..=segments).map(|k| {
            let t = -std::f64::consts::FRAC_PI_2 + std::f64::consts::PI * k as f64 / segments as f64;
            Point2::new(cc.x + rho * (t.cos() * tg.x + t.sin() * nm.x), cc.y + rho * (t.cos() * tg.y + t.sin() * nm.y))
        }));
        let snap = |p: Point2| Point2::new(crate::cl::lattice(p.x), crate::cl::lattice(p.y));
        suffix = suffix.into_iter().map(snap).collect();
        // The intended Hermite endpoint derivative equals tg; actual
        // emitted chord turns, crossing and engagement still gate it.
        eprintln!(
            "F1 {name}: landing={p:?} heading={heading:?} join={b:?} derivative={tg:?} suffix_vertices={} pre_return_cells={} whole_descent={worst}",
            suffix.len(),
            ras.standing()
        );
        for (si, w) in suffix.windows(2).enumerate() {
            for (pi, old) in floors.iter().enumerate() {
                for old in old.windows(2) {
                    if super::super::guard::proper(w[0], w[1], old[0], old[1]) {
                        eprintln!(
                            "F1 FAILED_FLOOR_CROSSING suffix_leg={si} new={w:?} preceding_piece={pi} old={old:?}; floor NOT walked; downstream advance/corner/closing NOT RUN"
                        );
                    }
                }
            }
        }
        floors.push(suffix.clone());
        assert!(
            bad.is_none() && first_crossing(&floors).is_none(),
            "F1 {name}: prefix/traverse uncertified={bad:?}, floor_crossing={:?}; stop fixed strategy before floor walk",
            first_crossing(&floors)
        );
        let before = ras.standing();
        let w = ras.walk(&suffix, s.r, rim, s.r / 10.0);
        assert!(w.0 <= bound && ras.standing() < before, "F1 floor engagement/progress {w:?}/{bound}");
        // Subsequent/corner/closure remain mandatory; no initial pass
        // is interpreted as full acceptance of the construction.
        eprintln!("F1 first advance passed; this is not subsequent/corner/closure acceptance");
    }
}

#[path = "troch_recovery_controls.rs"]
mod controls;
