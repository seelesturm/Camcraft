//! F2 controls: the actual retained polygon must supplement sampled stock.
use super::*;
#[test]
fn recovery_f2_loaded_rim_and_early_loaded_descent_controls() {
    let reach = region(-20.0, -20.0, 20.0, 20.0);
    let (r, h) = (5.0, 10.0 / GRID_PER_D);
    let rim = crate::quality::rim_for(10.0, h);
    let bite = deg_at_rim(BITE_LOAD, 10.0, rim);
    let mut ras = Raster::from_region(&reach, h, r).unwrap();
    // An actual preceding cutter sweep clears a physical disc, not rim.
    ras.cut(Point2::new(0.0, 0.0), Point2::new(0.0, 0.0), r);
    let loaded = vec![Point2::new(-0.02, 0.0), Point2::new(0.0, 0.0)];
    assert!(ras.capsule_clear(loaded[0], loaded[1], r - GRAZE - h));
    let deg = ras.peek(&loaded, rim, 0.5);
    assert!(deg > bite, "a reduced clear capsule is not measured air");
    // Generate a real prior circular sweep. With orbit radius 1 < r,
    // its overlapping discs fill the centre as well as the annulus.
    let previous: Vec<_> = (0..=360)
        .map(|k| {
            let a = std::f64::consts::TAU * k as f64 / 360.0;
            Point2::new(a.cos(), a.sin())
        })
        .collect();
    let mut clear = Raster::from_region(&reach, h, r).unwrap();
    for w in previous.windows(2) {
        clear.cut(w[0], w[1], r);
    }
    let air = vec![Point2::new(-0.1, 0.0), Point2::new(0.0, 0.0)];
    assert!(clear.peek(&air, rim, 0.5) <= bite);
    let early = vec![Point2::new(0.8, 0.0), Point2::new(1.2, 0.0), Point2::new(0.0, 0.0)];
    let ret = Return {
        lift: LIFTS[0],
        down: early.clone(),
        ..Return::default()
    };
    let emitted = legs(Point2::new(0.0, 0.0), &ret);
    let readings: Vec<_> = emitted.iter().filter(|l| l.3 < l.2).map(|l| clear.peek(&[l.0, l.1], rim, 0.5)).collect();
    assert!(readings.last().is_some_and(|&d| d <= bite));
    assert!(readings.iter().any(|&d| d > bite));
    assert!(clear.peek(&early, rim, 0.5) > bite);
    use crate::quality::Rim::{Open, Stock, Wall};
    assert_eq!(crate::quality::longest_arc([Wall, Wall, Open].into_iter(), false), 0);
    assert_eq!(crate::quality::longest_arc([Wall, Wall, Stock, Open].into_iter(), false), 3);
    let mut walls = Raster::from_region(&reach, h, r).unwrap();
    walls.cut(Point2::new(0.0, 0.0), Point2::new(0.0, 0.0), 40.0);
    assert_eq!(walls.peek(&[Point2::new(16.0, 0.0), Point2::new(16.1, 0.0)], rim, 0.5), 0.0);
    eprintln!("F2 reduced_capsule=true rim_loaded={deg} bite={bite}; early_loaded/emitted={readings:?}; clear positive and wall-only/stock-bearing controls passed");
}
#[test]
fn recovery_f2_subcell_retained_stock_and_unknown_controls() {
    let retained = Region::new(vec![rect(0.0, 0.0, 1.0, 1.0), rect(20.021, 10.0, 20.029, 30.0)]).unwrap();
    let ras = Raster::from_region(&retained, 10.0 / GRID_PER_D, 5.0).unwrap();
    // With origin -5 and h=1/12 the column centres straddle this real
    // 0.008mm strip. Establish that geometric premise independently.
    let feature = region(20.021, 10.0, 20.029, 30.0);
    assert!(feature.area() > 0.0 && retained.contains(Point2::new(20.025, 20.0)));
    let (nx, ny) = ras.dims();
    let represented = (0..nx * ny).filter(|&i| feature.contains(ras.center(i)) && ras.mat(ras.center(i))).count();
    assert_eq!(represented, 0, "distinguishing subcell fixture premise");
    let p = Point2::new(15.0, 20.0);
    let path = vec![p, Point2::new(15.01, 20.0)];
    let radius = crate::quality::rim_for(10.0, ras.h);
    assert!(ras.stock_clear(p, radius));
    let envelope = Region::sweep(&[path.clone()], radius).unwrap();
    let missed = envelope.intersect(&feature).unwrap();
    assert!(!missed.is_empty() && missed.area() > 0.0, "real retained stock intersects the claimed clear envelope");
    // Clearance must be refused by the polygon evidence, not accepted
    // from the zero represented cells. No production law is changed.
    let cleared = region(-10.0, -10.0, 40.0, 40.0).difference(&retained).unwrap();
    assert!(!covered(&cleared, &path, radius));
    assert!(!covered(&Region::empty(), &path, radius));
    assert!(!covered(&cleared, &[], radius));
    assert!(!covered(&cleared, &[p, p], radius));
    assert!(!covered(&cleared, &[p, Point2::new(f64::NAN, 0.0)], radius));
    // A genuine narrow continuous gap/equality is unknown at the
    // envelope error, not clearance. A wider control is certifiable.
    let narrow = region(-5.125, -10.0, 5.125, 10.0);
    let equality = vec![Point2::new(0.0, -0.1), Point2::new(0.0, 0.1)];
    assert!(!covered(&narrow, &equality, 5.125));
    assert!(!covered(&region(-5.124, -10.0, 5.124, 10.0), &equality, 5.125));
    assert!(covered(&region(-5.2, -10.0, 5.2, 10.0), &equality, 5.125));
    eprintln!(
        "F2 retained_sliver_area={} represented_cells={represented} raster_clear=true analytic_intersection_area={}; unknown/empty/nonfinite/degenerate/equality/narrow-gap controls passed",
        feature.area(),
        missed.area()
    );
}
