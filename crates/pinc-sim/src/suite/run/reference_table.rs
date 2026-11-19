//! The reference numbers a run is read against: the leader's and the reference model's terms on the matrix seeds,
//! pooled over both variants of each scenario, as recorded in the written spec ("Numbers to meet or beat").
//!
//! Values are in the units of the spec's table, not of [`crate::suite::grade::Terms`]; [`display`] converts a term to
//! those units. [`Comparability`] says whether a ratio against these numbers is like for like.
//!
//! Invariants: a row is `(leader, reference)` per column in [`COLUMNS`] order, `None` where the spec has a dash.

use crate::suite::grade::Terms;

/// The 14 terms of the table, in column order.
pub const COLUMNS: [&str; 14] = [
    "L1", "L2", "L3", "L5", "T1", "C1", "C2", "B1", "B3", "B4", "B5", "R1", "R2", "R3",
];

/// The unit of each column, in column order.
pub const UNITS: [&str; 14] = [
    "ms",
    "ms",
    "ms",
    "s",
    "Mbit/s",
    "B",
    "s",
    "x",
    "kB/node-h",
    "/node-h",
    "x",
    "ns/B",
    "KiB",
    "B",
];

/// How a term compares with the reference harness's (the written spec, section 7.3 point 3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Comparability {
    /// Same definition and physics: latencies, delivery shares, L5, B3 and B4 counts. The throughput terms and C2
    /// are classed here too: they are durations over the same physics, though the spec's list does not name them.
    Identical,
    /// Real byte sizes replace modelled ones: B1, B2, B5, C1, R3.
    RealSizes,
    /// A changed cost model: R1 and R2.
    CostModel,
}

impl Comparability {
    /// The label printed in the tables.
    pub const fn label(self) -> &'static str {
        match self {
            Self::Identical => "identical",
            Self::RealSizes => "real sizes",
            Self::CostModel => "changed cost model",
        }
    }
}

/// The comparability of `term`.
pub fn comparability(term: &str) -> Comparability {
    match term {
        "B1" | "B2" | "B5" | "C1" | "R3" => Comparability::RealSizes,
        "R1" | "R2" => Comparability::CostModel,
        _ => Comparability::Identical,
    }
}

type Pair = Option<(f64, f64)>;

const fn p(a: f64, b: f64) -> Pair {
    Some((a, b))
}

/// One scenario's row: `(leader, reference)` per column.
pub type Row = [Pair; 14];

/// The table, one row per scenario.
pub const NUMBERS: [(&str, Row); 12] = [
    (
        "S1",
        [
            p(0.2, 0.4),
            p(104.0, 262.0),
            p(7.7, 578.0),
            None,
            p(7685.0, 870.0),
            None,
            None,
            p(1.048, 1.162),
            p(126.0, 10682.0),
            p(1187.0, 97052.0),
            p(0.010, 0.015),
            p(4.9, 29.0),
            p(72.0, 613.0),
            p(108.8, 32.0),
        ],
    ),
    (
        "S2",
        [
            p(88.0, 167.0),
            p(494.0, 10333.0),
            p(943.0, 1439.0),
            p(2.2, 123.5),
            p(8.30, 2.42),
            p(2235.0, 152_156.0),
            p(0.37, 4.24),
            p(1.676, 8.841),
            p(79.0, 16598.0),
            p(615.0, 106_932.0),
            p(0.194, 1.177),
            p(110.0, 2316.0),
            p(58.0, 448.0),
            p(110.3, 32.0),
        ],
    ),
    (
        "S3",
        [
            p(121.0, 233.0),
            p(10250.0, 32187.0),
            p(11137.0, 15817.0),
            p(21.5, 42.6),
            p(10.45, 3.51),
            p(5105.0, 92082.0),
            p(5.22, 8.33),
            p(1.449, 4.159),
            p(216.0, 13638.0),
            p(1807.0, 87763.0),
            p(0.076, 0.467),
            p(53.0, 719.0),
            p(71.0, 1102.0),
            p(108.2, 32.0),
        ],
    ),
    (
        "S4",
        [
            p(97.0, 136.0),
            p(66244.0, 21724.0),
            p(917.0, 1812.0),
            p(16.8, 131.9),
            p(4.68, 1.87),
            p(25589.0, 346_353.0),
            p(18.3, 82.7),
            p(2.550, 12.655),
            p(277.0, 20038.0),
            p(899.0, 95205.0),
            p(0.740, 3.084),
            p(98.0, 1413.0),
            p(61.0, 383.0),
            p(108.6, 32.0),
        ],
    ),
    (
        "S5",
        [
            p(85.0, 150.0),
            p(265.0, 521.0),
            p(784.0, 1773.0),
            None,
            p(5.80, 1.97),
            None,
            None,
            p(1.889, 6.565),
            p(86.0, 19535.0),
            p(757.0, 112_657.0),
            p(0.443, 1.364),
            p(65.0, 1138.0),
            p(64.0, 643.0),
            p(109.0, 32.0),
        ],
    ),
    (
        "S6",
        [
            p(1170.0, 1816.0),
            p(18929.0, 81058.0),
            p(55334.0, 53327.0),
            p(5.9, 227.7),
            p(0.017, 0.008),
            None,
            None,
            p(8.226, 71.988),
            p(612.0, 6172.0),
            p(6730.0, 35759.0),
            p(0.949, 7.153),
            p(948.0, 9940.0),
            p(51.0, 138.0),
            p(107.6, 32.0),
        ],
    ),
    (
        "S10",
        [
            p(76.0, 122.0),
            p(269.0, 3190.0),
            p(969.0, 1016.0),
            p(1.3, 126.3),
            p(2.23, 2.74),
            p(6730.0, 41184.0),
            p(0.73, 1.40),
            p(2.224, 13.885),
            p(42.0, 15720.0),
            p(330.0, 74819.0),
            p(0.472, 3.270),
            p(140.0, 1520.0),
            p(48.0, 242.0),
            p(108.4, 32.0),
        ],
    ),
    (
        "S11",
        [
            p(63.0, 123.0),
            p(546.0, 908.0),
            p(467.0, 579.0),
            p(1.2, 38.9),
            p(19.32, 9.62),
            p(2854.0, 20453.0),
            p(0.17, 2.62),
            p(1.101, 1.288),
            p(47.0, 7345.0),
            p(349.0, 54300.0),
            p(0.005, 0.019),
            p(11.0, 47.0),
            p(91.0, 3273.0),
            p(103.6, 32.0),
        ],
    ),
    (
        "S12",
        [
            p(71.0, 97.0),
            p(24858.0, 21958.0),
            p(641.0, 1023.0),
            p(0.22, 1.47),
            p(0.94, 0.10),
            None,
            None,
            p(1.614, 8.071),
            p(160.0, 9368.0),
            p(1069.0, 51924.0),
            p(0.103, 0.496),
            p(74.0, 1105.0),
            p(51.0, 237.0),
            p(108.0, 32.0),
        ],
    ),
    (
        "S13",
        [
            p(86.0, 137.0),
            p(35529.0, 32075.0),
            p(584.0, 10965.0),
            p(103.5, 257.8),
            p(6.38, 4.03),
            p(5760.0, 100_429.0),
            p(0.35, 4.35),
            p(4.115, 28.861),
            p(94.0, 11359.0),
            p(609.0, 79045.0),
            p(0.620, 3.297),
            p(2087.0, 11798.0),
            p(52.0, 137.0),
            p(108.6, 32.0),
        ],
    ),
    (
        "S14",
        [
            p(454.0, 994.0),
            p(1471.0, 6325.0),
            p(564.0, 690.0),
            None,
            None,
            None,
            None,
            p(2.185, 23.306),
            p(49.0, 10023.0),
            p(388.0, 73483.0),
            p(0.206, 2.216),
            p(220.0, 3979.0),
            p(120.0, 613.0),
            p(106.4, 32.0),
        ],
    ),
    (
        "S15",
        [
            p(75.0, 102.0),
            p(189.0, 338.0),
            p(667.0, 1115.0),
            p(2.1, 105.0),
            p(3.43, 1.98),
            p(3036.0, 95442.0),
            p(0.30, 1.84),
            p(2.274, 13.900),
            p(53.0, 12279.0),
            p(433.0, 85719.0),
            p(0.375, 1.610),
            p(169.0, 2676.0),
            p(63.0, 375.0),
            p(105.9, 32.0),
        ],
    ),
];

/// The terms the spec gives outside the table: `(scenario, term, leader, reference)`, in the unit of [`display`]
/// (T2 and T3 as Mbit/s and ms).
pub const EXTRA: [(&str, &str, f64, f64); 8] = [
    ("S3", "C3", 0.0, 0.0336),
    ("S3", "C4", 0.0, 0.0556),
    ("S6", "C4", 0.0, 0.676),
    ("S11", "T2", 18.24, 11.22),
    ("S11", "T3", 874.5, 682.1),
    ("S11", "T4", 0.0, 0.524),
    ("S12", "T2", 0.94, 0.10),
    ("S14", "B2", 39.5, 128.7),
];

/// The value of `term` in the unit of the spec's table.
pub fn display(term: &str, v: f64) -> f64 {
    match term {
        "L1" | "L2" | "L3" | "L4" | "T3" => v / 1e6,
        "L5" | "C2" => v / 1e9,
        "T1" | "T2" => 8000.0 / v,
        "B3" => v / 1000.0,
        "R2" => v / 1024.0,
        _ => v,
    }
}

/// The row of `scenario`.
pub fn row(scenario: &str) -> Option<&'static Row> {
    NUMBERS.iter().find(|(s, _)| *s == scenario).map(|(_, r)| r)
}

/// The terms of `t` that the table has columns for, with their displayed value.
pub fn displayed(t: &Terms) -> Vec<(&'static str, Option<f64>)> {
    COLUMNS.iter().map(|c| (*c, t.get(c).map(|v| display(c, v)))).collect()
}
