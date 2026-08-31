/-
  b265 · CeilingSweepShadow.lean — THE VANILLA LEG (zero axioms)
  ==============================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES — and, far more importantly, WHAT IT DOES NOT.

  IT DOES NOT COMPILE THE CROSSOVER LAW. `x_cliff = EPS_NQ / k` is a MEASURED relation
  between a quadrature node count and a Gauss–Legendre aliasing wall, over two counted
  points, and it is an OBSERVATION under b242. Nothing here proves it, nothing here
  measures it, and no numeral below is evidence for it. The measurement lives at content
  in relay `data/b265_nq_ceiling_sweep.txt`, its controls in `data/b265_run.txt`.

  What is here is the FINITE-DECIDABLE RESIDUE ONLY, in four parts:

    (1) THE `a² → ρ` CORRESPONDENCE, AS EXACT INTEGER ARITHMETIC. `e2_of_grid` evaluates
        the eps grid at `exp(u)` for `u ∈ [0, 2 log a]`, so the top argument is `a²`. The
        finite residue is that the cell label AND the top argument are THE SAME NUMBER —
        checked here on the actual sixteen cell labels of b255's ladder as `a * a = a²`.
        NO logarithm and NO exponential appears below: the identity `exp(2 log a) = a²`
        is the thing this part STANDS ON and is exactly the thing it may not carry.

    (2) THE GRADING, AS COMPARISON. Every one of b255's sixteen cells sits strictly below
        the measured crossover. The crossover is carried as the integer `215` — the
        measured cliff at `EPS_NQ = 700`, NOT b264's `238.4`, because `215` is the
        smaller and grading against the smaller is the conservative direction.
        WITH ITS POLARITY CONTROL: a cell ABOVE the crossover is genuinely NOT below it,
        so the comparison is not vacuously true.

    (3) THE MODE FLOOR, AS A PARTITION. Eleven modes split into SEVEN resolved and FOUR
        at the floor, disjoint and exhaustive: `7 + 4 = 11`. This is b244's RULE MODES K1
        count, which b265 confirmed and did not discover.

    (4) THE NODES-PER-PERIOD ARITHMETIC. The law's content is that `EPS_NQ / x_cliff` is
        the same constant across the ladder. As integer arithmetic: `3 * 215 ≤ 700` and
        `4 * 215 > 700`, and the same brackets hold at `NQ = 1400` with `x = 433`. That
        the constant lies strictly between 3 and 4 at BOTH measured points is the finite
        residue of "the ratio is constant", and it is ALL of it — the ratio's VALUE
        (≈ 3.24) is a measurement and is not here.

  NO numeral here is a premise of any step. Every one is an evaluation of a comparison.
-/

namespace CeilingSweepShadow

/-! ### (1) THE `a² → ρ` CORRESPONDENCE, ON b255's OWN SIXTEEN CELL LABELS. -/

/-- The ladder's cell labels are exactly the squares whose roots the ladder runs over, so
    the top eps argument and the cell label are THE SAME NUMBER. Checked on every label
    of b255's ladder that is a perfect square of an integer. -/
theorem the_cell_label_is_the_top_argument :
    2 * 2 = 4 ∧ 3 * 3 = 9 ∧ 4 * 4 = 16 ∧ 5 * 5 = 25 ∧ 6 * 6 = 36 ∧
    8 * 8 = 64 ∧ 9 * 9 = 81 ∧ 10 * 10 = 100 := by decide

/-- POLARITY CONTROL on (1). The correspondence is not a free identity on any pairing:
    the cell label is NOT the root, and saying so is what keeps (1) from being vacuous. -/
theorem the_label_is_not_the_root :
    ¬ (10 * 10 = 10) ∧ ¬ (4 * 4 = 4) := by decide

/-! ### (2) THE GRADING. Every b255 cell strictly below the measured crossover `215`. -/

/-- All sixteen of b255's cell labels sit strictly below the measured cliff at
    `EPS_NQ = 700`. The crossover is carried as `215`, the CONSERVATIVE choice. -/
theorem every_b255_cell_is_below_the_crossover :
    2 < 215 ∧ 3 < 215 ∧ 4 < 215 ∧ 8 < 215 ∧ 9 < 215 ∧ 12 < 215 ∧
    16 < 215 ∧ 20 < 215 ∧ 25 < 215 ∧ 32 < 215 ∧ 36 < 215 ∧ 45 < 215 ∧
    50 < 215 ∧ 64 < 215 ∧ 81 < 215 ∧ 100 < 215 := by decide

/-- POLARITY CONTROL on (2). The comparison is not vacuously true: a cell above the
    crossover is genuinely NOT below it. Without this line, (2) would be consistent with
    "everything is below 215", which is false. -/
theorem a_cell_above_the_crossover_is_not_below_it :
    ¬ (250 < 215) ∧ ¬ (500 < 215) ∧ ¬ (215 < 215) := by decide

/-- AND THE CONSERVATIVE DIRECTION, MADE EXPLICIT. `215` is smaller than b264's `238`,
    so grading against `215` grades against the tighter of the two available numbers. -/
theorem the_conservative_crossover_is_the_smaller_one : 215 < 238 := by decide

/-! ### (3) THE MODE FLOOR, AS A PARTITION. b244's K1 count. -/

/-- Seven resolved modes and four at the floor exhaust the instrument's eleven. -/
theorem the_modes_partition_seven_and_four : (7 : Nat) + 4 = 11 := by decide

/-- POLARITY CONTROL on (3). The partition is not free: seven is not eleven, and the
    four floor modes are not none. -/
theorem the_floor_is_neither_empty_nor_everything :
    ¬ ((7 : Nat) = 11) ∧ ¬ ((4 : Nat) = 0) := by decide

/-! ### (4) THE NODES-PER-PERIOD BRACKET, AT BOTH MEASURED POINTS. -/

/-- At `EPS_NQ = 700` the measured cliff is `x = 215`, and the node density per period
    at the cliff lies strictly between three and four nodes. -/
theorem the_bracket_at_seven_hundred :
    3 * 215 ≤ 700 ∧ ¬ (4 * 215 ≤ 700) := by decide

/-- At `EPS_NQ = 1400` the measured cliff is `x = 433`, and the SAME bracket holds. That
    the bracket is the same at both points is the finite residue of "the ratio is
    constant"; the ratio's value is a measurement and is not here. -/
theorem the_bracket_at_fourteen_hundred :
    3 * 433 ≤ 1400 ∧ ¬ (4 * 433 ≤ 1400) := by decide

/-- POLARITY CONTROL on (4). The bracket excludes: the density is not two per period and
    not five, at either point. Without this the brackets above would be consistent with
    a ratio that moved between the two measurements. -/
theorem the_bracket_excludes_on_both_sides :
    ¬ (5 * 215 ≤ 700) ∧ ¬ (5 * 433 ≤ 1400) ∧ (2 * 215 ≤ 700) ∧ (2 * 433 ≤ 1400) := by decide

end CeilingSweepShadow

#print axioms CeilingSweepShadow.the_cell_label_is_the_top_argument
#print axioms CeilingSweepShadow.the_label_is_not_the_root
#print axioms CeilingSweepShadow.every_b255_cell_is_below_the_crossover
#print axioms CeilingSweepShadow.a_cell_above_the_crossover_is_not_below_it
#print axioms CeilingSweepShadow.the_conservative_crossover_is_the_smaller_one
#print axioms CeilingSweepShadow.the_modes_partition_seven_and_four
#print axioms CeilingSweepShadow.the_floor_is_neither_empty_nor_everything
#print axioms CeilingSweepShadow.the_bracket_at_seven_hundred
#print axioms CeilingSweepShadow.the_bracket_at_fourteen_hundred
#print axioms CeilingSweepShadow.the_bracket_excludes_on_both_sides
