/-
  b264 · ArchimedeanTwinShadow.lean — THE VANILLA LEG (zero axioms)
  ================================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES — and, far more importantly, WHAT IT DOES NOT.

  IT DOES NOT COMPILE `eps_even`'s DECAY. The registration's clause (G) fixes the list
  of what a shadow here MAY NOT CARRY, and it is quoted rather than paraphrased:
  "PLANCHEREL, CAUCHY-SCHWARZ, RIEMANN-LEBESGUE, FOURIER INVERSION, MERCER, THE OPERATOR,
  `eps` ITSELF, OR ANY LIMIT." None of that is here. NO limit appears in this file. The
  derivation lives at content in relay `data/b264_eps_even_decay.txt`, and the controls
  in `data/b264_run.txt`.

  What is here is the FINITE-DECIDABLE RESIDUE ONLY, in five parts:

    (1) THE EXPONENT BOOKKEEPING OF (R1), COUNTED IN HALVES so that it is integer
        arithmetic. The owner's prefactor supplies one half; the change of variables
        `du = dv/rho` supplies two more; the total is three. That is the whole of
        "THREE HALVES", and it is arithmetic, not analysis.

    (2) THE MASK PARTITION. Eleven qeps modes split into six even-indexed and five
        odd-indexed, disjoint and exhaustive. This is an INDEX fact and carries no `rho`.

    (3) THE SIGN LAW `(-1)^n > 0 IFF n EVEN` over the eleven indices.

        ### AND THE THING THIS PART MUST NOT BE MISREAD AS. ###
        This is ARITHMETIC ABOUT `(-1)^n`. It is NOT a certification that the instrument
        realizes pin P1's sign law. The run measured that separately (F6), and measured
        it only where it can be measured: at `EPS_NQ = 700` the eigensolver resolves
        SEVEN of the eleven modes, and modes 7..10 sit at `sqrt(machine epsilon)`, fail
        to decay, and MOVE when `NQ` moves. Their signs are noise. F6 is read on the
        seven resolved modes, where it did not fire. THIS FILE PROVES THE ARITHMETIC AND
        SETTLES NOTHING ABOUT THE INSTRUMENT.

    (4) THE EMPTY OVERLAP AT `rho = 1`. The owner's integration range is `[1/rho, 1]`,
        which at `rho = 1` is a point: `eps(1) = 0` for a reason that is a RANGE and not
        a size. As arithmetic, `¬ (1 ≤ 1 - 1)`. WITH ITS POLARITY CONTROL: from `rho ≥ 2`
        the range is non-empty, so it is the endpoint that is special and nothing else.

    (5) THE CEILING, AS NODES PER PERIOD — and it is the ceiling the run MEASURED, which
        is not the one the act was sent to measure. `A_n(x)` integrates `cos(2 pi t x)`
        over `t in [0,1]`, carrying `x` periods, on the owner's FIXED `EPS_NQ` grid. So
        the node density is `EPS_NQ / x` per period, and it crosses three nodes per
        period between `x = 233` and `x = 234`. The run's measured failure at `x ~ 238`
        is CONSISTENT with that line and is not derived from it.

  NO numeral here is a premise of any step. Every one is an evaluation of a range.
-/

namespace ArchimedeanTwinShadow

/-! ### (1) THE EXPONENT BOOKKEEPING OF (R1), IN HALVES. -/

/-- (R1)'s exponent, counted in HALVES: the owner's `rho^{-1/2}` prefactor is ONE half,
    the change of variables `du = dv/rho` is TWO more, and the total is THREE. -/
theorem exponent_bookkeeping_in_halves : (1 : Nat) + 2 = 3 := by decide

/-- POLARITY CONTROL on (1). The count is not free: three halves is not two, and not four.
    Without this line the statement above would be consistent with any bookkeeping at all. -/
theorem the_halves_do_not_come_out_otherwise :
    ¬ ((1 : Nat) + 2 = 2) ∧ ¬ ((1 : Nat) + 2 = 4) := by decide

/-! ### (2) THE MASK PARTITION — an INDEX fact, carrying no `rho`. -/

/-- The six even-indexed qeps modes are even and the five odd-indexed ones are odd. -/
theorem the_masks_are_what_their_names_say :
    (0 % 2 = 0) ∧ (2 % 2 = 0) ∧ (4 % 2 = 0) ∧ (6 % 2 = 0) ∧ (8 % 2 = 0) ∧ (10 % 2 = 0) ∧
    (1 % 2 = 1) ∧ (3 % 2 = 1) ∧ (5 % 2 = 1) ∧ (7 % 2 = 1) ∧ (9 % 2 = 1) := by decide

/-- The two masks are disjoint and exhaust the eleven modes: `6 + 5 = 11`. -/
theorem the_masks_partition_the_eleven : (6 : Nat) + 5 = 11 := by decide

/-! ### (3) THE SIGN LAW OVER THE ELEVEN INDICES.
     ARITHMETIC ONLY. See the header: this settles nothing about the instrument. -/

/-- `(-1)^n` is positive exactly at the even indices, across all eleven. -/
theorem the_sign_law_over_the_eleven_indices :
    ((-1 : Int) ^ 0 > 0) ∧ ((-1 : Int) ^ 1 < 0) ∧ ((-1 : Int) ^ 2 > 0) ∧
    ((-1 : Int) ^ 3 < 0) ∧ ((-1 : Int) ^ 4 > 0) ∧ ((-1 : Int) ^ 5 < 0) ∧
    ((-1 : Int) ^ 6 > 0) ∧ ((-1 : Int) ^ 7 < 0) ∧ ((-1 : Int) ^ 8 > 0) ∧
    ((-1 : Int) ^ 9 < 0) ∧ ((-1 : Int) ^ 10 > 0) := by decide

/-- POLARITY CONTROL on (3). The law is not vacuously "all positive": the odd indices are
    genuinely negative, which is what makes the EVEN mask's tail sign say anything. -/
theorem the_sign_law_is_not_all_one_way :
    ¬ ((-1 : Int) ^ 1 > 0) ∧ ¬ ((-1 : Int) ^ 3 > 0) ∧ ¬ ((-1 : Int) ^ 5 > 0) := by decide

/-! ### (4) THE EMPTY OVERLAP AT `rho = 1`. -/

/-- At `rho = 1` the overlap range `[1/rho, 1]` is a single point — as integer arithmetic,
    the range `1 ≤ k ≤ 1 - 1` admits no `k`. This is the RANGE reason `eps(1) = 0`. -/
theorem the_overlap_is_empty_at_one : ¬ (1 ≤ 1 - 1) := by decide

/-- POLARITY CONTROL on (4). From `rho ≥ 2` the range IS non-empty, so it is the endpoint
    that is special and not the construction. -/
theorem the_overlap_is_nonempty_above_one :
    (1 ≤ 2 - 1) ∧ (1 ≤ 5 - 1) ∧ (1 ≤ 100 - 1) := by decide

/-! ### (5) THE MEASURED CEILING, AS NODES PER PERIOD. -/

/-- `EPS_NQ = 700` nodes across `x` periods crosses THREE nodes per period between
    `x = 233` and `x = 234`. Stated as exact integer arithmetic on node counts. -/
theorem three_nodes_per_period_crosses_between_233_and_234 :
    (3 * 233 ≤ 700) ∧ ¬ (3 * 234 ≤ 700) := by decide

/-- The run's MEASURED failure at `x ~ 238` lies past that line. This is a CONSISTENCY
    statement between a measurement and an arithmetic threshold; the measurement is not
    derived from the threshold, and the threshold does not predict the measurement. -/
theorem the_measured_ceiling_lies_past_the_three_node_line :
    ¬ (3 * 238 ≤ 700) := by decide

/-- AND THE CONTRAST THAT MAKES (5) THE POINT OF THIS PART. The owner's OUTER node count
    `EPS_NG = 400` under the act's registered law of eight nodes per period is exhausted
    only at `rho = 50` — yet the run measured `NG = 400` still tracking at `rho = 100`.
    So the `NG` line is the LOOSER of the two, and it is not what breaks first. -/
theorem the_outer_node_line_sits_where_it_sits :
    (8 * 50 = 400) ∧ ¬ (8 * 51 ≤ 400) := by decide

/-- POLARITY CONTROL on (5). The two ceilings are genuinely different numbers and the
    inner one binds first: `233 < 400`, and the inner line is crossed while the outer
    node budget is still nominally intact. -/
theorem the_inner_ceiling_binds_before_the_outer :
    (233 < 400) ∧ (3 * 233 ≤ 700) := by decide

end ArchimedeanTwinShadow

#print axioms ArchimedeanTwinShadow.exponent_bookkeeping_in_halves
#print axioms ArchimedeanTwinShadow.the_halves_do_not_come_out_otherwise
#print axioms ArchimedeanTwinShadow.the_masks_are_what_their_names_say
#print axioms ArchimedeanTwinShadow.the_masks_partition_the_eleven
#print axioms ArchimedeanTwinShadow.the_sign_law_over_the_eleven_indices
#print axioms ArchimedeanTwinShadow.the_sign_law_is_not_all_one_way
#print axioms ArchimedeanTwinShadow.the_overlap_is_empty_at_one
#print axioms ArchimedeanTwinShadow.the_overlap_is_nonempty_above_one
#print axioms ArchimedeanTwinShadow.three_nodes_per_period_crosses_between_233_and_234
#print axioms ArchimedeanTwinShadow.the_measured_ceiling_lies_past_the_three_node_line
#print axioms ArchimedeanTwinShadow.the_outer_node_line_sits_where_it_sits
#print axioms ArchimedeanTwinShadow.the_inner_ceiling_binds_before_the_outer
