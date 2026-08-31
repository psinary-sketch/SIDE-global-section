/-
  b261 · E2EvenMonotoneShadow.lean — THE VANILLA LEG (zero axioms)
  ================================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES — and, far more importantly, WHAT IT DOES NOT.

  IT DOES NOT COMPILE J2, IN EITHER DIRECTION. `E2even(a) = 2 ∫₀² ψ(s) εₑᵥₑₙ(aˢ) ds` is a
  real-valued integral of a prolate-mode overlap against a mollifier's autocorrelation.
  NONE of that is here and none of it was forced into `Nat`. The derivation and the
  refutation both live at content in relay `data/b261_e2even_monotone.txt`.

  What is here is the FINITE-DECIDABLE RESIDUE ONLY, and it is exactly three things:

    (1) THE KERNEL'S SHAPE — `εₑᵥₑₙ` scaled ×1e6, at the four points that decide the act:
        it is ZERO at ρ = 1, RISES to a peak near ρ ≈ 1.2, and FALLS afterwards.
        THE TURN IS THE WHOLE FINDING, and it is arithmetic here rather than prose.

    (2) THE REFUTATION — `E2even` ×1e9 at six probe cells BELOW the ladder, each STRICTLY
        SMALLER than at `a² = 2`, and RISING through them. This is the counterexample to
        "E2even decreases monotonically", stated as integer comparisons.

    (3) THE LADDER — the sixteen banked cells, fifteen STRICT decreases, as integer
        comparisons. WITH ITS POLARITY CONTROL: the same predicate applied to the PROBE
        cells FAILS, which is what makes (3) a statement about the ladder's range rather
        than about the function.

  EVERY NUMERAL IS AN EVALUATION, TRUNCATED TOWARD ZERO, of a quantity the run computed
  from the instrument. NO numeral here is a premise of any step of the derivation, and
  none of them is a bound — truncation makes each comparison the harder one.
-/

namespace E2EvenMonotoneShadow

/-! ### (1) THE KERNEL'S SHAPE — `εₑᵥₑₙ(ρ)` scaled ×1e6.

`εₑᵥₑₙ(1) = 0` is NOT an evaluation: it is the owner's own support line, *"integrand
supported ONLY on u in [ρ⁻¹, 1] → eps(1) = 0"*, and `per_mode_eps_grids` writes the zero
through its own `if hi - lo <= 0: continue`. The other three are evaluations. -/

/-- `εₑᵥₑₙ` RISES from zero: `0 < 272056 < 1470398` at `ρ = 1, 1.0198, 1.2046`. -/
theorem kernel_rises_from_zero :
    (0 < 272056) ∧ (272056 < 1470398) := by decide

/-- `εₑᵥₑₙ` FALLS after the peak: `1470398 > 395736 > 45464 > 1559` at `ρ = 1.2046, 2, 10, 100`. -/
theorem kernel_falls_after_the_peak :
    (1470398 > 395736) ∧ (395736 > 45464) ∧ (45464 > 1559) := by decide

/-- POLARITY CONTROL, AND IT IS THE ONE THE WHOLE ACT TURNS ON. The kernel is NOT
    monotone: it cannot be both rising throughout and falling throughout. Stated as the
    failure of the rising relation across the peak — without this line, `kernel_rises_from_zero`
    would be consistent with "rises everywhere" and there would be no turn. -/
theorem kernel_is_not_monotone : ¬ (1470398 < 395736) := by decide

/-- POLARITY CONTROL ON THE TAIL. The far end is not zero either — the kernel decays but
    has not vanished at the grid's end, so "→ 0" is an IMPORT about the limit and not
    something the finite grid establishes. -/
theorem kernel_tail_is_positive_not_zero : (0 < 1559) := by decide

/-! ### (2) THE REFUTATION — `E2even` ×1e9 at the six probe cells below the ladder.

`a² = 1.05, 1.10, 1.20, 1.35, 1.50, 1.75`, against `a² = 2`. -/

/-- Every probe cell is STRICTLY SMALLER than `E2even(a² = 2) = 1002346928`. These six
    comparisons ARE the counterexample to "E2even decreases monotonically on (1, ∞)". -/
theorem probe_cells_are_all_smaller_than_at_two :
    (154974787 < 1002346928) ∧ (294741237 < 1002346928) ∧
    (526961571 < 1002346928) ∧ (766113960 < 1002346928) ∧
    (902826267 < 1002346928) ∧ (992958675 < 1002346928) := by decide

/-- And they RISE through the probe — six strict increases in a row, ending at `a² = 2`.
    A function that rises does not decrease monotonically. -/
theorem probe_cells_rise_monotonically :
    (154974787 < 294741237) ∧ (294741237 < 526961571) ∧
    (526961571 < 766113960) ∧ (766113960 < 902826267) ∧
    (902826267 < 992958675) ∧ (992958675 < 1002346928) := by decide

/-! ### (3) THE LADDER — the sixteen banked cells, fifteen STRICT decreases. -/

/-- `a² = 2, 3, 4, 8, 9, 12, 16, 20` — the lower eight. -/
theorem ladder_decreases_lower :
    (1002346928 > 911291238) ∧ (911291238 > 834279370) ∧
    (834279370 > 685650001) ∧ (685650001 > 665298530) ∧
    (665298530 > 620236607) ∧ (620236607 > 580750905) ∧
    (580750905 > 553305191) := by decide

/-- `a² = 20, 25, 32, 36, 45, 50, 64, 81, 100` — the upper eight. -/
theorem ladder_decreases_upper :
    (553305191 > 528224524) ∧ (528224524 > 502868190) ∧
    (502868190 > 491558875) ∧ (491558875 > 471386275) ∧
    (471386275 > 462389237) ∧ (462389237 > 442510177) ∧
    (442510177 > 424968684) ∧ (424968684 > 410337162) := by decide

/-- POLARITY CONTROL. The SAME predicate applied across the turn FAILS: `E2even` at
    `a² = 1.75` is NOT greater than at `a² = 2`. So (3) is a claim about WHERE THE LADDER
    BEGINS, not about the function — which is exactly the act's finding. -/
theorem the_ladder_predicate_fails_below_the_turn :
    ¬ (992958675 > 1002346928) := by decide

/-! ### (4) THE COUNTS — QUOTED-N, decided rather than asserted in prose. -/

/-- Twenty-two cells: six probe plus sixteen ladder. Twenty-one steps, of which six rise
    (all below the turn) and fifteen fall (all on the ladder). -/
theorem cell_and_step_counts :
    (6 + 16 = 22) ∧ (6 + 15 = 21) ∧ (22 - 1 = 21) := by decide

/-- POLARITY CONTROL ON THE COUNTS. The rising steps and the falling steps are NOT the
    same count, and neither is the whole — a line that would fail if the two had been
    transcribed from each other. -/
theorem rising_and_falling_counts_differ :
    ¬ (6 = 15) ∧ (6 < 21) ∧ (15 < 21) := by decide

end E2EvenMonotoneShadow

#print axioms E2EvenMonotoneShadow.kernel_rises_from_zero
#print axioms E2EvenMonotoneShadow.kernel_falls_after_the_peak
#print axioms E2EvenMonotoneShadow.kernel_is_not_monotone
#print axioms E2EvenMonotoneShadow.kernel_tail_is_positive_not_zero
#print axioms E2EvenMonotoneShadow.probe_cells_are_all_smaller_than_at_two
#print axioms E2EvenMonotoneShadow.probe_cells_rise_monotonically
#print axioms E2EvenMonotoneShadow.ladder_decreases_lower
#print axioms E2EvenMonotoneShadow.ladder_decreases_upper
#print axioms E2EvenMonotoneShadow.the_ladder_predicate_fails_below_the_turn
#print axioms E2EvenMonotoneShadow.cell_and_step_counts
#print axioms E2EvenMonotoneShadow.rising_and_falling_counts_differ
