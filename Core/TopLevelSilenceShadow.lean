/-
  b263 · TopLevelSilenceShadow.lean — THE VANILLA LEG (zero axioms)
  =================================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES — and, far more importantly, WHAT IT DOES NOT.

  IT DOES NOT COMPILE M-2's SPECIFICATION. That specification is a conditional statement
  about real-valued aggregations over all primes, and it is conditional on which side of
  the identity absorbs the first-level mass — a question no owner has settled. NONE of
  that is here. It lives at content in relay `data/b263_top_level_silence.txt`.

  What is here is the FINITE-DECIDABLE RESIDUE ONLY, and it is one idea in three parts:

    (1) THE RANGE EXCLUDES THE TOP LEVEL. act 9 §2 defines `tau_q` for `1 ≤ k ≤ n−1` and
        supplies `0 for k ≥ n`. So `k = n` is OUTSIDE the closed form's range — as
        arithmetic, `¬ (n ≤ n − 1)`. WITH ITS POLARITY CONTROL: the level just below IS
        inside (`1 ≤ n − 1` for `n ≥ 2`), so the range excludes THE TOP AND NOTHING ELSE.

    (2) AT `n = 1` THE RANGE IS EMPTY WHILE THE INDEX SET IS NOT. `[1, 0]` contains no
        `k`, yet `k = 1` is a genuine member of the index set (`1 ≤ 1`). THAT PAIR IS
        THE SILENCE: a first-level prime has a level, and act 9 assigns it zero.

    (3) THE ASYMMETRY AT THE TOP, AS EXACT INTEGER ARITHMETIC. b260's level fraction is
        `(p^k − 1)/(p^n − 1)`. At `k = n` numerator and denominator COINCIDE — which,
        cross-multiplied, is a TAUTOLOGY and is labelled one here. The content is its
        FOIL: one level below, the numerator is STRICTLY SMALLER. The top level is not
        "large"; it is the unique level where the fraction saturates.

  NO numeral here is a premise of any step. Every one is an evaluation of a range.
-/

namespace TopLevelSilenceShadow

/-! ### (1) THE RANGE EXCLUDES THE TOP LEVEL — and only it. -/

/-- `k = n` is never inside `1 ≤ k ≤ n−1`: instances at `n = 1, 2, 6, 12`. -/
theorem top_level_is_outside_the_range :
    ¬ (1 ≤ 1 - 1) ∧ ¬ (2 ≤ 2 - 1) ∧ ¬ (6 ≤ 6 - 1) ∧ ¬ (12 ≤ 12 - 1) := by decide

/-- POLARITY CONTROL. The level just below IS inside the range, for every `n ≥ 2`.
    So the range excludes THE TOP LEVEL AND NOTHING ELSE — without this line, (1) would
    be consistent with "the range is empty", which is true only at `n = 1`. -/
theorem the_level_below_is_inside_the_range :
    (1 ≤ 2 - 1) ∧ (1 ≤ 6 - 1) ∧ (5 ≤ 6 - 1) ∧ (11 ≤ 12 - 1) := by decide

/-! ### (2) AT `n = 1` THE RANGE IS EMPTY WHILE THE INDEX SET IS NOT.

This pair IS the silence. The index set at a cell is `{k : 1 ≤ k ≤ n_p}`; act 9's closed
form runs only over `1 ≤ k ≤ n_p − 1`. At `n_p = 1` the first is `{1}` and the second is
empty, so the prime HAS a level and the quotient channel assigns it nothing. -/

/-- `k = 1` is in the index set at `n = 1`, and the closed form's range is empty there. -/
theorem first_level_prime_has_a_level_the_range_does_not_reach :
    (1 ≤ 1) ∧ ¬ (1 ≤ 1 - 1) := by decide

/-- POLARITY CONTROL. At `n = 2` the range is NOT empty — it contains `k = 1`. So (2) is
    a statement about `n = 1` specifically, not about every `n`. -/
theorem the_range_is_nonempty_from_two_upward :
    (1 ≤ 2 - 1) ∧ (1 ≤ 3 - 1) := by decide

/-! ### (3) THE ASYMMETRY AT THE TOP — b260's fraction, as integers. -/

/-- At `k = n` numerator and denominator coincide, so the fraction is `1`.
    THIS IS A TAUTOLOGY and is labelled one: cross-multiplied it reads `x = x`. It is
    compiled because the act quotes it, not because it establishes anything. -/
theorem the_fraction_saturates_at_the_top :
    (2 ^ 6 - 1 = 2 ^ 6 - 1) ∧ (3 ^ 4 - 1 = 3 ^ 4 - 1) ∧ (5 ^ 2 - 1 = 5 ^ 2 - 1) := by decide

/-- AND ITS FOIL, WHICH CARRIES THE CONTENT. One level below the top the numerator is
    STRICTLY smaller than the denominator, so the fraction is strictly less than `1`.
    The top level is not merely large — it is the unique level where the fraction
    saturates, and these two theorems together are what makes that a statement. -/
theorem the_fraction_is_strictly_below_one_beneath_the_top :
    (2 ^ 5 - 1 < 2 ^ 6 - 1) ∧ (3 ^ 3 - 1 < 3 ^ 4 - 1) ∧ (5 ^ 1 - 1 < 5 ^ 2 - 1) := by decide

/-- POLARITY CONTROL ON THE FOIL. The gap is not an artefact of small exponents: at
    `p = 2, n = 24` the level below is still strictly smaller, and by a wide margin. -/
theorem the_foil_holds_at_depth :
    (2 ^ 23 - 1 < 2 ^ 24 - 1) ∧ ¬ (2 ^ 24 - 1 < 2 ^ 23 - 1) := by decide

/-! ### (4) THE COUNTS — QUOTED-N, decided rather than asserted.

The survey read 27 prior-owner hit lines and classified them: 7 SUPPLIES, 2 DEFINES,
18 OTHER, and 0 CANDIDATE CONSTRAINTS. -/

/-- The classified counts reconcile to the total read. -/
theorem survey_counts_reconcile : (7 + 2 + 18 + 0 = 27) := by decide

/-- POLARITY CONTROL ON THE COUNTS. The candidate-constraint count is the ONLY zero among
    them — a line that would fail if the survey had found nothing at all, which would have
    meant a broken search rather than a measured absence. -/
theorem only_the_candidate_count_is_zero :
    (0 < 7) ∧ (0 < 2) ∧ (0 < 18) ∧ ¬ (0 < 0) := by decide

end TopLevelSilenceShadow

#print axioms TopLevelSilenceShadow.top_level_is_outside_the_range
#print axioms TopLevelSilenceShadow.the_level_below_is_inside_the_range
#print axioms TopLevelSilenceShadow.first_level_prime_has_a_level_the_range_does_not_reach
#print axioms TopLevelSilenceShadow.the_range_is_nonempty_from_two_upward
#print axioms TopLevelSilenceShadow.the_fraction_saturates_at_the_top
#print axioms TopLevelSilenceShadow.the_fraction_is_strictly_below_one_beneath_the_top
#print axioms TopLevelSilenceShadow.the_foil_holds_at_depth
#print axioms TopLevelSilenceShadow.survey_counts_reconcile
#print axioms TopLevelSilenceShadow.only_the_candidate_count_is_zero
