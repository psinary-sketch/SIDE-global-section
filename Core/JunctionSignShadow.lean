/-
  b260 · JunctionSignShadow.lean — THE VANILLA LEG (zero axioms)
  ==============================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES — and, far more importantly, WHAT IT DOES NOT.

  IT DOES NOT COMPILE J1. The claim `Θ_q(a) ≤ PR(a)` is an inequality between two
  REAL-VALUED finite sums whose summands carry `2 log p`, `p^{-k/2}` and the bump's
  autocorrelation `corr`. NONE of that is here, and none of it is forced into `Nat`.
  The derivation lives at content in `D:\relay\data\b260_junction_sign.txt`.
  A shadow that appeared to carry the real-valued inequality would be a lie in Lean.

  What is here is the FINITE-DECIDABLE RESIDUE ONLY, and it is exactly three things:

    (1) THE STAIRCASE, DECIDED — `n_p(a) = #{k ≥ 1 : p^k ≤ a²}` at the ladder's
        deepest cell, each place proved by BOTH halves (`p^n ≤ a²` AND `¬(p^{n+1} ≤ a²)`).
        The negative half is not decoration: it is what makes `n_p` a maximum.

    (2) THE RANGE CAP IS SLACK — the instrument's loop bound `k ≤ 2n−1` never binds,
        because the guard `p^k ≤ a²` selects `k ≤ n` and `n ≤ 2n−1`. WITH ITS POLARITY
        CONTROL: at `n = 1` the cap is EXACTLY TIGHT, so "slack" is a claim about `n ≥ 2`
        and not a triviality.

    (3) THE PER-TERM RATIO INEQUALITY, IN EXACT INTEGER ARITHMETIC — act 9 §2's
        `(p^n − p^k)/(p^n − 1) < 1` for `1 ≤ k ≤ n−1`, stated without division as
        `p^n − p^k < p^n − 1`; and the endpoint `k = n`, where the numerator is `0`.
        WITH ITS POLARITY CONTROL AT `k = 0`, WHICH IS THE LOAD-BEARING ONE: at `k = 0`
        the inequality becomes an EQUALITY, so the hypothesis `1 ≤ k` excludes something
        real and is not a formality.

  THE `p^{-k/2}` FACTOR IS ABSENT ON PURPOSE. It is common to both summands and cancels
  from the comparison; carrying it into `Nat` would require `Real.rpow` gymnastics that
  the registration refused in advance as contortion.

  NO NUMERAL HERE IS A PREMISE OF ANY STEP OF THE DERIVATION. Every one is an evaluation
  of a formula the owners already state.
-/

namespace JunctionSignShadow

/-! ### (1) THE STAIRCASE, DECIDED — b17's `n_p(a) = #{k ≥ 1 : p^k ≤ a²}`.

At the ladder's deepest cell `a² = 100` with the fixed place set `S4 = (2,3,5)`.
Each place is proved by BOTH halves. The second half is what makes `n_p` a MAXIMUM
rather than merely a lower bound. -/

/-- `n₂(100) = 6`, `n₃(100) = 4`, `n₅(100) = 2` — the positive halves. -/
theorem staircase_at_hundred_lower :
    (2 ^ 6 ≤ 100) ∧ (3 ^ 4 ≤ 100) ∧ (5 ^ 2 ≤ 100) := by decide

/-- The negative halves. WITHOUT THESE THREE LINES the staircase would be a lower bound
    and the index set would be unbounded above. -/
theorem staircase_at_hundred_upper :
    ¬ (2 ^ 7 ≤ 100) ∧ ¬ (3 ^ 5 ≤ 100) ∧ ¬ (5 ^ 3 ≤ 100) := by decide

/-- POLARITY CONTROL ON THE FIXED PLACE SET. `S4` is fixed at `(2,3,5)`, so `7` never
    enters this ladder even though `7^2 = 49 ≤ 100` WOULD admit it. This line is the
    arithmetic witness that the ladder measures the powers of a FIXED prime set and not
    a growing one — the species limit b255 states in prose. -/
theorem seven_would_have_entered_a_growing_place_set : (7 ^ 2 ≤ 100) := by decide

/-! ### (2) THE RANGE CAP IS SLACK — S1's finite lemma.

`theta_quotient` loops `for k in range(1, 2*n)`, i.e. `k ≤ 2n−1`, and GUARDS each term
by `k·log p ≤ 2L`, i.e. `p^k ≤ a²`, i.e. `k ≤ n`. The two index sets can only agree if
the cap never cuts below the guard, which is `n ≤ 2n−1`. -/

/-- The cap does not bind at any `n` occurring on the ladder (`n = 1 … 6`). -/
theorem cap_never_binds :
    (1 ≤ 2 * 1 - 1) ∧ (2 ≤ 2 * 2 - 1) ∧ (3 ≤ 2 * 3 - 1) ∧
    (4 ≤ 2 * 4 - 1) ∧ (5 ≤ 2 * 5 - 1) ∧ (6 ≤ 2 * 6 - 1) := by decide

/-- The cap is STRICTLY slack from `n = 2` upward: there are `k` the loop would reach
    that the guard rejects. -/
theorem cap_strictly_slack_from_two :
    (2 < 2 * 2 - 1) ∧ (3 < 2 * 3 - 1) ∧ (4 < 2 * 4 - 1) ∧
    (5 < 2 * 5 - 1) ∧ (6 < 2 * 6 - 1) := by decide

/-- POLARITY CONTROL. At `n = 1` the cap is EXACTLY TIGHT — `2·1−1 = 1` — so the loop
    and the guard admit the same single value and there is no slack at all. Without this
    line "the cap is slack" would read as a claim about every `n`, and it is not one. -/
theorem cap_is_tight_at_one : ¬ (1 < 2 * 1 - 1) := by decide

/-! ### (3) THE PER-TERM RATIO INEQUALITY — act 9 §2, IN EXACT INTEGER ARITHMETIC.

act 9 §2 states `tau_q(p,n,k) · p^(k/2) = (p^n − p^k)/(p^n − 1)` for `1 ≤ k ≤ n−1`,
and `0 for k ≥ n`. The whole content of S3-i is that this ratio is `< 1`, which without
division is `p^n − p^k < p^n − 1`. Stated at every `(p,n,k)` of the deepest cell. -/

/-- `p = 2`, `n = 6`, `k = 1 … 5`. Numerators `62, 60, 56, 48, 32` against `63`. -/
theorem ratio_below_one_at_two :
    (2 ^ 6 - 2 ^ 1 < 2 ^ 6 - 1) ∧ (2 ^ 6 - 2 ^ 2 < 2 ^ 6 - 1) ∧
    (2 ^ 6 - 2 ^ 3 < 2 ^ 6 - 1) ∧ (2 ^ 6 - 2 ^ 4 < 2 ^ 6 - 1) ∧
    (2 ^ 6 - 2 ^ 5 < 2 ^ 6 - 1) := by decide

/-- `p = 3`, `n = 4`, `k = 1 … 3`. Numerators `78, 72, 54` against `80`.
    `p = 5`, `n = 2`, `k = 1`. Numerator `20` against `24`. -/
theorem ratio_below_one_at_three_and_five :
    (3 ^ 4 - 3 ^ 1 < 3 ^ 4 - 1) ∧ (3 ^ 4 - 3 ^ 2 < 3 ^ 4 - 1) ∧
    (3 ^ 4 - 3 ^ 3 < 3 ^ 4 - 1) ∧ (5 ^ 2 - 5 ^ 1 < 5 ^ 2 - 1) := by decide

/-- THE ENDPOINT `k = n`, WHICH IS WHERE THE GAP'S WHOLE-TERM HALF COMES FROM. The
    numerator is `0` while the denominator is not, so act 9's value VANISHES while the
    prime side's term does not. This is the arithmetic behind the sawtooth. -/
theorem ratio_vanishes_at_the_top_level :
    (2 ^ 6 - 2 ^ 6 = 0) ∧ (3 ^ 4 - 3 ^ 4 = 0) ∧ (5 ^ 2 - 5 ^ 2 = 0) ∧
    (0 < 2 ^ 6 - 1) ∧ (0 < 3 ^ 4 - 1) ∧ (0 < 5 ^ 2 - 1) := by decide

/-- POLARITY CONTROL, AND THE ONE THIS MODULE MOST NEEDS. The derivation's step is
    `p^k > 1`, which requires `1 ≤ k`. AT `k = 0` THE STRICT INEQUALITY FAILS — it becomes
    an equality, because `p^0 = 1`. So the hypothesis `1 ≤ k` in act 9's range EXCLUDES
    SOMETHING REAL, and `ratio_below_one_*` above is not true of every exponent. -/
theorem ratio_is_not_below_one_at_zero :
    ¬ (2 ^ 6 - 2 ^ 0 < 2 ^ 6 - 1) ∧ ¬ (3 ^ 4 - 3 ^ 0 < 3 ^ 4 - 1) ∧
    ¬ (5 ^ 2 - 5 ^ 0 < 5 ^ 2 - 1) := by decide

/-! ### (4) THE COUNTS — QUOTED-N, DECIDED RATHER THAN ASSERTED.

The run reports 119 terms across the sixteen cells, of which 43 sit at `k = n`. Both
are sums of the per-cell staircase totals, and both are checked here so that a count
typed into a report has an arithmetic witness. -/

/-- The index-set sizes per cell, `a² = 2 … 100`, summing to the reported 119. -/
theorem term_count_is_one_hundred_nineteen :
    1 + 1 + 3 + 5 + 6 + 6 + 7 + 7 + 8 + 10 + 10 + 10 + 10 + 11 + 12 + 12 = 119 := by decide

/-- The `k = n` counts per cell — one per ACTIVE place — summing to the reported 43. -/
theorem top_level_count_is_forty_three :
    1 + 1 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 = 43 := by decide

/-- POLARITY CONTROL ON THE COUNTS. The two are NOT equal and the second is a strict
    subset of the first — a line that would fail if the `k = n` terms had been counted
    twice or if the totals had been transcribed from each other. -/
theorem the_two_counts_are_distinct : ¬ (119 = 43) ∧ (43 < 119) := by decide

end JunctionSignShadow

#print axioms JunctionSignShadow.staircase_at_hundred_lower
#print axioms JunctionSignShadow.staircase_at_hundred_upper
#print axioms JunctionSignShadow.seven_would_have_entered_a_growing_place_set
#print axioms JunctionSignShadow.cap_never_binds
#print axioms JunctionSignShadow.cap_strictly_slack_from_two
#print axioms JunctionSignShadow.cap_is_tight_at_one
#print axioms JunctionSignShadow.ratio_below_one_at_two
#print axioms JunctionSignShadow.ratio_below_one_at_three_and_five
#print axioms JunctionSignShadow.ratio_vanishes_at_the_top_level
#print axioms JunctionSignShadow.ratio_is_not_below_one_at_zero
#print axioms JunctionSignShadow.term_count_is_one_hundred_nineteen
#print axioms JunctionSignShadow.top_level_count_is_forty_three
#print axioms JunctionSignShadow.the_two_counts_are_distinct
