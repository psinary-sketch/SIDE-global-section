/-
  b262 · JunctionLimitShadow.lean — THE VANILLA LEG (zero axioms)
  ===============================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES — and, far more importantly, WHAT IT DOES NOT.

  IT DOES NOT COMPILE J3. The verdict `(GROWS)` is a statement about
  `J(a) = Σ_{p,k} (2 log p / L) ψ(u/L) · 2 sinh(u/2) / (p^{n_p} − 1)` as `a² → ∞`,
  and it rests on the Prime Number Theorem and on a saddle-point asymptotic. NONE of
  that is here and none of it was forced into `Nat`. The derivation lives at content in
  relay `data/b262_junction_limit.txt`; the ladder that controls it lives in
  `data/b262_run.txt` and `data/b262_repairs.txt`.

  What is here is the FINITE-DECIDABLE RESIDUE ONLY, and it is four things:

    (1) THE PARTITION — b260's counts, and the fact that `T_top` and `T_fixed` are
        disjoint and exhaust the index set.

    (2) THE FIXED-LEVEL FRACTION — `φ(p,k,n) = (p^k − 1)/(p^n − 1)` at fixed `(p,k)`,
        exhibited as EXACT INTEGER arithmetic: the denominators grow while the numerator
        stands still. This is act 9's LEVEL LIMIT, and it is the half of J3 that dies.

    (3) THE SHARP BOUND ON `T_fixed`, WHICH THIS ACT FOUND WHILE REPAIRING A BAD CONTROL:
        for every `k ≤ n−1` and every `p ≥ 2`, `φ < 1/p`. As integers, with no division:
        `p · (p^{n−1} − 1) < p^n − 1`, which reduces to `p > 1`. It is SHARPER than the
        envelope the registration used, and the record carries it.

    (4) THE SCOPE WALL, AS ARITHMETIC — at `a² = 100`, EVERY prime of `S4 = (2,3,5)` has
        `n_p ≥ 2`, while `11` has `n_p = 1`. THE FAMILY THAT DECIDES J3 IS ABSENT FROM
        THE BENCH SET AND PRESENT IN THE FULL ONE. This is the module's real content:
        it is the one thing a reader of b255/b260/b261's tables could not have seen.

  EVERY NUMERAL IS AN EVALUATION of a quantity the run computed, or a bare arithmetic
  fact. NO numeral here is a premise of any step of the derivation.
-/

namespace JunctionLimitShadow

/-! ### (1) THE PARTITION — b260's counts.

`T_top := {(p,k) : k = n_p}`, `T_fixed := {(p,k) : k < n_p}`. Disjoint by construction
(`k = n` and `k < n` cannot both hold) and exhaustive (`k ≤ n` always). b260 counted
43 top-level and 76 fixed-level pairs across its sixteen cells. -/

/-- The counts reconcile: 43 + 76 = 119, b260's own total. -/
theorem partition_counts : (43 + 76 = 119) := by decide

/-- POLARITY CONTROL. The two classes are NOT the same size, and neither is the whole —
    a line that would fail if one had been transcribed from the other. -/
theorem partition_classes_are_distinct :
    ¬ (43 = 76) ∧ (43 < 119) ∧ (76 < 119) := by decide

/-! ### (2) THE FIXED-LEVEL FRACTION — act 9's level limit, as integers.

At FIXED `(p,k) = (2,1)` the numerator is `2^1 − 1 = 1` and stands still, while the
denominator `2^n − 1` grows without bound. That is the whole content of "the per-term
junction dies", stated without division. -/

/-- The denominators grow strictly: `2^n − 1` at `n = 1, 2, 4, 8, 16`. -/
theorem fixed_level_denominators_grow :
    (2 ^ 1 - 1 < 2 ^ 2 - 1) ∧ (2 ^ 2 - 1 < 2 ^ 4 - 1) ∧
    (2 ^ 4 - 1 < 2 ^ 8 - 1) ∧ (2 ^ 8 - 1 < 2 ^ 16 - 1) := by decide

/-- And the numerator at fixed `k = 1` does not move: it is `1` for every `n`.
    So the fraction `1 / (2^n − 1)` is driven to zero by the denominator alone. -/
theorem fixed_level_numerator_stands_still :
    (2 ^ 1 - 1 = 1) ∧ (1 < 2 ^ 8 - 1) ∧ (1 < 2 ^ 16 - 1) := by decide

/-- POLARITY CONTROL. At the TOP level the numerator does NOT stand still — it equals the
    denominator, so the fraction is `1` and the term does not die at all. Without this
    line, (2) would read as "every term dies", which is exactly the false reading J3
    exists to correct. -/
theorem top_level_fraction_is_one :
    (2 ^ 8 - 1 = 2 ^ 8 - 1) ∧ ¬ (2 ^ 8 - 1 < 2 ^ 8 - 1) := by decide

/-! ### (3) THE SHARP BOUND ON `T_fixed` — `φ < 1/p`, found while repairing a bad control.

`φ = (p^k − 1)/(p^n − 1)` is increasing in `k`, so on `k ≤ n−1` its supremum is
`(p^{n−1} − 1)/(p^n − 1)`. That this is `< 1/p` is, cleared of division,
`p · (p^{n−1} − 1) < p^n − 1`, i.e. `p^n − p < p^n − 1`, i.e. `p > 1`. -/

/-- The cleared form at `p = 2, 3, 5` and several `n`. -/
theorem fixed_level_bound_cleared :
    (2 * (2 ^ 11 - 1) < 2 ^ 12 - 1) ∧ (2 * (2 ^ 23 - 1) < 2 ^ 24 - 1) ∧
    (3 * (3 ^ 11 - 1) < 3 ^ 12 - 1) ∧ (5 * (5 ^ 11 - 1) < 5 ^ 12 - 1) := by decide

/-- POLARITY CONTROL, AND IT IS THE ONE THAT MAKES (3) SHARP. The bound does NOT improve
    to `1/(p+1)`: at `p = 2` the same cleared inequality with `p+1` FAILS. So `1/p` is
    the right constant and not a convenient one. -/
theorem fixed_level_bound_is_sharp :
    ¬ (3 * (2 ^ 11 - 1) < 2 ^ 12 - 1) ∧ ¬ (3 * (2 ^ 23 - 1) < 2 ^ 24 - 1) := by decide

/-! ### (4) THE SCOPE WALL — the family the bench cannot see.

`n_p(a) = #{k ≥ 1 : p^k ≤ a²}`. At `a² = 100`: a prime has `n_p = 1` exactly when
`p ≤ 100 < p²`. -/

/-- Every prime of the bench set `S4 = (2,3,5)` has `n_p ≥ 2` at `a² = 100`, because
    `p² ≤ 100` for each of them. So NONE of them is in the `n_p = 1` family. -/
theorem bench_primes_are_not_in_the_top_family :
    (2 ^ 2 ≤ 100) ∧ (3 ^ 2 ≤ 100) ∧ (5 ^ 2 ≤ 100) := by decide

/-- But `11` IS in it: `11 ≤ 100` and `11² > 100`, so `n₁₁(10) = 1` exactly.
    THE FAMILY THE DERIVATION SAYS DOMINATES IS PRESENT IN THE FULL PRIME SET AND
    ABSENT FROM THE BENCH SET, AND THAT IS THIS MODULE'S POINT. -/
theorem eleven_is_in_the_top_family :
    (11 ≤ 100) ∧ ¬ (11 ^ 2 ≤ 100) := by decide

/-- More of the family, so it is not one exceptional prime: `13, 47, 97` all have
    `n_p = 1` at `a² = 100`. The run counted 21 such primes; here are three of them. -/
theorem the_top_family_is_not_a_singleton :
    ((13 ≤ 100) ∧ ¬ (13 ^ 2 ≤ 100)) ∧
    ((47 ≤ 100) ∧ ¬ (47 ^ 2 ≤ 100)) ∧
    ((97 ≤ 100) ∧ ¬ (97 ^ 2 ≤ 100)) := by decide

/-- POLARITY CONTROL. `101` is NOT in the family at `a² = 100` — it is outside the cutoff
    entirely. Without this, "many primes have `n_p = 1`" would be consistent with "every
    prime does", and the cutoff would be doing no work. -/
theorem the_cutoff_still_excludes :
    ¬ (101 ≤ 100) := by decide

end JunctionLimitShadow

#print axioms JunctionLimitShadow.partition_counts
#print axioms JunctionLimitShadow.partition_classes_are_distinct
#print axioms JunctionLimitShadow.fixed_level_denominators_grow
#print axioms JunctionLimitShadow.fixed_level_numerator_stands_still
#print axioms JunctionLimitShadow.top_level_fraction_is_one
#print axioms JunctionLimitShadow.fixed_level_bound_cleared
#print axioms JunctionLimitShadow.fixed_level_bound_is_sharp
#print axioms JunctionLimitShadow.bench_primes_are_not_in_the_top_family
#print axioms JunctionLimitShadow.eleven_is_in_the_top_family
#print axioms JunctionLimitShadow.the_top_family_is_not_a_singleton
#print axioms JunctionLimitShadow.the_cutoff_still_excludes
