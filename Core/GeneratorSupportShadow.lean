/-
  b268 · GeneratorSupportShadow.lean — THE VANILLA LEG (zero axioms)
  ==================================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES — and, far more importantly, WHAT IT DOES NOT.

  IT COMPILES NO GENERATOR AND NO PROJECTOR. `P₁`, `S`, `Π`, `f_{i,j}`, `Son(p,n)`,
  `E₁` and `ℤ[ζ_N]` are ABSENT here. The nonvanishing of `4q·P₁f_{1,1}` is DERIVED at
  content in relay `data/b268_generator_nonvanishing.txt` and controlled by exact
  reduction modulo `Φ_N` in `data/b268_run.txt`. NOTHING BELOW IS THAT DERIVATION,
  AND NOTHING BELOW IS EVIDENCE FOR IT.

  IT ALSO COMPILES NO AGGREGATION. M-2 is owed and stays owed.

  What is here is the FINITE-DECIDABLE RESIDUE ONLY, in three parts:

    (1) THE ODD LAW'S VALUES AT THE TABLED PRIMES, as the law's own equation
        `4·d₁ = (q−1)²`. Arithmetic, and already the subject of b267's shadow;
        repeated here only because part (3)'s contrast needs it in the same file.

    (2) THE SUPPORT COUNT AS EXACT ARITHMETIC. The derivation's conclusion is
        `support = N − q` with `N = q²`, i.e. `support = q² − q = q(q−1)`. Decided at
        the eight computed places. WITH THE STEP THAT MAKES IT A NONVANISHING:
        `q(q−1) > 0` for `q ≥ 2`, so the support is inhabited and the vector is not
        the zero vector. THE COUNT IS WHAT IS DECIDED; the identification of that
        count with a support is the DERIVATION's, not this file's.

    (3) THE HINGE, AND IT IS THE ONE PART THAT EARNS ITS PLACE HERE. The odd
        argument turns on `gcd(q+2, q²) = 1`, which holds for odd `q` and FAILS at
        `q = 4` where `gcd(6,16) = 2`. Both are decided. THAT CONTRAST IS WHY p = 2
        is handled separately rather than folded into the odd result, and it is the
        finite residue of the act's one real case split.

  NO numeral here is a premise of any step. Every one is an evaluation.
-/

namespace GeneratorSupportShadow

/-! ### (1) THE ODD LAW AT THE TABLED PRIMES, `4·d₁ = (q−1)²` AT LEVEL 1. -/

/-- `d₁(p,1) = ((p−1)/2)²` at `p = 3, 5, 7, 11`, as the law's own equation. -/
theorem odd_law_values :
    4 * 1 = (3 - 1) * (3 - 1) ∧ 4 * 4 = (5 - 1) * (5 - 1) ∧
    4 * 9 = (7 - 1) * (7 - 1) ∧ 4 * 25 = (11 - 1) * (11 - 1) := by decide

/-- THE PLACE-2 LAW at the arrival depth: `4·d₁ = q(q−2)` at `q = 2` is `0`. -/
theorem place2_law_zero_at_arrival : 2 * (2 - 2) = 0 := by decide

/-! ### (2) THE SUPPORT COUNT, AND ITS INHABITEDNESS. -/

/-- `N − q = q² − q` at the eight computed places `q = 4, 3, 5, 7, 11, 13, 17, 19`. -/
theorem support_count_is_q_squared_minus_q :
    4 * 4 - 4 = 12 ∧ 3 * 3 - 3 = 6 ∧ 5 * 5 - 5 = 20 ∧ 7 * 7 - 7 = 42 ∧
    11 * 11 - 11 = 110 ∧ 13 * 13 - 13 = 156 ∧ 17 * 17 - 17 = 272 ∧
    19 * 19 - 19 = 342 := by decide

/-- AND THE STEP THAT TURNS A COUNT INTO A NONVANISHING: the count is POSITIVE at
    every odd `q ≥ 3`, so the support is inhabited. Decided at the tabled odd `q`. -/
theorem support_is_positive_at_odd_places :
    0 < 3 * 3 - 3 ∧ 0 < 5 * 5 - 5 ∧ 0 < 7 * 7 - 7 ∧ 0 < 11 * 11 - 11 ∧
    0 < 13 * 13 - 13 ∧ 0 < 17 * 17 - 17 ∧ 0 < 19 * 19 - 19 := by decide

/-- POLARITY CONTROL on (2). The count is not positive for free: at `q = 1` it is
    zero. So `q ≥ 2` is doing work, and the positivity is not vacuous. -/
theorem the_count_vanishes_at_q_one : 1 * 1 - 1 = 0 := by decide

/-! ### (3) THE HINGE. `gcd(q+2, q²) = 1` FOR ODD `q`, AND NOT AT `q = 4`. -/

/-- For odd `q` the second congruence collapses because `q+2` is coprime to `q²`.
    Decided at `q = 3, 5, 7, 11, 13`. -/
theorem hinge_holds_at_odd_places :
    Nat.gcd (3 + 2) (3 * 3) = 1 ∧ Nat.gcd (5 + 2) (5 * 5) = 1 ∧
    Nat.gcd (7 + 2) (7 * 7) = 1 ∧ Nat.gcd (11 + 2) (11 * 11) = 1 ∧
    Nat.gcd (13 + 2) (13 * 13) = 1 := by decide

/-- ### THE FOIL, AND IT IS THE WHOLE REASON `p = 2` IS STATED SEPARATELY:
    at `q = 4` the hinge FAILS — `gcd(6, 16) = 2`, not `1`. The odd argument does
    not cover `p = 2`, and this line is why. -/
theorem hinge_fails_at_q_four : Nat.gcd (4 + 2) (4 * 4) = 2 := by decide

/-- POLARITY CONTROL on (3). The hinge's failure at `q = 4` is a genuine `≠ 1`, and
    the odd cases are a genuine `= 1`; neither is vacuous. -/
theorem the_hinge_discriminates :
    ¬ (Nat.gcd (4 + 2) (4 * 4) = 1) ∧ ¬ (Nat.gcd (3 + 2) (3 * 3) = 2) := by decide

/-- AND THE THING THE HINGE'S FAILURE DOES ### NOT ### DO, decided so it cannot be
    misread: `p = 2` at level 2 still lands on `N − q = 12`. The hinge failing
    changes the ROUTE to the count, not the count. -/
theorem place_two_still_lands_on_the_count : 4 * 4 - 4 = 12 := by decide

end GeneratorSupportShadow

#print axioms GeneratorSupportShadow.odd_law_values
#print axioms GeneratorSupportShadow.place2_law_zero_at_arrival
#print axioms GeneratorSupportShadow.support_count_is_q_squared_minus_q
#print axioms GeneratorSupportShadow.support_is_positive_at_odd_places
#print axioms GeneratorSupportShadow.the_count_vanishes_at_q_one
#print axioms GeneratorSupportShadow.hinge_holds_at_odd_places
#print axioms GeneratorSupportShadow.hinge_fails_at_q_four
#print axioms GeneratorSupportShadow.the_hinge_discriminates
#print axioms GeneratorSupportShadow.place_two_still_lands_on_the_count
