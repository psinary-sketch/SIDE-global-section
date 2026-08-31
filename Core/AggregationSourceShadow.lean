/-
  b267 · AggregationSourceShadow.lean — THE VANILLA LEG (zero axioms)
  ===================================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES — and, far more importantly, WHAT IT DOES NOT.

  IT COMPILES NO AGGREGATION. M-2 is owed and stays owed. Nothing below states,
  adopts or realizes a function satisfying SPEC-1/2/3, and nothing below is
  evidence that one exists. IT ALSO COMPILES NO OPERATOR: `E₁`, `S̄_v`, `V_inv`,
  the vector state `ω_u`, and every limit are ABSENT here by the registration's
  clause (K), because a shadow that appeared to carry them would be a lie in Lean.

  What is here is the FINITE-DECIDABLE RESIDUE ONLY, in three parts:

    (1) THE CLOSED FORM AT `k = n`, AS EXACT ARITHMETIC. act 9 §2 displays
        `τ_q·p^(k/2) = (pⁿ − p^k)/(pⁿ − 1)` for `1 ≤ k ≤ n−1`, and supplies `0`
        for `k ≥ n`. The finite residue is that the NUMERATOR vanishes at `k = n`
        — `pⁿ − pⁿ = 0` — so the supplied zero is the expression's OWN value there.
        WITH ITS FOIL: at `k = n+1` the numerator is STRICTLY NEGATIVE, so the
        supplied `0` is NOT the expression's value there but an overriding
        convention. THAT CONTRAST IS THE WHOLE POINT and both halves are decided.

        No division appears below. `pⁿ − 1 > 0` for `p ≥ 2, n ≥ 1`, so the sign
        and the vanishing of the quotient are the numerator's, and the numerator
        is what is decided. The quotient itself is not formed.

    (2) THE EMPTY RANGE AT `n = 1`. `1 ≤ k ≤ n−1` reads `1 ≤ k ≤ 0`, which admits
        no `k`. That is b263's silence as arithmetic, WITH ITS POLARITY CONTROL:
        at `n = 2` the range is non-empty, so it is `n = 1` that is special and
        not the construction.

    (3) THE TWO LEVEL LAWS AT `n = 1`, AS THEIR OWN EQUATIONS. The place-2 law
        `4·d₁ = q(q−2)` at `q = 2` gives `d₁ = 0` — the arrival death, and it is
        the law's own value. The odd law `4·d₁ = (q−1)²` at `q = p` gives
        `4·d₁ = (p−1)²`, nonzero for every odd `p`, exhibited at four odd cells.

        ### AND WHAT PART (3) MUST NOT BE MISREAD AS. ###
        `d₁ > 0` is a statement about the SECTOR's dimension. It is NOT a statement
        that b226's chosen generator `4q·P₁f_{1,1}` is nonzero there — b226 says
        so itself: "d_1 > 0 GIVES E_1 != 0. IT DOES NOT GIVE u_{1,1} != 0", and
        names the general nonvanishing as a result it did not perform. THIS FILE
        DECIDES THE LAW'S ARITHMETIC AND SETTLES NOTHING ABOUT THAT GENERATOR.

  NO numeral here is a premise of any step. Every one is an evaluation.
-/

namespace AggregationSourceShadow

/-! ### (1) THE CLOSED FORM'S NUMERATOR AT `k = n`, AND ITS FOIL ONE STEP ABOVE. -/

/-- At `k = n` the numerator `pⁿ − p^k` vanishes, so the closed form's value at the
    top level is the EXPRESSION'S OWN, not a convention. Instances at
    `(p,n) = (2,1), (2,3), (3,1), (3,2), (5,1), (7,1)`. -/
theorem numerator_vanishes_at_top :
    2 ^ 1 - 2 ^ 1 = 0 ∧ 2 ^ 3 - 2 ^ 3 = 0 ∧ 3 ^ 1 - 3 ^ 1 = 0 ∧
    3 ^ 2 - 3 ^ 2 = 0 ∧ 5 ^ 1 - 5 ^ 1 = 0 ∧ 7 ^ 1 - 7 ^ 1 = 0 := by decide

/-- THE FOIL, AND IT IS THE HALF THAT MAKES (1) SAY SOMETHING. One level ABOVE the
    top, the numerator does not vanish: `p^(n+1) > pⁿ` strictly. So the supplied
    `0 for k ≥ n` is the expression's own value at `k = n` and an OVERRIDING
    CONVENTION for `k > n`. Stated over `ℕ` as the strict inequality, so no
    subtraction truncation is involved. -/
theorem numerator_does_not_vanish_above_top :
    2 ^ 1 < 2 ^ 2 ∧ 2 ^ 3 < 2 ^ 4 ∧ 3 ^ 1 < 3 ^ 2 ∧
    3 ^ 2 < 3 ^ 3 ∧ 5 ^ 1 < 5 ^ 2 ∧ 7 ^ 1 < 7 ^ 2 := by decide

/-- POLARITY CONTROL on (1). The vanishing is not a truncation artefact of `ℕ`
    subtraction: the denominator is genuinely positive at these cells, so the
    quotient's vanishing is the numerator's and not a division by zero. -/
theorem denominator_is_positive :
    0 < 2 ^ 1 - 1 ∧ 0 < 2 ^ 3 - 1 ∧ 0 < 3 ^ 1 - 1 ∧
    0 < 3 ^ 2 - 1 ∧ 0 < 5 ^ 1 - 1 ∧ 0 < 7 ^ 1 - 1 := by decide

/-! ### (2) THE EMPTY RANGE AT `n = 1`. -/

/-- act 9's range `1 ≤ k ≤ n−1` admits no `k` at `n = 1`: it reads `1 ≤ k ≤ 0`. -/
theorem range_is_empty_at_first_level : ¬ (1 ≤ 1 - 1) := by decide

/-- POLARITY CONTROL on (2). From `n ≥ 2` the range IS inhabited, so it is `n = 1`
    that is special and not the construction. Without this line, (2) would be
    consistent with "the range is always empty", which is false. -/
theorem range_is_inhabited_above_one :
    (1 ≤ 2 - 1) ∧ (1 ≤ 3 - 1) ∧ (1 ≤ 8 - 1) := by decide

/-! ### (3) THE TWO LEVEL LAWS AT `n = 1`. ARITHMETIC ONLY — see the header. -/

/-- THE ARRIVAL DEATH, from the place-2 law `4·d₁ = q(q−2)` at `q = 2`:
    the right-hand side is `2·0 = 0`, so `d₁ = 0` at the cell `(2,1)`. -/
theorem place2_law_gives_zero_at_arrival : 2 * (2 - 2) = 0 := by decide

/-- THE ODD LAW at `q = p`, `n = 1`: `4·d₁ = (p−1)²`, exhibited nonzero at four odd
    primes — `p = 3, 5, 7, 11` giving `4·d₁ = 4, 16, 36, 100`, i.e. `d₁ = 1, 4, 9, 25`. -/
theorem odd_law_is_nonzero_at_first_level :
    4 * 1 = (3 - 1) * (3 - 1) ∧ 4 * 4 = (5 - 1) * (5 - 1) ∧
    4 * 9 = (7 - 1) * (7 - 1) ∧ 4 * 25 = (11 - 1) * (11 - 1) := by decide

/-- POLARITY CONTROL on (3), AND IT IS THE ONE THAT MATTERS: the two laws DISAGREE
    at `n = 1`. The odd law's right-hand side is positive where the place-2 law's
    is zero. So `p = 2` is the exceptional place BY THE LAWS' OWN VALUES, and not
    by an exception written beside them. -/
theorem the_two_laws_disagree_at_first_level :
    (2 * (2 - 2) = 0) ∧ (0 < (3 - 1) * (3 - 1)) ∧ (0 < (5 - 1) * (5 - 1)) := by decide

/-- AND THE VALUE THE FERRY CARRIED, CORRECTED AS ARITHMETIC. `d₁(p,1) = ((p−1)/2)²`
    equals `1` ONLY at `p = 3`; it is `4` at `p = 5` and `9` at `p = 7`. The
    NONZERO claim generalizes; the value `1` is the `p = 3` cell. -/
theorem the_value_one_is_the_p_three_cell_only :
    4 * 1 = (3 - 1) * (3 - 1) ∧ ¬ (4 * 1 = (5 - 1) * (5 - 1)) ∧
    ¬ (4 * 1 = (7 - 1) * (7 - 1)) := by decide

end AggregationSourceShadow

#print axioms AggregationSourceShadow.numerator_vanishes_at_top
#print axioms AggregationSourceShadow.numerator_does_not_vanish_above_top
#print axioms AggregationSourceShadow.denominator_is_positive
#print axioms AggregationSourceShadow.range_is_empty_at_first_level
#print axioms AggregationSourceShadow.range_is_inhabited_above_one
#print axioms AggregationSourceShadow.place2_law_gives_zero_at_arrival
#print axioms AggregationSourceShadow.odd_law_is_nonzero_at_first_level
#print axioms AggregationSourceShadow.the_two_laws_disagree_at_first_level
#print axioms AggregationSourceShadow.the_value_one_is_the_p_three_cell_only
