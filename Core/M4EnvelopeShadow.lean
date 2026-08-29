/-
  b250 · M4EnvelopeShadow.lean — THE VANILLA LEG (zero axioms)
  ============================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES — and, far more importantly, WHAT IT DOES NOT.

  IT DOES NOT COMPILE THE THEOREM. The M-4 derivation of b250 rests on Plancherel,
  the identity theorem, Schmidt/Eckart–Young and Mercer, and lives at content in
  `D:\relay\data\b250_m4_derivation.txt`. NONE of that is here. THE ANALYTIC STEPS ARE
  NOT FORCED INTO VANILLA `Nat`, and a shadow that appeared to carry them would be a
  lie in Lean. What is here is the FINITE-DECIDABLE residue only:

    (1) FACTORIAL DOMINATES GEOMETRIC — the mechanism behind S2's decay, as the finite
        statement that `c · m! ≤ (m+1)!` once `m + 1 ≥ c`, at an integer `c = 7 > 2π`.
    (2) THE ENVELOPE'S ARITHMETIC AT THE CUT — S4's four evaluated rows as rational
        inequalities on scaled integers.
    (3) THE MINIMAX INEQUALITY'S FINITE INSTANCE — `μ_N ≤ bound(N)` at banked N.
    (4) THE RANGE CONDITION'S TEETH — `T(14) < 1` (available at K1's cut N = 6) AND
        `T(10) > 1` (NOT available at N = 4). The second is the POLARITY CONTROL: it is
        what makes the first mean something.

  Every numeral below is an EVALUATION of a formula derived in the bank, scaled to an
  integer. NO numeral here is a premise of any step of the derivation.
-/

namespace M4EnvelopeShadow

/-- `Nat.factorial` IS NOT IN VANILLA LEAN 4 CORE — it is Mathlib's, and the residence tree
    carries no Mathlib. That is the SAME finding the bank's import list reports from the other
    direction, and it arrived here as a compile error rather than as an assumption. Defined
    locally, by structural recursion, so the leg stays vanilla. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-! ### (1) FACTORIAL DOMINATES GEOMETRIC — the mechanism behind S2's decay.

`c^m / m!` is eventually decreasing because the ratio of consecutive terms is `c/(m+1)`.
At `c = 2π < 7`, the turn happens once `m + 1 ≥ 7`. Stated at an INTEGER `c = 7`, which
DOMINATES `2π`, so the finite claim is the harder one. -/

/-- the ratio turns at `m = 6`: `7 · m! ≤ (m+1)!` for every `m ≥ 6`, instances. -/
theorem factorial_dominates_geometric :
    (7 * fact 6 ≤ fact 7) ∧
    (7 * fact 7 ≤ fact 8) ∧
    (7 * fact 8 ≤ fact 9) ∧
    (7 * fact 9 ≤ fact 10) ∧
    (7 * fact 10 ≤ fact 11) ∧
    (7 * fact 11 ≤ fact 12) := by decide

/-- POLARITY CONTROL. It does NOT turn earlier: at `m = 5` the geometric still wins.
    Without this line the theorem above would be consistent with "always true", and the
    `m ≥ 6` in the bank would be decoration. -/
theorem factorial_does_not_dominate_before :
    ¬ (7 * fact 5 ≤ fact 6) := by decide

/-! ### (2) THE ENVELOPE'S ARITHMETIC AT THE CUT — S4's evaluated rows.

`Σ_{n>N} t(n) ≤ (2 − S_N)/(1 − β_N)`. The four rows of the bank's table, as scaled
integers: the ZERO-IMPORT sharp envelope against the measured tail. Scalings are per
row and stated in each conjunct's magnitude. -/

/-- N = 6 (K1's cut): tail `1.11558894e−14` ≤ envelope `1.15757629e−14`, ×1e22.
    N = 8: `9.91242848e−23` ≤ `9.91250843e−23`, ×1e31.
    N = 10: `1.4601387e−31` ≤ `1.46013869e−31` + the evaluation's own error, ×1e40.
    N = 11: `3.18448512e−36` ≤ `3.1837636e−36` + the evaluation's own error, ×1e45. -/
theorem envelope_holds_at_cuts :
    (111558894 ≤ 115757629) ∧
    (991242848 ≤ 991250843) ∧
    (146013870 ≤ 146013869 + 8) ∧
    (318448512 ≤ 318376360 + 72152) := by decide

/-- POLARITY CONTROL, AND IT IS THE ONE THIS ACT MOST NEEDS. At the two deepest cuts the
    envelope does NOT dominate the measured tail on its own — it needs the evaluation's
    own error term, `7.2152e−40`, which the bank reports rather than hides. These two
    lines are the arithmetic proof that the error term is LOAD-BEARING and was not added
    for comfort. -/
theorem deep_cuts_need_the_evaluation_error :
    ¬ (146013870 ≤ 146013869) ∧
    ¬ (318448512 ≤ 318376360) := by decide

/-! ### (3) THE MINIMAX INEQUALITY'S FINITE INSTANCE — `μ_N ≤ bound(N)`.

S2 gives `μ_N ≤ T(N)²` on ZERO specific imports. The instances are enormously slack,
and the slack is shown rather than trimmed. Scaled ×1e9 after taking a common exponent
per row; each conjunct compares `μ_N` against `T(N)` at the row's own scale. -/

/-- N = 14: `μ = 3.85119078e−16` ≤ `T = 3.6271779e−2`, so ×1e18 the bound is ~1e16 times
    larger; compared here at ×1e18 with the bound truncated DOWNWARD to 36271779000000.
    N = 20: `μ = 1.134386458e−28` ≤ `T = 6.5705942e−8`, at ×1e30 with the bound truncated
    DOWNWARD. Truncating the BOUND downward makes each claim strictly harder. -/
theorem minimax_instances :
    (385 ≤ 36271779000000) ∧
    (113 ≤ 65705942000000000000000) := by decide

/-! ### (4) THE RANGE CONDITION'S TEETH.

S4 needs `β_N < 1`. On the zero-import bound `T` this FAILS at small `N`, because
`c^m/m!` peaks near `m = c = 2π`. The first available cut is `N = 6`, and K1's cut is
`N = 6`. Scaled ×1e7. -/

/-- `T(14) = 0.0362718 < 1` — the zero-import envelope IS available at `N = 6`. -/
theorem range_condition_holds_at_six : (362718 < 10000000) := by decide

/-- POLARITY CONTROL. `T(10) = 24.354796 > 1` — the zero-import envelope is NOT available
    at `N = 4`. THE RANGE CONDITION IS NOT COSMETIC, and this line is the proof that the
    `N ≥ 6` in the bank excludes something real. -/
theorem range_condition_fails_at_four : ¬ (243547960 < 10000000) := by decide

end M4EnvelopeShadow
