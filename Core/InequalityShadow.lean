/-
  W-CONSTRUCTION-1 act 12 · InequalityShadow.lean — THE VANILLA LEG (zero axioms)
  ===============================================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4 (v4.29.1 pinned),
  decide only, expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES -- the coefficient comparison only: (p^n - p^k) < (p^n - 1) for 1 <= k < n at the listed
  cells (p = 2, n = 2..4; p = 3, n = 2, 3; p = 5, n = 2), decided at no axioms; the term-by-term step to Theta_q(g) <=
  Sum_p W_p(g) against nonnegative test data is the act-12 argument and is not compiled here.
-/

namespace InequalityShadow

/-- (p^n - p^k) < (p^n - 1) at the banked and capped cells p = 2, n = 2, 3, 4; p = 3, n = 2, 3; p = 5, n = 2 -- every k
with 1 <= k < n. -/
theorem quotient_below_weil :
    (2 ^ 2 - 2 ^ 1 < 2 ^ 2 - 1) ∧
    (2 ^ 3 - 2 ^ 1 < 2 ^ 3 - 1) ∧ (2 ^ 3 - 2 ^ 2 < 2 ^ 3 - 1) ∧
    (2 ^ 4 - 2 ^ 1 < 2 ^ 4 - 1) ∧ (2 ^ 4 - 2 ^ 2 < 2 ^ 4 - 1) ∧
    (2 ^ 4 - 2 ^ 3 < 2 ^ 4 - 1) ∧
    (3 ^ 2 - 3 ^ 1 < 3 ^ 2 - 1) ∧
    (3 ^ 3 - 3 ^ 1 < 3 ^ 3 - 1) ∧ (3 ^ 3 - 3 ^ 2 < 3 ^ 3 - 1) ∧
    (5 ^ 2 - 5 ^ 1 < 5 ^ 2 - 1) := by decide

/-- the strictness mechanism at the cells: p^k > 1 for k ≥ 1 (the gap is exactly
    p^k − 1 > 0), instances. -/
theorem strictness_gap :
    (2 ^ 1 - 1 ≥ 1) ∧ (2 ^ 2 - 1 ≥ 1) ∧ (2 ^ 3 - 1 ≥ 1) ∧
    (3 ^ 1 - 1 ≥ 1) ∧ (3 ^ 2 - 1 ≥ 1) ∧ (5 ^ 1 - 1 ≥ 1) := by decide

end InequalityShadow
