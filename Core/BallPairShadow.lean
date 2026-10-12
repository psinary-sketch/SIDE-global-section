/-
  W-CONSTRUCTION-1 act 15 · BallPairShadow.lean — THE VANILLA LEG (zero axioms)
  =============================================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4 (v4.29.1 pinned),
  decide only, expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES -- the arithmetic of the ball-scale relation at the banked cells (2,1), (2,2), (2,3),
  (3,1), (3,2), (5,1), (5,2): p^{2n} - 2*p^n + 1 = (p^n - 1)^2, and the values 2*p^n - 1. The dimension reading (dim
  Son_p = p^{2n} - dim(E + B), with E and B of dimension p^n meeting in rank one) is b10's L-A in relay's bank and is
  not compiled here.
-/

namespace BallPairShadow

/-- the inclusion–exclusion identity p^{2n} − 2·p^n + 1 = (p^n − 1)² at the banked
    cells (2,1), (2,2), (2,3), (3,1), (3,2), (5,1), (5,2). -/
theorem sonin_dim_inclusion_exclusion :
    (2 ^ 2 - 2 * 2 ^ 1 + 1 = (2 ^ 1 - 1) ^ 2) ∧
    (2 ^ 4 - 2 * 2 ^ 2 + 1 = (2 ^ 2 - 1) ^ 2) ∧
    (2 ^ 6 - 2 * 2 ^ 3 + 1 = (2 ^ 3 - 1) ^ 2) ∧
    (3 ^ 2 - 2 * 3 ^ 1 + 1 = (3 ^ 1 - 1) ^ 2) ∧
    (3 ^ 4 - 2 * 3 ^ 2 + 1 = (3 ^ 2 - 1) ^ 2) ∧
    (5 ^ 2 - 2 * 5 ^ 1 + 1 = (5 ^ 1 - 1) ^ 2) ∧
    (5 ^ 4 - 2 * 5 ^ 2 + 1 = (5 ^ 2 - 1) ^ 2) := by decide

/-- the values 2*p^n - 1 at the cells (2,1), (2,2), (2,3), (3,1), (3,2), (5,1) -- the constraint count that the reading
dim E = dim B = p^n with a rank-one intersection gives; those dimensions are not compiled here. -/
theorem constraint_span_dims :
    (2 * 2 ^ 1 - 1 = 3) ∧ (2 * 2 ^ 2 - 1 = 7) ∧ (2 * 2 ^ 3 - 1 = 15) ∧
    (2 * 3 ^ 1 - 1 = 5) ∧ (2 * 3 ^ 2 - 1 = 17) ∧ (2 * 5 ^ 1 - 1 = 9) := by decide

end BallPairShadow
