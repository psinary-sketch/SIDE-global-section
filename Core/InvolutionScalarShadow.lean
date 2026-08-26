/-
  THE INVOLUTION SCALAR'S ARITHMETIC CORE · InvolutionScalarShadow.lean
  =====================================================================

  Ferry 2026-08-26 (b204, the sign across the family). Vanilla Lean 4 (v4.29.1
  pinned), no imports; expected profile per terminal: "does not depend on any
  axioms" — AND THE PROFILE IS PRINTED, NEVER ASSUMED.

  ### WHAT THIS FILE IS A SHADOW OF, AND WHAT IT IS NOT.
  The step this act needed is: a commuting involution acting on a ONE-DIMENSIONAL
  eigenspace acts on it by a scalar `c` with `c² = 1`, hence by `+1` or `−1`.
  · The MODULE half of that step — that the action is by a scalar at all — needs a
    vector-space structure and is NOT decidable; it is not built here, and the
    record's nearest held piece is `LocalLimit.eigenvector_of_commute` (classical
    profile), which carries eigenvectors along a commuting operator.
  · ### WHAT IS BUILT HERE IS ONLY THE ARITHMETIC CORE: from `c * c = 1`, in ℤ,
    conclude `c = 1 ∨ c = −1`. ### A SHADOW OF THE SCALAR STEP IS NOT THE SCALAR
    STEP, and this header says so rather than leaving a reader to infer it.

  ### AND WHAT IT DECIDES NOTHING ABOUT: which of the two values `c` takes at any
  particular eigenvalue. That is M22, it is a fact about the object, and no
  arithmetic here touches it.

  Bank: relay `data/b204_sign_across_family.txt`.
-/

namespace InvolutionScalarShadow

/-! ### THE POLARITY CONTROL, FIRST.

  A dichotomy theorem proved without a witness that FAILS its hypothesis is a
  theorem nobody has tested. ### So the failing cases are decided before the
  dichotomy is stated. -/

/-- witnesses that the hypothesis `c * c = 1` is not vacuous: both values satisfy it. -/
theorem both_signs_satisfy : (1 : Int) * 1 = 1 ∧ (-1 : Int) * (-1) = 1 := by decide

/-- ### THE NEGATIVE CONTROL: integers whose square is not `1` — so the hypothesis
    genuinely selects, and the dichotomy below is not true of everything. -/
theorem others_fail : (0 : Int) * 0 ≠ 1 ∧ (2 : Int) * 2 ≠ 1 ∧ (-2 : Int) * (-2) ≠ 1 := by
  decide

/-- ### AND THE TWO VALUES ARE DISTINCT — without this the dichotomy would be
    consistent with there being only one sector. -/
theorem signs_distinct : (1 : Int) ≠ -1 := by decide

/-! ### THE DICHOTOMY, THROUGH A NATURAL-NUMBER CORE.

  ### A FIRST DRAFT ROUTED THIS THROUGH `omega` AND PRINTED `[sorryAx]` ON THE MAIN
  ### TERMINAL: `omega` cannot see a quadratic. The print caught it (Rule 5), and the
  ### repair was a RESTRUCTURE — the bound `4 ≤ (k+2)(k+2)` comes from `Nat.mul_le_mul`
  ### instead, and no tactic is asked for what it cannot do. -/

/-- the natural-number core: `m * m = 1` forces `m = 1`. The `k+2` case is closed by
    `2*2 ≤ (k+2)*(k+2)`, which contradicts `= 1`. -/
theorem nat_sq_one : (m : Nat) → m * m = 1 → m = 1
  | 0,     h => absurd h (by decide)
  | 1,     _ => rfl
  | k + 2, h =>
    absurd (h ▸ Nat.mul_le_mul (Nat.le_add_left 2 k) (Nat.le_add_left 2 k)) (by decide)

/-- ### THE ARITHMETIC CORE: in `ℤ`, `c * c = 1` forces `c = 1` or `c = −1`.
    ### This is the shadow of “a commuting involution on a one-dimensional eigenspace
    acts by `±1`” — ### its arithmetic half only, and the header says which half. -/
theorem int_sq_one : (c : Int) → c * c = 1 → c = 1 ∨ c = -1
  | Int.ofNat n, h => by
      have hn : n = 1 := nat_sq_one n (Int.ofNat.inj h)
      rw [hn]; exact Or.inl rfl
  | Int.negSucc n, h => by
      have h0 : n = 0 := Nat.succ.inj (nat_sq_one (n + 1) (Int.ofNat.inj h))
      rw [h0]; exact Or.inr rfl

/-- and the converse, so the characterization is two-sided and no reader has to
    assume it. -/
theorem int_sq_one_of : (c : Int) → c = 1 ∨ c = -1 → c * c = 1
  | _, Or.inl h => by rw [h]; decide
  | _, Or.inr h => by rw [h]; decide

end InvolutionScalarShadow

#print axioms InvolutionScalarShadow.both_signs_satisfy
#print axioms InvolutionScalarShadow.others_fail
#print axioms InvolutionScalarShadow.signs_distinct
#print axioms InvolutionScalarShadow.nat_sq_one
#print axioms InvolutionScalarShadow.int_sq_one
#print axioms InvolutionScalarShadow.int_sq_one_of
