/-
  THE TRACE'S FACTORIZATION, AND WHY THE SIGN NEVER ENTERS
  · TraceFactorizationShadow.lean
  ========================================================

  Ferry 2026-08-28 (b227, the trace). Vanilla Lean 4 (v4.29.1 pinned), no
  imports; the axiom profile is PRINTED, never assumed.

  ### WHAT THIS FILE IS THE SHADOW OF.
  Act 7's TAIL joint says the restricted-product trace is ### **"defined by
  exactly this"** — that the `E₁`-unit's norm-1 ### **forces the local factor to
  1 at every inactive place**. b227 reads that as the vector state
  `ω_u(T) = ⟨Tu,u⟩`, which factorizes as `∏_v ⟨T_v u_v, u_v⟩` and is `1` at each
  inactive place because `T_v = id` and `‖u_v‖ = 1`.

  This file shadows the two finite-decidable parts of that reading:

    (1) ### **THE FACTORIZATION** — inactive places contribute exactly `1`, so
        the product over all places equals the product over the ACTIVE ones;
    (2) ### **THE PHASE-INVARIANCE** — the state is unchanged when the unit is
        multiplied by a unit scalar. ### **THIS IS THE WHOLE REASON b227's LIFT
        WORKS:** b211's derived simplicity makes the rank-2 eigenfunction a
        well-defined RAY, norm-one reduces it to a sign, and ### **the state
        cannot see the sign** — so b214's BENCH-grade sign never enters.

  ### **IT SHADOWS NO OPERATOR, NO SPACE, AND NO NUMBER.** The factors are
  opaque values here. ### **In particular it does NOT model the quotient
  channel's operator**, which b227 found does not act on this object's space at
  all — the Fourier half does not descend to `V_inv` (b10).

  ### THE STAND-IN, DECLARED. Factors are `Int`; the real state's factors are
  complex. ### **The two facts shadowed use only that the factors form a
  commutative monoid under multiplication with a unit `1`, and that `λ·λ̄ = 1`
  for a unit scalar** — both true in `ℂ`. No ordering of `ℂ` is used or implied:
  the positivity terminals below are about the `Int` model only and are marked.

  ### THE POLARITY CONTROLS COME FIRST and are not decoration: without
  `naive_product_differs` the factorization theorem would be true of a model in
  which inactive places happened not to matter, and without
  `zero_factor_kills_positivity` the positivity terminal would be true of a
  model in which nothing could ever fail.
-/

namespace TraceFactorizationShadow

/-- the local factor of the state at a place: the operator's factor where the
    place is ACTIVE, and `1` where it is not. -/
def factor (active : List Nat) (f : Nat → Int) (v : Nat) : Int :=
  if active.contains v then f v else 1

/-- the state, as the product of local factors over the places carried. -/
def stateProd (places active : List Nat) (f : Nat → Int) : Int :=
  places.foldr (fun v acc => factor active f v * acc) 1

/-- the same product with the ACTIVE/INACTIVE distinction ignored — used only as
    a polarity control, never as a definition. -/
def naiveProd (places : List Nat) (f : Nat → Int) : Int :=
  places.foldr (fun v acc => f v * acc) 1

/-- a concrete finite roster of places. -/
def places : List Nat := [2, 3, 5, 7, 11, 13]

/-- a concrete active set — the places where the operator is not the identity. -/
def active : List Nat := [2, 3]

/-- concrete local factors. -/
def fac : Nat → Int := fun v => if v = 2 then 3 else if v = 3 then 5 else 7

/-- ### THE DEFINING PROPERTY, at an inactive place: the factor is `1`. -/
theorem inactive_factor_is_one : factor active fac 5 = 1 := by decide

/-- ### and at an active place it is not forced to `1`. -/
theorem active_factor_is_not_forced : factor active fac 2 = 3 := by decide

/-- (1) ### **THE FACTORIZATION.** The product over all six places equals the
    product over the two active ones — the inactive four contribute `1` each. -/
theorem product_is_over_the_active_set :
    stateProd places active fac = 15 := by decide

/-- ### POLARITY CONTROL — the active/inactive distinction is DOING WORK: the
    naive product, which ignores it, gives a different value. -/
theorem naive_product_differs :
    naiveProd places fac ≠ stateProd places active fac := by decide

/-- the `Int` model's positivity. ### MARKED: this is about the model, not about
    any ordering of `ℂ`. -/
theorem product_positive_here : 0 < stateProd places active fac := by decide

/-- ### POLARITY CONTROL — positivity is not automatic in this model: one zero
    factor at an active place collapses it. -/
theorem zero_factor_kills_positivity :
    ¬ (0 < stateProd places active (fun v => if v = 2 then 0 else 5)) := by decide

/-- the state's dependence on a scalar multiple of the unit: `⟨T(λu),λu⟩`
    carries `λ·λ̄`, which is `1` for a unit scalar. Over `Int` the unit scalars
    are `1` and `-1`. -/
def stateOf (lam : Int) (base : Int) : Int := lam * lam * base

/-- (2) ### **THE PHASE-INVARIANCE — THE REASON THE LIFT WORKS.** Flipping the
    unit's sign does not move the state. ### **So b214's BENCH-grade sign never
    enters the trace, and b211's derived simplicity — which fixes the RAY — is
    all the archimedean leg needs.** -/
theorem state_is_sign_blind (b : Int) : stateOf 1 b = stateOf (-1) b :=
  congrArg (fun s => s * b) (show (1 : Int) * 1 = (-1 : Int) * (-1) by decide)

/-- ### POLARITY CONTROL — the state is NOT invariant under a non-unit scalar,
    so `state_is_sign_blind` is measuring unit scalars and not the encoding. -/
theorem state_sees_non_unit_scalars : stateOf 2 3 ≠ stateOf 1 3 := by decide

end TraceFactorizationShadow

#print axioms TraceFactorizationShadow.inactive_factor_is_one
#print axioms TraceFactorizationShadow.active_factor_is_not_forced
#print axioms TraceFactorizationShadow.product_is_over_the_active_set
#print axioms TraceFactorizationShadow.naive_product_differs
#print axioms TraceFactorizationShadow.product_positive_here
#print axioms TraceFactorizationShadow.zero_factor_kills_positivity
#print axioms TraceFactorizationShadow.state_is_sign_blind
#print axioms TraceFactorizationShadow.state_sees_non_unit_scalars
