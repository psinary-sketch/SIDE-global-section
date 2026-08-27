/-
  THE SIGN TRANSFER · SignTransferShadow.lean
  ============================================

  Ferry 2026-08-27 (b211, the alternation derived). Vanilla Lean 4 (v4.29.1
  pinned), no imports; the axiom profile is PRINTED, never assumed.

  ### WHAT THIS FILE IS THE SHADOW OF.
  b211 derives, at content, the identity

      α(μ_k) · β′(μ_k) = ∫₁^∞ ψ_{μ_k}² dx

  whose right-hand side is an integral of a square and is therefore STRICTLY
  POSITIVE. From that the derivation takes one step:

    ### if every termwise product is POSITIVE and one factor ALTERNATES,
    ### then the other factor ALTERNATES.

  ### THAT STEP, AND ONLY THAT STEP, IS WHAT IS SHADOWED HERE.

  ### WHAT IT IS NOT — and the fence matters more here than usual, because the
  ### act it serves reaches theorem grade and a reader could mistake the shadow
  ### for the reach.
  · It is NOT the derivation. The identity is derived at content in
    `relay/data/b211_alternation_derived.txt`; nothing here knows what α, β, ψ
    or an eigenvalue is.
  · It is NOT the analytic half. That β′ alternates in sign at consecutive
    SIMPLE ZEROS of a real-analytic function is an analytic fact resting on
    premise (ii), it is ### NOT FINITE-DECIDABLE, and it is deliberately NOT in
    Core. ### THE SHADOW IS THE ALGEBRAIC TRANSFER ONLY.
  · It does NOT establish that the corpus's β′ alternates. That is derived
    elsewhere and lives at its own grade.
  · ### IT IS NOT A DUPLICATE OF `AlternationShadow.lean` (b207). That file
    shows a GLOBAL sign error cannot turn "both values occur" into "one value
    occurs". ### THIS ONE SHOWS THE TRANSFER FROM ONE FACTOR TO THE OTHER.
    Neither implies the other and the derivation uses both.

  Bank: relay `data/b211_alternation_derived.txt`.
-/

namespace SignTransferShadow

/-- a value is a sign when it is `1` or `-1`. -/
def IsSign (x : Int) : Prop := x = 1 ∨ x = -1

/-- a sequence alternates when each term is the negation of the last. -/
def Alternates (s : Nat → Int) : Prop := ∀ i, s (i + 1) = -s i

/-! ### THE POLARITY CONTROLS, FIRST.

  ### A TRANSFER THEOREM PROVED WITHOUT A WITNESS WHERE THE TRANSFER FAILS IS A
  ### THEOREM NOBODY HAS TESTED. The failing case is decided before the theorems
  ### are stated, and the failing case here is the one that matters: ### THE
  ### HYPOTHESIS THAT THE PRODUCT IS POSITIVE IS LOAD-BEARING, and dropping it
  ### breaks the conclusion rather than merely weakening it. -/

/-- the positive-product case: signs agree. -/
theorem control_pos : (0 : Int) < 1 * 1 := by decide

/-- the negative-product case: signs differ, and the product is NOT positive —
    so `0 < x * y` genuinely selects. -/
theorem control_neg : ¬ ((0 : Int) < 1 * (-1)) := by decide

/-- and the two sign values are distinct, without which "alternates" would be
    satisfiable by a constant sequence. -/
theorem signs_distinct : (1 : Int) ≠ -1 := by decide

/-! ### THE BRIDGE: A POSITIVE PRODUCT OF TWO SIGNS FORCES THEM EQUAL.

  ### THIS IS WHERE THE CONTENT SITS. Everything after it is rewriting. -/

theorem eq_of_mul_pos {x y : Int} (hx : IsSign x) (hy : IsSign y)
    (h : 0 < x * y) : x = y := by
  match hx, hy with
  | Or.inl ex, Or.inl ey => rw [ex, ey]
  | Or.inr ex, Or.inr ey => rw [ex, ey]
  | Or.inl ex, Or.inr ey =>
      rw [ex, ey] at h
      exact absurd h (by decide)
  | Or.inr ex, Or.inl ey =>
      rw [ex, ey] at h
      exact absurd h (by decide)

/-! ### THE TRANSFER. -/

/-- ### IF EVERY TERMWISE PRODUCT IS POSITIVE AND `b` ALTERNATES, THEN `a`
    ALTERNATES. ### This is the step the derivation takes from
    `α·β′ = ∫ψ² > 0` together with the alternation of `β′`. -/
theorem transfer (a b : Nat → Int)
    (ha : ∀ k, IsSign (a k)) (hb : ∀ k, IsSign (b k))
    (hpos : ∀ k, 0 < a k * b k) (halt : Alternates b) :
    Alternates a := by
  intro k
  have e1 : a k = b k := eq_of_mul_pos (ha k) (hb k) (hpos k)
  have e2 : a (k + 1) = b (k + 1) := eq_of_mul_pos (ha (k + 1)) (hb (k + 1)) (hpos (k + 1))
  rw [e2, halt k, e1]

/-- ### AND THE TRANSFER RUNS BOTH WAYS, because the hypothesis is symmetric in
    `a` and `b`. ### Recorded because the derivation reads it in one direction
    and the record should not have to re-derive the other. -/
theorem transfer_symm (a b : Nat → Int)
    (ha : ∀ k, IsSign (a k)) (hb : ∀ k, IsSign (b k))
    (hpos : ∀ k, 0 < a k * b k) (halt : Alternates a) :
    Alternates b := by
  intro k
  have e1 : a k = b k := eq_of_mul_pos (ha k) (hb k) (hpos k)
  have e2 : a (k + 1) = b (k + 1) := eq_of_mul_pos (ha (k + 1)) (hb (k + 1)) (hpos (k + 1))
  rw [← e2, halt k, e1]

/-! ### THE WITNESS THAT THE HYPOTHESES ARE SATISFIABLE.

  ### A THEOREM WHOSE HYPOTHESES NOTHING SATISFIES IS VACUOUSLY TRUE AND SAYS
  ### NOTHING. So an inhabitant is exhibited. -/

/-- ### DEFINED BY RECURSION AND NOT BY `i % 2`, AND THE AXIOM PRINT IS WHY —
    see the note at the foot of this file. A recursive `flip` alternates
    DEFINITIONALLY, which is both cheaper and truer to the hypothesis it must
    satisfy. -/
def flip : Nat → Int
  | 0 => 1
  | (n + 1) => -(flip n)

theorem neg_is_sign {x : Int} (h : IsSign x) : IsSign (-x) := by
  match h with
  | Or.inl e => exact Or.inr (by rw [e])
  | Or.inr e => exact Or.inl (by rw [e]; decide)

theorem sq_pos {x : Int} (h : IsSign x) : (0 : Int) < x * x := by
  match h with
  | Or.inl e => rw [e]; decide
  | Or.inr e => rw [e]; decide

/-- ### `flip` alternates BY DEFINITION — no lemma, no rewriting, no axiom. -/
theorem flip_alternates : Alternates flip := fun _ => rfl

theorem flip_is_sign : ∀ k, IsSign (flip k)
  | 0 => Or.inl rfl
  | (n + 1) => neg_is_sign (flip_is_sign n)

theorem flip_pos : ∀ k, (0 : Int) < flip k * flip k :=
  fun k => sq_pos (flip_is_sign k)

/-- ### THE HYPOTHESES ARE JOINTLY SATISFIABLE AND THE CONCLUSION HOLDS OF THE
    WITNESS — so `transfer` is not vacuously true. -/
theorem transfer_nonvacuous : Alternates flip :=
  transfer flip flip flip_is_sign flip_is_sign flip_pos flip_alternates

/-! ### THE NOTE THE AXIOM PRINT EARNED, RECORDED IN THE FILE IT CHANGED.

  The first draft defined the witness as `fun i => if i % 2 = 0 then 1 else -1`
  and proved its two properties with `simp [flip, h]`. ### THE PRINT CAME BACK
  ### `flip_is_sign` AND `flip_pos` **depends on axioms: [propext]** — inherited
  ### from `simp`, not from anything the statement needed.

  The repair was to define `flip` by RECURSION instead, after which it
  alternates DEFINITIONALLY (`fun _ => rfl`), its sign property is a two-line
  induction, and its positivity factors through `sq_pos`. ### CHEAPER, TRUER TO
  ### THE HYPOTHESIS IT MUST SATISFY, AND ZERO-AXIOM.

  ### THIS IS THE SAME SPECIES b207 RECORDED ONE ACT AGO, WHERE `Int.mul_neg`
  ### PULLED `[propext]` AND THE REPAIR WAS TO RESTRUCTURE TO NEGATION.
  ### THE STANDING INFERENCE IS NOT THAT THE EXECUTOR WRITES BAD LEAN — IT IS
  ### THAT **THE PRINT IS PART OF THE FILE'S CONSTRUCTION, NOT A CHECK RUN ON A
  ### FINISHED FILE**, and an act that prints only at the end has already
  ### shipped the shape the tactic chose for it.
-/

end SignTransferShadow

#print axioms SignTransferShadow.control_pos
#print axioms SignTransferShadow.control_neg
#print axioms SignTransferShadow.signs_distinct
#print axioms SignTransferShadow.eq_of_mul_pos
#print axioms SignTransferShadow.transfer
#print axioms SignTransferShadow.transfer_symm
#print axioms SignTransferShadow.neg_is_sign
#print axioms SignTransferShadow.sq_pos
#print axioms SignTransferShadow.flip_alternates
#print axioms SignTransferShadow.flip_is_sign
#print axioms SignTransferShadow.flip_pos
#print axioms SignTransferShadow.transfer_nonvacuous
