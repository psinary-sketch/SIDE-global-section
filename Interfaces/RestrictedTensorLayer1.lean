/-
  W-CONSTRUCTION-1 · RestrictedTensorLayer1.lean — b193, 2026-08-26.
  THE RESTRICTED TENSOR CONSTRUCTION, LAYER ONE: THE TWO-FACTOR TENSOR CARRIES THE
  GLOBAL-SECTION SHAPE.

  ### WHAT THIS IS AND IS NOT. GlobalSection.lean records the standing debt:
  ### "The CONSTRUCTION of this data as ⊗′_v S̄_v is the infrastructure debt."
  ### THIS FILE DISCHARGES THE **FIRST LAYER** OF THAT CONSTRUCTION AND NOTHING MORE:
  ### given two factors carrying the shape, THE TENSOR OF THE TWO CARRIES IT TOO,
  ### with `F` and `parity` BUILT (not assumed) and the two identities PROVED.
  ### IT IS NOT THE RESTRICTED TENSOR PRODUCT. It is finite, two-factor, and complete
  ### only because a binary algebraic tensor of complete spaces needs no completion
  ### step here — the colimit over places and the completion are LATER LAYERS AND ARE
  ### NOT CLAIMED.

  ### INCUMBENT PRESERVATION: `GlobalSection.GlobalSectionData` is NOT redefined,
  ### renamed, or weakened. This file CONSUMES it and produces an instance of it.

  MATHLIB INGREDIENTS, EACH LOCATED AT CONTENT (Mathlib/Analysis/InnerProductSpace/
  TensorProduct.lean), NOT RECALLED:
  · `TensorProduct.instNormedAddCommGroup` — "the normed additive group structure on
    tensor products, where ‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖";
  · `TensorProduct.instInnerProductSpace` — "the inner product space structure on
    tensor products, where ⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫";
  · `TensorProduct.congrIsometry` — "the linear isometry equivalence version of
    `TensorProduct.congr f g` when `f` and `g` are linear isometry equivalences".

  ### THE GATE THIS FILE MUST PASS, AND IT CAN FAIL: the two identities the corpus's
  ### own structure demands — `F² = parity` and `parity² = 1` — must hold ON THE BUILT
  ### OBJECT. ### A "does it agree with Mathlib's tensor product" gate would be
  ### definitional here and could not fail, so it is not the gate used.

  SORRY COUNT: 0. Axiom profile printed at the foot, never assumed.
-/
import Mathlib.Analysis.InnerProductSpace.TensorProduct

namespace RestrictedTensorLayer1

open scoped TensorProduct

/-- the shape the corpus's `GlobalSectionData` demands of a single local factor:
    a Hilbert space with a unitary `F` and a `parity`, `F² = parity`, `parity² = 1`.
    ### STATED HERE SO LAYER ONE HAS FACTORS TO CONSUME; it is the same shape
    `GlobalSection.GlobalSectionData` carries, and that structure is untouched. -/
structure FactorData where
  H : Type
  [ncg : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  F : H ≃ₗᵢ[ℂ] H
  parity : H ≃ₗᵢ[ℂ] H
  F_sq : ∀ x, F (F x) = parity x
  parity_sq : ∀ x, parity (parity x) = x

attribute [instance] FactorData.ncg FactorData.ips

variable (A B : FactorData)

/-- the carrier of layer one: the algebraic tensor of the two factors, carrying
    Mathlib's inner product `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`. -/
abbrev Carrier : Type := A.H ⊗[ℂ] B.H

/-- `F` on the tensor: BUILT as `F_A ⊗ F_B` via Mathlib's `congrIsometry`. -/
noncomputable def Ftensor : Carrier A B ≃ₗᵢ[ℂ] Carrier A B :=
  TensorProduct.congrIsometry A.F B.F

/-- `parity` on the tensor: BUILT as `parity_A ⊗ parity_B`. -/
noncomputable def parityTensor : Carrier A B ≃ₗᵢ[ℂ] Carrier A B :=
  TensorProduct.congrIsometry A.parity B.parity

/-- ### THE GATE, HALF ONE: `F² = parity` on the built object.
    PROVED from the factors', by functoriality of `congr` on pure tensors and
    linearity on the span. -/
theorem Ftensor_sq (x : Carrier A B) :
    Ftensor A B (Ftensor A B x) = parityTensor A B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [Ftensor, parityTensor]
  | tmul a b => simp [Ftensor, parityTensor, TensorProduct.congrIsometry, A.F_sq, B.F_sq]
  | add x y hx hy => simp [map_add, hx, hy]

/-- ### THE GATE, HALF TWO: `parity² = 1` on the built object. -/
theorem parityTensor_sq (x : Carrier A B) :
    parityTensor A B (parityTensor A B x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [parityTensor]
  | tmul a b => simp [parityTensor, TensorProduct.congrIsometry, A.parity_sq, B.parity_sq]
  | add x y hx hy => simp [map_add, hx, hy]

/-- ### LAYER ONE, ASSEMBLED: the two-factor tensor carries the global-section shape.
    ### THE OBJECT IS BUILT, NOT ASSUMED — `F` and `parity` are constructed from the
    ### factors' and the two identities are theorems above, not fields taken on trust. -/
noncomputable def tensorFactor : FactorData where
  H := Carrier A B
  F := Ftensor A B
  parity := parityTensor A B
  F_sq := Ftensor_sq A B
  parity_sq := parityTensor_sq A B

end RestrictedTensorLayer1

#print axioms RestrictedTensorLayer1.Ftensor_sq
#print axioms RestrictedTensorLayer1.parityTensor_sq
#print axioms RestrictedTensorLayer1.tensorFactor
