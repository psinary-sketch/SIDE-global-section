/-
  W-CONSTRUCTION-1 act 3 — LocalLimit.lean: sitting 20's limit theorems and the CNU
  theorem, STATED IN LEAN against real Mathlib (toolchain v4.30.0-rc1, checkout
  cecd0c4d56). DESIGN: the abstract Hilbert-space content is PROVED here (no sorry);
  the concrete realization over L²(ℚ_p) with the standard character is a SINGLE
  labeled debt (`padicFourierData_exists`, OWED TO FILES B–C of the companion).
  Nothing at complete roster. Sorries are counted, labeled, never hidden.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open scoped InnerProductSpace

namespace LocalLimit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- THEOREM (sitting 20, Q2's positive half, abstract form): on the fixed space of any
    isometry `F`, the pairing `⟪x, F x⟫` is the squared norm — the constrained sector's
    positivity is a norm, by construction. PROVED, no sorry. -/
theorem inner_map_self_of_fixed (F : H →ₗᵢ[ℂ] H) (x : H) (hx : F x = x) :
    ⟪x, F x⟫_ℂ = (‖x‖ : ℂ) ^ 2 := by
  rw [hx, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- THEOREM (sitting 20, Q2's radical half, abstract form): if `F` maps a subspace ONTO
    itself, the pairing `⟪·, F ·⟫` has zero radical on it. PROVED, no sorry. -/
theorem radical_zero (F : H →ₗᵢ[ℂ] H) (S : Submodule ℂ H)
    (hsurj : ∀ z ∈ S, ∃ y ∈ S, F y = z) (x : H) (hx : x ∈ S)
    (h : ∀ y ∈ S, ⟪x, F y⟫_ℂ = 0) : x = 0 := by
  obtain ⟨y, hy, hFy⟩ := hsurj x hx
  have := h y hy
  rw [hFy, inner_self_eq_zero] at this
  exact this

/-- THEOREM (R2-1, the CNU theorem's abstract engine): a compressed isometry with the
    ESCAPE property (no nonzero vector of `S` has its whole forward orbit in `S`) has no
    unimodular eigenvalue: if the compression of `U` to `S` has `P(Ux) = λ x` with
    `|λ| = 1`, then `x = 0`. The escape hypothesis is exactly what the p-adic Fourier
    computation discharges (banked exact witnesses); here it is a hypothesis. PROVED
    from it, no sorry. -/
theorem no_unimodular_eigenvalue [CompleteSpace H]
    (U : H ≃ₗᵢ[ℂ] H) (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (hesc : ∀ x ∈ S, (∀ k : ℕ, (fun y => U y)^[k] x ∈ S) → x = 0)
    (x : H) (hx : x ∈ S) (lam : ℂ) (hlam : ‖lam‖ = 1)
    (heig : S.starProjection (U x) = lam • x) : x = 0 := by
  have hUxnorm : ‖S.starProjection (U x)‖ = ‖U x‖ := by
    rw [heig, norm_smul, hlam, one_mul, U.norm_map]
  have hUxmem : U x ∈ S := (S.mem_iff_norm_starProjection (U x)).mpr hUxnorm
  have hUx : U x = lam • x := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hUxmem, heig]
  have horbit : ∀ k : ℕ, (fun y => U y)^[k] x = lam ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, map_smul, hUx, smul_smul, pow_succ, mul_comm]
  refine hesc x hx fun k => ?_
  rw [horbit k]
  exact S.smul_mem _ hx

/-- the `C₄` idempotent attached to a fourth root `lam` (no inverses appear: `lam⁻¹ =
    lam³` when `lam⁴ = 1`). -/
noncomputable def proj4 (F : H →ₗ[ℂ] H) (lam : ℂ) (x : H) : H :=
  (4 : ℂ)⁻¹ • (x + lam ^ 3 • F x + lam ^ 2 • F (F x) + lam • F (F (F x)))

/-- THE FOUR-SECTOR DECOMPOSITION, CLAUSE ONE (the eigen-property), PROVED — the
    former `four_sector_decomposition_stub`'s first half, discharged 2026-08-22
    (b100, the sense build act): for a finite-order `F` (`F⁴ = 1`) and any fourth
    root `lam`, the `C₄` idempotent lands in `ker(F − lam)`. Closed-form spectral
    projections; no sorry. -/
theorem proj4_eigen (F : H →ₗ[ℂ] H) (h4 : ∀ y : H, F (F (F (F y))) = y)
    (lam : ℂ) (hlam : lam ^ 4 = 1) (x : H) :
    F (proj4 F lam x) = lam • proj4 F lam x := by
  unfold proj4
  rw [map_smul, smul_comm]
  congr 1
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, h4]
  rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
  rw [show lam * lam ^ 3 = lam ^ 4 by ring, hlam, one_smul]
  rw [show lam * lam ^ 2 = lam ^ 3 by ring, show lam * lam = lam ^ 2 by ring]
  abel

/-- THE FOUR-SECTOR DECOMPOSITION, CLAUSE TWO (completeness), PROVED — the four
    `C₄` idempotents sum to the identity, so `H = ⊕_{lam⁴=1} ker(F − lam)` as the
    docstring stated. With `proj4_eigen`: the decomposition, discharged. No sorry. -/
theorem proj4_sum (F : H →ₗ[ℂ] H) (x : H) :
    proj4 F 1 x + proj4 F Complex.I x + proj4 F (-1) x + proj4 F (-Complex.I) x = x := by
  unfold proj4
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
  have hnI2 : (-Complex.I) ^ 2 = -1 := by rw [neg_pow]; simp [hI2]
  have hnI3 : (-Complex.I) ^ 3 = Complex.I := by rw [pow_succ, hnI2]; ring
  rw [hI2, hI3, hnI2, hnI3]
  norm_num
  module

/-- THE SOT LIMIT OF THE LEVEL COMPRESSIONS, PROVED — the former stub's second
    half, discharged 2026-08-22 (b100): for a MONOTONE family `U` of submodules
    with orthogonal projections, the compressions of a bounded operator `A` to the
    levels converge strongly to the compression on the closure of the supremum.
    Mathlib's `starProjection_tendsto_closure_iSup` supplies the projection
    convergence; the operator step is the three-term split with the `‖P‖ ≤ 1`
    domination. No sorry.

    ### THE SCOPE, STATED SO NO READER OVER-CLAIMS IT (b100, filed at full
    prominence): this discharges the ABSTRACT clause the docstring stated — the
    abstract-lemma-pass debt this file named. It does NOT certify that the
    programme's concrete level family satisfies the MONOTONICITY hypothesis; that
    is a separate, concrete question whose owner is the construction, and b70's
    decided non-stabilization witness bears on it. The abstract lemma is proved;
    its applicability to the concrete family is NOT claimed here. -/
theorem compression_tendsto {ι : Type*} [Preorder ι]
    (U : ι → Submodule ℂ H) [∀ i, (U i).HasOrthogonalProjection]
    [(⨆ i, U i).topologicalClosure.HasOrthogonalProjection]
    (hU : Monotone U) (A : H →L[ℂ] H) (x : H) :
    Filter.Tendsto (fun i => (U i).starProjection (A ((U i).starProjection x))) Filter.atTop
      (nhds ((⨆ i, U i).topologicalClosure.starProjection
            (A ((⨆ i, U i).topologicalClosure.starProjection x)))) := by
  set P := (⨆ i, U i).topologicalClosure with hP
  have h2 : Filter.Tendsto (fun i => (U i).starProjection (A (P.starProjection x)))
      Filter.atTop (nhds (P.starProjection (A (P.starProjection x)))) :=
    Submodule.starProjection_tendsto_closure_iSup U hU _
  have hx : Filter.Tendsto (fun i => (U i).starProjection x) Filter.atTop
      (nhds (P.starProjection x)) :=
    Submodule.starProjection_tendsto_closure_iSup U hU x
  have hxn : Filter.Tendsto (fun i => ‖(U i).starProjection x - P.starProjection x‖)
      Filter.atTop (nhds 0) := tendsto_iff_norm_sub_tendsto_zero.mp hx
  have h1 : Filter.Tendsto (fun i => (U i).starProjection (A ((U i).starProjection x))
      - (U i).starProjection (A (P.starProjection x))) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun i => ‖A‖ * ‖(U i).starProjection x - P.starProjection x‖)
      (fun i => norm_nonneg _) (fun i => ?_) ?_
    · have hlin : (U i).starProjection (A ((U i).starProjection x))
          - (U i).starProjection (A (P.starProjection x))
          = (U i).starProjection (A ((U i).starProjection x - P.starProjection x)) := by
        rw [← map_sub, ← map_sub]
      rw [hlin]
      calc ‖(U i).starProjection (A ((U i).starProjection x - P.starProjection x))‖
          ≤ ‖A ((U i).starProjection x - P.starProjection x)‖ :=
            Submodule.norm_starProjection_apply_le _ _
        _ ≤ ‖A‖ * ‖(U i).starProjection x - P.starProjection x‖ := A.le_opNorm _
    · have := hxn.const_mul ‖A‖
      simpa using this
  have hsum := h1.add h2
  simpa using hsum

/-- THE HULL (b101, the monotonicity act): the running span of an arbitrary
    family — constructed unconditionally, so that a limit object exists for ANY
    level family whatever, monotone or not. -/
def hull {ι : Type*} [Preorder ι] (U : ι → Submodule ℂ H) (i : ι) : Submodule ℂ H :=
  ⨆ j, ⨆ (_ : j ≤ i), U j

theorem hullMono {ι : Type*} [Preorder ι] (U : ι → Submodule ℂ H) :
    Monotone (hull U) := by
  intro a b hab
  refine iSup_mono' fun j => ⟨j, ?_⟩
  exact iSup_mono' fun hj => ⟨le_trans hj hab, le_rfl⟩

theorem hull_ge {ι : Type*} [Preorder ι] (U : ι → Submodule ℂ H) (i : ι) :
    U i ≤ hull U i :=
  le_iSup_of_le i (le_iSup_of_le le_rfl le_rfl)

theorem hull_iSup_eq {ι : Type*} [Preorder ι] (U : ι → Submodule ℂ H) :
    (⨆ i, hull U i) = ⨆ i, U i := by
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun j => iSup_le fun _ => le_iSup U j
  · exact iSup_mono fun i => hull_ge U i

/-- THE HULL'S SOT LIMIT, UNCONDITIONAL IN THE FAMILY: no monotonicity
    hypothesis on `U` -- the hull supplies it by construction. The limit object is
    the compression on the closure of the hull's supremum, and `hull_iSup_eq`
    (proved above) identifies that supremum with the ORIGINAL family's. -/
theorem hull_compression_tendsto {ι : Type*} [Preorder ι]
    (U : ι → Submodule ℂ H) [∀ i, (hull U i).HasOrthogonalProjection]
    [(⨆ i, hull U i).topologicalClosure.HasOrthogonalProjection]
    (A : H →L[ℂ] H) (x : H) :
    Filter.Tendsto (fun i => (hull U i).starProjection (A ((hull U i).starProjection x))) Filter.atTop
      (nhds ((⨆ i, hull U i).topologicalClosure.starProjection
            (A ((⨆ i, hull U i).topologicalClosure.starProjection x)))) :=
  compression_tendsto (hull U) (hullMono U) A x

/-- ACT 6 (the ε-lemma's clean half): eigenvectors of `F` stay eigenvectors under any
    commuting operator — if `A∘F = F∘A` and `F x = λ•x` then `F (A x) = λ•(A x)`.
    THE USE: on Weil-even test data `ϑ(g)` commutes with `F` (the intertwining
    `F U_λ = U_{1/λ} F` plus `g(λ) = g(1/λ)`), so the `±1` sectors of the even Sonin
    space are `ϑ(g)`-invariant and the trace SPLITS: our `Θ` is CC Thm 4.7's trace
    MINUS the `(−1)`-sector term. The trace-class bookkeeping of that split is OWNED
    by the ε-lemma (build document §14). PROVED, no sorry. -/
theorem eigenvector_of_commute (A F : H →ₗ[ℂ] H) (hc : ∀ x, A (F x) = F (A x))
    (lam : ℂ) (x : H) (hx : F x = lam • x) : F (A x) = lam • A x := by
  rw [← hc, hx, map_smul]

/-- ACT 12 (the inequality's L2 link, PROVED): for nested closed subspaces `T ≤ S`
    the compressed positive form is dominated — `‖P_T x‖ ≤ ‖P_S x‖`. With `T` the
    `E₁` sector (`Π₊S`, sitting 22's decomposition) inside `S` the Sonin space, this
    is "the `E₁` positive form ≤ the full one": the chain's sound archimedean link.
    PROVED, no sorry. -/
theorem nested_projection_norm_le [CompleteSpace H] (T S : Submodule ℂ H)
    [T.HasOrthogonalProjection] [S.HasOrthogonalProjection] (hTS : T ≤ S) (x : H) :
    ‖T.starProjection x‖ ≤ ‖S.starProjection x‖ := by
  have h := Submodule.starProjection_comp_starProjection_of_le (𝕜 := ℂ) hTS
  have hx : T.starProjection (S.starProjection x) = T.starProjection x := by
    simpa using DFunLike.congr_fun h x
  calc ‖T.starProjection x‖ = ‖T.starProjection (S.starProjection x)‖ := by rw [hx]
    _ ≤ ‖S.starProjection x‖ := T.norm_starProjection_apply_le _

/-- ACT 14 (the no-exact-level obstruction, PROVED): ℝ has no compact open additive
    subgroup — an open subgroup of the connected line is clopen, hence everything,
    and the line is noncompact. This is exactly why sitting 8's exact-transport chart
    (which rides ℚ_p's compact-open levels `ℤ_p ⊃ p^nℤ_p`) cannot transpose to `∞`:
    the archimedean place is the place WITHOUT finite exact levels — the grid model
    is an approximation scheme, never a restriction. PROVED, no sorry. -/
theorem real_no_compact_open_addSubgroup (H : AddSubgroup ℝ)
    (ho : IsOpen (H : Set ℝ)) : ¬ IsCompact (H : Set ℝ) := by
  have hclop : IsClopen (H : Set ℝ) := (⟨H, ho⟩ : OpenAddSubgroup ℝ).isClopen
  have huniv : (H : Set ℝ) = Set.univ := hclop.eq_univ ⟨0, H.zero_mem⟩
  intro hc
  rw [huniv] at hc
  exact noncompact_univ ℝ hc

/-- THE NEXT ERA's OPENING THEOREM (theorem-first; the finite places closed at EVERY p):
    the fixed-point localization, GENERAL p — for any prime `p`, level `n ≥ 1`, step
    `k ≥ 1`, NO Sonin cell `1 ≤ α < p^n` satisfies `p^n ∣ α(p^k − 1)`. This is the
    general-`p` core of trace silence and of the escape hypothesis' arithmetic: the
    banked `p = 2, 3` instances (TraceSilence, no axioms) are its shadows; every other
    step of sitting 20's chain is p-free by construction (the abstract theorems above;
    file A proved for arbitrary p). PROVED, no sorry. -/
theorem general_p_no_fixed_cell (p n k α : ℕ) (hp : p.Prime)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hα1 : 1 ≤ α) (hαn : α < p ^ n) :
    ¬ (p ^ n ∣ α * (p ^ k - 1)) := by
  intro hdvd
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  have hndvd : ¬ (p ∣ p ^ k - 1) := by
    intro h
    have h2 : p ∣ p ^ k := dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hk)
    have h3 : p ∣ 1 := by
      have h4 := Nat.dvd_sub h2 h
      rwa [Nat.sub_sub_self hpk] at h4
    exact hp.one_lt.not_ge (Nat.le_of_dvd one_pos h3)
  have hcop : Nat.Coprime (p ^ n) (p ^ k - 1) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd)
  have hα : p ^ n ∣ α := (Nat.Coprime.dvd_of_dvd_mul_right hcop) hdvd
  exact (Nat.le_of_dvd (Nat.lt_of_lt_of_le Nat.zero_lt_one hα1) hα).not_gt hαn


/-! ### THE TOWER'S ALL-LEVELS ARITHMETIC (b102, the eighth seam close's strikeable)

  The four index facts that row 65 decided at the banked truncation pairs, here
  PROVED FOR ALL `p` and `n` (`0 < p`; the banked cells are prime powers, so the
  hypothesis is free there). The chain is the one the b101 registration wrote
  longhand; what changes is the grade.

  ### WHY THIS LIVES AT THE CLASSICAL PROFILE AND NOT AT THE CORE ZERO-AXIOM BAR
  (the strikeable's honest landing, verified by print this act): the statements
  are PROVED, but they cannot reach the zero-axiom bar, and the reason is a
  property of Lean's own library rather than of the mathematics. Every route to
  them runs through core `Nat` lemmas that are themselves propext-carrying —
  `Nat.mul_assoc`, `Nat.pow_add`, `Nat.dvd_of_mod_eq_zero`, `Nat.mul_mod_mul_left`,
  `Nat.add_mul_mod_self_left`, `Nat.mul_div_cancel_left`, `Nat.mul_mod_right`,
  `Nat.mul_left_comm` (each printed this act). `rw` itself is clean; the taint is
  inherited transitively, not introduced by the proofs. Reaching the bar would
  mean reproving a chunk of core `Nat` arithmetic, which is not this act's
  business. So: the banked-pairs terminals stay in Core at the zero-axiom bar
  (row 65, unchanged), and the universal statements live here, declared, at
  {propext, Classical.choice, Quot.sound}. `simp`, `omega` and `ac_rfl` are not
  used anywhere below.
-/

/-- exponent split: p^(2n+2) = p^(n+1) * p^(n+1) -/
theorem pow_split_even (p n : Nat) : p ^ (2 * n + 2) = p ^ (n + 1) * p ^ (n + 1) := by
  rw [← Nat.pow_add]
  have : n + 1 + (n + 1) = 2 * n + 2 := by
    rw [Nat.two_mul, Nat.add_assoc, Nat.add_comm 1 (n + 1), Nat.add_assoc]
    show n + (n + 2) = n + n + 2
    exact (Nat.add_assoc n n 2).symm
  rw [this]

/-- exponent split: p^(2n+1) = p^(n+1) * p^n -/
theorem pow_split_odd (p n : Nat) : p ^ (2 * n + 1) = p ^ (n + 1) * p ^ n := by
  rw [← Nat.pow_add]
  have : n + 1 + n = 2 * n + 1 := by
    rw [Nat.two_mul, Nat.add_right_comm]
  rw [this]

/-- (2) THE INNER-SUM RULE, ALL LEVELS -/
theorem inner_sum_general (p n r : Nat) (h : r % p ^ (n + 1) = 0) :
    (r * p ^ (2 * n + 1)) % p ^ (2 * n + 2) = 0 := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  subst hk
  rw [pow_split_even, pow_split_odd]
  have e : p ^ (n + 1) * k * (p ^ (n + 1) * p ^ n)
      = p ^ (n + 1) * p ^ (n + 1) * (k * p ^ n) := by
    rw [Nat.mul_assoc, Nat.mul_assoc]
    congr 1
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm k (p ^ (n + 1))]
  rw [e]
  exact Nat.mul_mod_right _ _

/-- (4) THE QUOTIENT LANDS IN THE BALL, ALL LEVELS -/
theorem quotient_general (p n r : Nat) (hp : 0 < p) (h : r % p ^ (n + 1) = 0) :
    (r / p) % p ^ n = 0 := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  subst hk
  have e : p ^ (n + 1) * k = p * (p ^ n * k) := by
    rw [Nat.pow_succ, Nat.mul_comm (p ^ n) p, Nat.mul_assoc]
  rw [e, Nat.mul_div_cancel_left _ hp]
  exact Nat.mul_mod_right _ _

theorem pow_split_lead (p n : Nat) : p ^ (2 * n + 1) = p * p ^ (2 * n) := by
  rw [Nat.pow_succ, Nat.mul_comm]

theorem two_n_split (p n : Nat) : p ^ (2 * n) = p ^ n * p ^ n := by
  rw [← Nat.pow_add, Nat.two_mul]

/-- (1) THE SUPPORT SIDE, ALL LEVELS, in mod form (no subtraction anywhere). -/
theorem ball_pullback_general (p n m j : Nat) (hp : 0 < p) :
    (((p * m + p ^ (2 * n + 1) * j) % p ^ (n + 1) = 0) ↔ (m % p ^ n = 0)) := by
  have hfac : p * m + p ^ (2 * n + 1) * j = p * (m + p ^ n * (p ^ n * j)) := by
    rw [pow_split_lead, two_n_split, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_add]
  have hmod : (p * m + p ^ (2 * n + 1) * j) % p ^ (n + 1)
      = p * ((m + p ^ n * (p ^ n * j)) % p ^ n) := by
    rw [hfac, Nat.pow_succ, Nat.mul_comm (p ^ n) p, Nat.mul_mod_mul_left]
  rw [hmod, Nat.add_mul_mod_self_left]
  constructor
  · intro h
    rcases Nat.mul_eq_zero.mp h with h0 | h0
    · subst h0; exact absurd hp (Nat.lt_irrefl 0)
    · exact h0
  · intro h
    rw [h, Nat.mul_zero]

theorem rearrange (a p k m : Nat) : a * p * k * p * m = p * p * (a * (k * m)) := by
  calc a * p * k * p * m
      = a * (p * (k * (p * m))) := by
        rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
    _ = a * (p * (p * (k * m))) := by rw [Nat.mul_left_comm k p m]
    _ = p * (a * (p * (k * m))) := by rw [Nat.mul_left_comm]
    _ = p * (p * (a * (k * m))) := by rw [Nat.mul_left_comm a p (k * m)]
    _ = p * p * (a * (k * m)) := by rw [← Nat.mul_assoc]

/-- (3) THE TRANSFORM INDEX SHIFT, ALL LEVELS (factor p², no subtraction). -/
theorem transform_shift_general (p n r m : Nat) (hp : 0 < p)
    (h : r % p ^ (n + 1) = 0) :
    (r * p * m) % p ^ (2 * n + 2) = p ^ 2 * (((r / p) * m) % p ^ (2 * n)) := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  subst hk
  have hdiv : p ^ (n + 1) * k / p = p ^ n * k := by
    rw [Nat.pow_succ, Nat.mul_comm (p ^ n) p, Nat.mul_assoc,
      Nat.mul_div_cancel_left _ hp]
  have hp2 : p ^ 2 = p * p := by rw [Nat.pow_succ, Nat.pow_one]
  have hr : p ^ (2 * n + 2) = p * (p * p ^ (2 * n)) := by
    rw [← Nat.mul_assoc, ← hp2, ← Nat.pow_add, Nat.add_comm]
  have hl : p ^ (n + 1) * k * p * m = p * (p * (p ^ n * (k * m))) := by
    rw [Nat.pow_succ, rearrange (p ^ n) p k m, Nat.mul_assoc]
  rw [hdiv, hl, hr, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hp2,
    Nat.mul_assoc, Nat.mul_assoc (p ^ n) k m]

/-- THE CONCRETE DEBT, in one place: the p-adic Fourier data over `L²(ℚ_p)` — the
    transform as a linear isometry equivalence with `F² = parity`, the Sonin closure as
    a closed subspace, the escape property. OWED TO FILES B–C (the standard character;
    Haar; Plancherel-by-the-tower; Schwartz–Bruhat). -/
structure PadicFourierData (p : ℕ) [Fact p.Prime] where
  H : Type
  [ncg : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  F : H ≃ₗᵢ[ℂ] H
  parity : H ≃ₗᵢ[ℂ] H
  F_sq : ∀ x, F (F x) = parity x
  parity_sq : ∀ x, parity (parity x) = x

/- THE REALIZATION over L²(ℚ_p): NOT claimed here. Per the 2026-08-19 ruling (no sorry
    in a kernel) the former existence statement moved to the working layer
    (relay/reports/2026-08-19-sorry-ledger-cleared.md, item 1) until it can enter
    PROVED. The structure above carries no proof obligation. -/


/-- ACT 4, THE MATHLIB LEG'S NEW STATEMENT (the spectral question's structural half):
    the minimal unitary dilation of the completely non-unitary compressed scaling is
    ABSOLUTELY CONTINUOUS (Nagy-Foias). Mathlib holds NO dilation theory (grep-checked:
    zero hits for unitary dilation / Sz.-Nagy) - the statement cannot yet be FORMED, so
    the debt is recorded as a named stub, not a sorry: OWED TO DILATION THEORY. The
    density-is-the-zero-side question is (AC)-open; the characteristic function of the
    compressed scaling (one-shell defect) is the named next object. -/
theorem ac_dilation_stub : True := trivial

end LocalLimit

#print axioms LocalLimit.inner_map_self_of_fixed
#print axioms LocalLimit.radical_zero
#print axioms LocalLimit.no_unimodular_eigenvalue
#print axioms LocalLimit.eigenvector_of_commute
#print axioms LocalLimit.nested_projection_norm_le
#print axioms LocalLimit.real_no_compact_open_addSubgroup
#print axioms LocalLimit.general_p_no_fixed_cell
#print axioms LocalLimit.proj4_eigen
#print axioms LocalLimit.proj4_sum
#print axioms LocalLimit.compression_tendsto
#print axioms LocalLimit.hullMono
#print axioms LocalLimit.hull_ge
#print axioms LocalLimit.hull_iSup_eq
#print axioms LocalLimit.hull_compression_tendsto
#print axioms LocalLimit.inner_sum_general
#print axioms LocalLimit.quotient_general
#print axioms LocalLimit.ball_pullback_general
#print axioms LocalLimit.transform_shift_general
