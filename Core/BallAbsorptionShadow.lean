/-
  b270 · BallAbsorptionShadow.lean — THE VANILLA LEG (zero axioms)
  ================================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES — and, far more importantly, WHAT IT DOES NOT.

  IT COMPILES NO PAIRING. `⟨U^k S_quot u_v, u_v⟩` IS ABSENT HERE. So are `U`, `S_quot`,
  `V_inv`, `u_v`, `Son(p,n)`, `E₁` and `ℤ[ζ_N]`. The refutation of (SPEC-1) is DERIVED at
  content in relay `data/b270_ambient_pairing_properties.txt` and controlled by exact
  reduction modulo `Φ_N` in `data/b270_run.txt`. NOTHING BELOW IS THAT DERIVATION,
  AND NOTHING BELOW IS EVIDENCE FOR IT.

  IT COMPILES NO AGGREGATION AND ADOPTS NO CANDIDATE. M-2 is owed and stays owed.

  THE CONDITION FOR BUILDING THIS FILE AT ALL WAS CHECKED, NOT ASSUMED. b269 built
  nothing, and its reason is quoted in relay's bank: a toy model that compiles cleanly
  and settles nothing, in a file whose header names the real spaces, is the double-name
  species in Lean. THAT TEST IS APPLIED AGAIN HERE AND ANSWERED DIFFERENTLY, for one
  reason: the residue below is not a stand-in for the derivation's mechanism — IT IS
  THAT MECHANISM, and it happens to be finite arithmetic on `ℤ/p^{2n}`.

  What is here is the FINITE-DECIDABLE RESIDUE ONLY, in three parts:

    (1) THE ABSORPTION LAW. In the model at `(p, n)` the modulus is `N = p^(2n)` and the
        ball is `{ m : m % p^n = 0 }` (b8's `model`, quoted in relay's registration §E).
        Then FOR EVERY `m`, `(p^n * m) % N` LIES IN THE BALL. This is the arithmetic
        reason the pairing vanishes at `k = n`: the operator sends the whole space into
        the ball, and the derivation's `u_v` vanishes there.

    (2) THAT THE LAW IS SPECIFIC TO `k ≥ n`, NOT GENERAL. At `(p,n) = (2,2)` and `k = 1`
        there EXISTS an off-ball `m` whose image `(p^k * m) % N` is also off-ball. WITHOUT
        THIS PART, PART (1) WOULD BE COMPATIBLE WITH A DEAD OPERATOR and would settle
        nothing — which is precisely the failure mode this file was tested against.

    (3) THE EMPTY-ORBIT LAW AT LEVEL 1, decided at the odd places b226's choice uses:
        no off-ball `m` has `p*m` off-ball, so the orbit relation of `V_inv` is empty
        there and the projection is multiplication by the off-ball indicator.

  WHAT IS NOT DECIDED HERE, AND MUST NOT BE READ INTO IT:
    · that `u_v` vanishes on the ball — that is b268's derivation, shadowed separately
      in `GeneratorSupportShadow.lean`; this file NEVER mentions `u_v`;
    · that (SPEC-1) is refuted — that conclusion needs both halves and is relay's;
    · anything about `h2`, which stands exactly where the deposit left it.

  THE COMPOSITION OF (1) AND `u_v`'s VANISHING IS THE REFUTATION. THIS FILE HOLDS ONE
  HALF OF IT, HONESTLY LABELLED, AND CLAIMS NOTHING ABOUT THE OTHER.
-/

namespace B270

/-- `N = p^(2n)` — b8's `model`, the modulus of the truncated cell. -/
def N (p n : Nat) : Nat := p ^ (2 * n)

/-- The ball: multiples of `p^n` in `ℤ/N`. -/
def inBall (p n m : Nat) : Bool := m % (p ^ n) == 0

/-- The image of `m` under the `k`-th power of the scaling map, on indices only.
    THE NORMALISATION `p^{-k/2}` IS ABSENT: it is a nonzero scalar and cannot change
    whether an index lies in the ball. THAT IS WHY DROPPING IT IS HONEST HERE. -/
def img (p n k m : Nat) : Nat := (p ^ k * m) % N p n

/-- (1) THE ABSORPTION LAW at one cell: every index is sent into the ball by `k = n`. -/
def absorbs (p n : Nat) : Bool :=
  (List.range (N p n)).all (fun m => inBall p n (img p n n m))

/-- (3) THE EMPTY-ORBIT LAW at one cell: no off-ball `m` has `p*m` off-ball. -/
def emptyOrbit (p n : Nat) : Bool :=
  (List.range (N p n)).all
    (fun m => (inBall p n m) || (inBall p n (img p n 1 m)))

/-- (2) The witness that the operator is not dead below `k = n`. -/
def hasLiveStep (p n k : Nat) : Bool :=
  (List.range (N p n)).any
    (fun m => (!inBall p n m) && (!inBall p n (img p n k m)))

/-! ### (1) THE ABSORPTION LAW, at every cell b226's choice reaches. -/

theorem absorb_2_2 : absorbs 2 2 = true := by decide
theorem absorb_3_1 : absorbs 3 1 = true := by decide
theorem absorb_5_1 : absorbs 5 1 = true := by decide
theorem absorb_7_1 : absorbs 7 1 = true := by decide
theorem absorb_11_1 : absorbs 11 1 = true := by decide
theorem absorb_13_1 : absorbs 13 1 = true := by decide

/-! ### (3) THE EMPTY-ORBIT LAW — level 1 only, and that restriction is the content. -/

theorem empty_3_1 : emptyOrbit 3 1 = true := by decide
theorem empty_5_1 : emptyOrbit 5 1 = true := by decide
theorem empty_7_1 : emptyOrbit 7 1 = true := by decide
theorem empty_11_1 : emptyOrbit 11 1 = true := by decide

/-! ### (2) THE OPERATOR IS NOT DEAD. `(2,2)` at `k = 1` has a live off-ball step.

    WITHOUT THIS THE FILE WOULD BE THE DOUBLE-NAME SPECIES: part (1) alone is exactly
    what a vacuously trivial operator would also satisfy. -/

theorem live_2_2_k1 : hasLiveStep 2 2 1 = true := by decide

/-! ### THE POLARITY REFUSALS. Each is FALSE and is decided FALSE, so the file's
    positive terminals are not vacuous. -/

/-- The empty-orbit law FAILS at level 2 — `(2,2)` has off-ball steps. -/
theorem refuse_empty_2_2 : emptyOrbit 2 2 = false := by decide

/-- The absorption law is NOT already true one step early at `(2,2)`: `k = 1` does not
    absorb. THE LAW IS ABOUT `k = n` AND NOT ABOUT EVERY `k`. -/
theorem refuse_absorb_early_2_2 :
    (List.range (N 2 2)).all (fun m => inBall 2 2 (img 2 2 1 m)) = false := by decide

/-- There is NO live off-ball step at `k = n` — the exact complement of `live_2_2_k1`. -/
theorem refuse_live_2_2_k2 : hasLiveStep 2 2 2 = false := by decide

/-- And none at level 1 either, where `k = n = 1`. -/
theorem refuse_live_3_1_k1 : hasLiveStep 3 1 1 = false := by decide

/-! ### THE AXIOM PROFILE, PRINTED BY THIS FILE ITSELF.

    b227's standard: a claimed compile is reported ONLY from its printed profile. These
    prints live in the banked file so the profile is produced by compiling the artefact
    that was banked — not by compiling a copy of it. -/

#print axioms B270.absorb_2_2
#print axioms B270.absorb_3_1
#print axioms B270.absorb_5_1
#print axioms B270.absorb_7_1
#print axioms B270.absorb_11_1
#print axioms B270.absorb_13_1
#print axioms B270.empty_3_1
#print axioms B270.empty_5_1
#print axioms B270.empty_7_1
#print axioms B270.empty_11_1
#print axioms B270.live_2_2_k1
#print axioms B270.refuse_empty_2_2
#print axioms B270.refuse_absorb_early_2_2
#print axioms B270.refuse_live_2_2_k2
#print axioms B270.refuse_live_3_1_k1

end B270
