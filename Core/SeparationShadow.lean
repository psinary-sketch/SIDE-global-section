/-
  THE SEPARATION SEAL'S DECIDED CORE · SeparationShadow.lean
  ==========================================================

  Ferry 2026-08-25 (b170). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  b154 read the requirements and found the apportionment's freedom. Its requirement
  **R4** is the owner's own phrase: the residual has TWO parts, `resid_N = D_N + R_N`,
  the divergent part and the truncation remainder. Its **R5** — the t(n)-weighting
  warrant, and b154 flags it as a step *"the owner does not take in words"* — speaks
  only of the DIVERGENT part.

  This module decides what that leaves, on finite data, ### **in the TWO-PART setting
  that row 69 does not cover**: row 69 decides the void gate and the one-scalar
  factoring over a SINGLE residual; these terminals give the residual its two parts
  with INDEPENDENT shares and ask what any sector-summed statement can see.

  · `void_gate_cannot_see_either_share` — across every split and every pair of shares in
    the sweep the gate holds, and ### the sector-summed total is IDENTICAL. ***Nothing
    summed over sectors can reach either share.***
  · `divergent_share_fixed_leaves_the_remainder_free` — ### THE SEAL, DECIDED: two
    configurations agreeing on the divergent share and on every total, differing only in
    the remainder's share, give DIFFERENT `W₊` — and both satisfy the gate. ***So a
    requirement that fixes the divergent share fixes nothing about the member.***
  · `the_two_shares_are_independent_coordinates` — varying the divergent share alone
    also separates, so neither coordinate is a function of the other.
  · `degenerate_case_stated_not_hidden` — when `R = 0` the remainder's share is
    invisible and the question is vacuous there. ### b58's third part, stated rather than
    passed over.

  ### WHAT THIS DOES NOT DO. It does not choose a member, and it is not a ruling: it
  ### says the choice is DEFINITIONAL, which is a different kind of statement. It does
  ### not show that no statement WHATEVER separates members — `μ = 1/2` separates them,
  ### and writing it down IS the definitional act. ### THE SEAL IS OVER THE REQUIREMENTS'
  ### OWN VOCABULARY, WHICH IS A DOCUMENTED SET AND NOT A MATHEMATICAL SPACE: if an owner
  ### asserts a new requirement, the vocabulary grows and this must be re-run.
  ### AND ITS LOAD-BEARING STEP IS R4 — A READING OF THE OWNER'S PHRASE — NOT A THEOREM.

  Nothing here re-grades any result, prefers any member, or bears on `h2`; b38's recorded
  (I-differ) verdict stands untouched. Bank: relay data/b170_separation_seal.txt.
-/

set_option maxRecDepth 16384

namespace SeparationShadow

/-- the mode-diagonal raw traces (b38's `tr_n_raw`), on finite data. -/
def aData : List Int := [7, 3, 5, 2, 9, 4]

/-- the mode-diagonal epsilon parts (b38's `E2_n`). -/
def bData : List Int := [1, 2, 1, 1, 3, 2]

/-- the certified arch column. -/
def archA : Int := 6

/-- the share denominator: shares are `p / shareQ`, cleared throughout. -/
def shareQ : Int := 100

def total (l : List Int) : Int := l.foldl (· + ·) 0

/-- entries at indices 0, 2, 4, … — the even sector, per b38's own reading. -/
def evens : List Int → List Int
  | [] => []
  | x :: xs => x :: (match xs with | [] => [] | _ :: ys => evens ys)

/-- `resid_N := Tr_raw_N − A − E2_N`, b38's own definition. -/
def resid : Int := total aData - archA - total bData

/-- `shareQ · W₊` under R4's TWO-PART split, with INDEPENDENT shares `pD`, `pR`. -/
def wPlusQ (dPart rPart pD pR : Int) : Int :=
  shareQ * (total (evens aData) - total (evens bData)) - pD * dPart - pR * rPart

/-- `shareQ · W₋`, the complementary sector taking the complementary shares. -/
def wMinusQ (dPart rPart pD pR : Int) : Int :=
  shareQ * ((total aData - total (evens aData)) - (total bData - total (evens bData)))
    - (shareQ - pD) * dPart - (shareQ - pR) * rPart

/-- splits of the residual into its two parts, `D + R = resid`. -/
def splits : List (Int × Int) := [(resid, 0), (0, resid), (resid - 4, 4), (7, resid - 7)]

def pdVals : List Int := [0, 37, 61, 100]
def prVals : List Int := [0, 12, 88, 100]

/-- ### NOTHING SUMMED OVER SECTORS CAN REACH EITHER SHARE, decided: across every split
    and every pair of shares the void gate holds, ### and the sector-summed total is
    identical to `shareQ · A` throughout. -/
theorem void_gate_cannot_see_either_share :
    splits.all (fun s => pdVals.all (fun pD => prVals.all (fun pR =>
      decide (wPlusQ s.1 s.2 pD pR + wMinusQ s.1 s.2 pD pR = shareQ * archA)))) = true := by
  decide

/-- ### THE SEAL, DECIDED. Two configurations agreeing on the DIVERGENT share `pD = 61`
    and on every sector-summed total, differing only in the remainder's share, give
    ### DIFFERENT `W₊` — and both satisfy the gate. ***A requirement that fixes the
    divergent share fixes nothing about the member.*** -/
theorem divergent_share_fixed_leaves_the_remainder_free :
    (decide (wPlusQ (resid - 4) 4 61 12 ≠ wPlusQ (resid - 4) 4 61 88)
     && decide (wPlusQ (resid - 4) 4 61 12 + wMinusQ (resid - 4) 4 61 12 = shareQ * archA)
     && decide (wPlusQ (resid - 4) 4 61 88 + wMinusQ (resid - 4) 4 61 88 = shareQ * archA)) = true := by
  decide

/-- ### THE TWO SHARES ARE INDEPENDENT COORDINATES: varying the divergent share alone
    also separates, so neither is a function of the other and fixing one cannot fix the
    other by implication. -/
theorem the_two_shares_are_independent_coordinates :
    (decide (wPlusQ (resid - 4) 4 37 12 ≠ wPlusQ (resid - 4) 4 61 12)
     && decide (wPlusQ (resid - 4) 4 61 12 ≠ wPlusQ (resid - 4) 4 61 88)) = true := by
  decide

/-- ### THE DEGENERATE CASE, STATED RATHER THAN PASSED OVER (b58's third part): when the
    truncation remainder is zero the freedom is invisible — differing `pR` gives the same
    `W₊` — so the seal's question is vacuous exactly there, and the record holds no
    measurement saying whether it is. -/
theorem degenerate_case_stated_not_hidden :
    (decide (wPlusQ resid 0 61 12 = wPlusQ resid 0 61 88)
     && decide (wPlusQ 0 resid 61 12 ≠ wPlusQ 0 resid 61 88)) = true := by
  decide

end SeparationShadow

#print axioms SeparationShadow.void_gate_cannot_see_either_share
#print axioms SeparationShadow.divergent_share_fixed_leaves_the_remainder_free
#print axioms SeparationShadow.the_two_shares_are_independent_coordinates
#print axioms SeparationShadow.degenerate_case_stated_not_hidden
