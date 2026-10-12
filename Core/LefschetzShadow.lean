/-
  THE LEFSCHETZ FAMILY · LefschetzShadow.lean
  ============================================

  Ferry 2026-08-21 (b67, the congruence act, component 1). Vanilla Lean 4 (v4.29.1
  pinned), no imports; expected profile per terminal: "does not depend on any axioms".

  THE ENDPOINT, here: the banked sector dimensions at all eight cells satisfy 4·d_i = (q−1)² + 3 and 4·d = (q−1)² − 1
  at p = 2 and 4·d = (q−1)² at odd q, decided as numeral identities; the derivation of these from the center's phase
  data (the character-average law as a fixed-point theorem) is in the bank, relay data/b67_congruence.txt, not here. THE SWAPPED PAIR (q/2, 0) ↔
  (0, q/2) is a σ-2-cycle inside the σ²-fixed square — it feeds Π's sum and not M's:
  the involution's geometry separated from the rotation's. Bank: relay data/b67_congruence.txt.
-/

namespace LefschetzShadow

/-- the σ²-fixed grid points at size q -/
def piFixed (q : Nat) : List (Nat × Nat) :=
  ((List.range q).map (fun a => (List.range q).map (fun t => (a, t)))).flatten.filter
    (fun v => ((q - v.1) % q, (q - v.2) % q) = v)

/-- σ applied once -/
def sig (q : Nat) (v : Nat × Nat) : Nat × Nat := ((q - v.2) % q, v.1)

/-- THE Π-LOCUS AND THE SWAPPED PAIR, decided at instances: the origin alone at q = 3, 5, 9; the 2-torsion square at q =
2, 4, 8; and (q/2, 0) ↔ (0, q/2) is a σ-2-cycle at q = 4, 8 — σ²-fixed, not σ-fixed. -/
theorem pi_locus_and_pair :
    (piFixed 3 = [(0,0)] ∧ piFixed 5 = [(0,0)] ∧ piFixed 9 = [(0,0)]) ∧
    (piFixed 2 = [(0,0),(0,1),(1,0),(1,1)] ∧
     piFixed 4 = [(0,0),(0,2),(2,0),(2,2)] ∧
     piFixed 8 = [(0,0),(0,4),(4,0),(4,4)]) ∧
    (sig 4 (2,0) = (0,2) ∧ sig 4 (0,2) = (2,0) ∧ sig 4 (2,0) ≠ (2,0) ∧
     sig 8 (4,0) = (0,4) ∧ sig 8 (0,4) = (4,0) ∧ sig 8 (4,0) ≠ (4,0)) := by decide

/-- a monomial c·ζ₁₆^e reduced in ℤ[x]/(x⁸+1) -/
def mono (c : Int) (e : Nat) : List Int :=
  let r := e % 8
  let s : Int := if (e / 8) % 2 = 0 then c else -c
  (List.range 8).map (fun k => if k = r then s else 0)

/-- THE Π-PHASES at (2,2): the center's Π-phase exponent q·(q/2) = N/2 and ζ^{N/2} reduces to −1 (decided); with the three
other 2-torsion points at phase 1 (banked), the sums are the banked traces 1 + 1 + 1 − 1 = 2 and, Sonin-restricted,
−1. -/
theorem pi_phase_instances :
    (4 * 2 = 16 / 2 ∧ mono 1 8 = [-1, 0, 0, 0, 0, 0, 0, 0]) ∧
    ((1 + 1 + 1 - 1 : Int) = 2 ∧ (0 - 1 : Int) = -1) := by decide

/-- THE BANKED DIMS AGAINST THE LAW, decided subtraction-free at all eight banked cells: 4·d_i = (q−1)² + 3 and (q−1)² =
4d + 1 at p = 2; 4·d = (q−1)² at odd q. -/
theorem dims_from_center :
    (4 * 1 = (2-1)^2 + 3 ∧ (2-1)^2 = 4 * 0 + 1) ∧
    (4 * 3 = (4-1)^2 + 3 ∧ (4-1)^2 = 4 * 2 + 1) ∧
    (4 * 13 = (8-1)^2 + 3 ∧ (8-1)^2 = 4 * 12 + 1) ∧
    (4 * 57 = (16-1)^2 + 3 ∧ (16-1)^2 = 4 * 56 + 1) ∧
    (4 * 1 = (3-1)^2 ∧ 4 * 4 = (5-1)^2 ∧ 4 * 16 = (9-1)^2 ∧ 4 * 169 = (27-1)^2) := by
  decide

/-- M³'S LOCUS AND PHASE, decided: fix(σ³) = fix(σ) at q = 4, and the center's M³-phase is the conjugate (i³ = −i in
pairs). -/
theorem m3_locus_phase :
    (((List.range 4).map (fun a => (List.range 4).map (fun t => (a, t)))).flatten.filter
        (fun v => sig 4 (sig 4 (sig 4 v)) = v) =
     ((List.range 4).map (fun a => (List.range 4).map (fun t => (a, t)))).flatten.filter
        (fun v => sig 4 v = v)) ∧
    ((0*0 - 1*1) * 0 - (0*1 + 1*0) * 1, (0*0 - 1*1) * 1 + (0*1 + 1*0) * 0) =
      ((0, -1) : Int × Int) := by decide

end LefschetzShadow
