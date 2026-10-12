/-
  THE THETA CONTINUATION'S DECIDED CORE · ThetaContinuationShadow.lean
  =====================================================================

  Ferry 2026-08-21 (b70). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  Decided here: THE CENTER EXITS AT EVERY BANKED PLACE-2 LEVEL (q = 4, 8, 16), with the (2,2) exit-set exactly the
  center; the ARITHMETIC of the non-stabilization witness only (1 + (−1) = 0 in ℤ[i] pairs, and the cited row-4 value
  2 is nonzero; the level scalings and the non-stabilization itself are b70's derivation and row 46's instance, not
  computed here); THE FINITE ORIENTATION BREAK (tr S = 4(1+i) and tr S* = 4(1−i) at (2,2) are distinct).
  Bank: relay data/b70_theta_continuation.txt.
-/

namespace ThetaContinuationShadow

/-- THE CENTER EXITS, decided per level: every V-image position 2·(q/2 + q·b) is a
    ball position (≡ 0 mod q) at q = 4, 8, 16; the (2,2) exit family is EXACTLY the
    center (the only even frequency at q = 4); the deeper families counted as data -/
theorem center_exit_instances :
    ((List.range 4).map (fun b => (2 * (4/2 + 4*b)) % 16 % 4) =
      (List.range 4).map (fun _ => 0)) ∧
    ((List.range 8).map (fun b => (2 * (8/2 + 8*b)) % 64 % 8) =
      (List.range 8).map (fun _ => 0)) ∧
    ((List.range 16).map (fun b => (2 * (16/2 + 16*b)) % 256 % 16) =
      (List.range 16).map (fun _ => 0)) ∧
    ((List.range 4).filter (fun t => decide (t ≠ 0) && decide (t % 2 = 0)) = [2]) ∧
    ((List.range 8).filter (fun t => decide (t ≠ 0) && decide (t % 2 = 0)) = [2, 4, 6]) := by
  decide

/-- ℤ[i] pairs for the level-1 computation -/
def padd (u v : Int × Int) : Int × Int := (u.1 + v.1, u.2 + v.2)

/-- THE NON-STABILIZATION WITNESS's arithmetic, decided: the coefficients 1 and ζ₄² = −1 (entered as literals) cancel, 1 +
(−1) = 0 in ℤ[i] pairs, and the cited row-4 value 2 is nonzero; the scalings at (2,1) and (2,2) are not computed here
(row 46, cited), and that the level family {V_n} does not stabilize on colimit classes is the b70 derivation. -/
theorem non_stabilization_witness :
    (padd (1, 0) (-1, 0) = (0, 0)) ∧
    (([2, 0, 0, 0, 0, 0, 0, 0] : List Int) ≠ [0, 0, 0, 0, 0, 0, 0, 0]) := by decide

/-- a monomial c·ζ₁₆^e reduced in ℤ[x]/(x⁸+1) -/
def mono (c : Int) (e : Nat) : List Int :=
  let r := e % 8
  let s : Int := if (e / 8) % 2 = 0 then c else -c
  (List.range 8).map (fun k => if k = r then s else 0)

def vadd (u v : List Int) : List Int := List.zipWith (· + ·) u v

def vsum (l : List (List Int)) : List Int :=
  l.foldl vadd [0, 0, 0, 0, 0, 0, 0, 0]

/-- THE FINITE ORIENTATION BREAK, decided: tr S = Σζ^{m²} = 4(1 + i) and
    tr S* = Σζ^{−m²} = 4(1 − i) at (2,2) — distinct: the finite kernel convention
    breaks the conjugation symmetry the recorded archimedean ground cannot break -/
theorem orientation_break :
    vsum ((List.range 16).map (fun m => mono 1 ((m * m) % 16))) =
      [4, 0, 0, 0, 4, 0, 0, 0] ∧
    vsum ((List.range 16).map (fun m => mono 1 ((16 - (m * m) % 16) % 16))) =
      [4, 0, 0, 0, -4, 0, 0, 0] ∧
    ([4, 0, 0, 0, 4, 0, 0, 0] : List Int) ≠ [4, 0, 0, 0, -4, 0, 0, 0] := by decide

end ThetaContinuationShadow
