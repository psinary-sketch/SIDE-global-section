/-
  THE T-JOINT'S DECIDED CORE · DoubleEntryShadow.lean
  ===================================================

  Ferry 2026-08-25 (b156). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  b154 named a one-parameter family of apportionments; b155 showed the identity's
  finite instance can SEE the parameter. THIS act asked whether b107's T-reading
  consumes an apportionment at all, and found that the apportionment-free candidate
  is not outside the family but IS a member of it — the one at share zero.

  Deriving that turned up a structural fact about b38's construction that neither
  earlier act stated, and THAT is what this module decides. b38's residual is
  `resid_N := Tr_raw_N − A − E2_N`, so ### THE CERTIFIED LEDGER COLUMN `A` IS AN
  INPUT TO THE APPORTIONED OBJECT-SIDE QUANTITY, while also standing on the ledger
  side of the closed equation. ### THE COLUMN THEREFORE ENTERS THE COMPARISON
  TWICE, AND THE TWO ENTRIES DO NOT CANCEL: they net to `(1 − share)`.

  Rationals are cleared, so a share is the integer pair `(q, p)` meaning `p/q`, and
  every statement below is over ℤ.

  · `column_enters_twice_net_q_minus_p` — perturb the ledger column by `δ` and the
    cleared closed equation moves by exactly `(q − p)·δ`, not by `q·δ`.
  · `zero_share_has_no_double_entry` — ### BOTH POLARITIES. At `p = 0` — the
    apportionment-free member, which subtracts no residual — the movement is
    exactly `q·δ`: the column enters ONCE. At `p ≠ 0` it is NOT `q·δ`, and each
    such instance carries that inequality as its negative witness.

  ### WHAT WAS CONSIDERED AND REFUSED, so the refusal is auditable: a terminal
  ### stating that the apportionment-free formula equals the family at share zero.
  ### It is an instance of b155's `share_dependence_is_exactly_R` evaluated at one
  ### share, and adding it would have been a RECOMBINATION of already-decided facts
  ### rather than new content. It is derived longhand in the bank instead.

  ### WITNESS DISCIPLINE: every instance's polarity was verified BEFORE this file
  ### was written — b154's defect, now standing procedure.

  Scope, on its face: instances of a linear rearrangement. ### NOTHING HERE SAYS
  WHICH IDENTIFICATION IS RIGHT, proposes one, or says the identity holds anywhere.
  b38's recorded (I-differ) verdict stands untouched, neither re-interpreted nor
  extended. Nothing here bears on `h2`. Bank: relay data/b156_seam_and_joint.txt.
-/

set_option maxRecDepth 16384

namespace DoubleEntryShadow

/-- one instance's tuple, taken apart by pattern rather than by a chain of
    projections -- the chain is where the first draft of this file went wrong. -/
abbrev Case : Type :=
  Int × Int × Int × Int × Int × Int × Int × Int × Int × Int

/-- the cleared closed equation. `q·D_closed`, with the apportioned object-side
    quantity written out so that the ledger column `A` appears BOTH on the ledger
    side and inside the residual the share rides. -/
def qD (q p A PR T Tr E2 E2even Thq : Int) : Int :=
  q * (A - PR) - (q * T - p * (Tr - A - E2)) - q * E2even + q * Thq

/-- instances with a NONZERO share: `(q, p, A, PR, T, Tr, E2, E2even, Thq, δ)`. -/
def nonzeroCases : List Case :=
  [ (10, 6, 5, 2, 7, 20, 3, 4, 1, 3),
    (4, 1, -3, 5, 2, -6, 1, 0, 2, -7),
    (1000, 617, 12, -5, 8, 40, 6, 9, 11, 2) ]

/-- instances at share ZERO — the apportionment-free member. -/
def zeroCases : List Case :=
  [ (10, 0, 5, 2, 7, 20, 3, 4, 1, 3),
    (7, 0, -3, 5, 2, -6, 1, 0, 2, -5) ]

/-- how far the cleared closed equation MOVES when the certified column moves by δ. -/
def moveOf : Case → Int
  | (q, p, A, PR, T, Tr, E2, E2even, Thq, d) =>
      qD q p (A + d) PR T Tr E2 E2even Thq - qD q p A PR T Tr E2 E2even Thq

/-- the share numerator of an instance. -/
def shareOf : Case → Int
  | (_, p, _, _, _, _, _, _, _, _) => p

/-- `q · δ` — what the movement would be if the column entered only ONCE. -/
def singleEntry : Case → Int
  | (q, _, _, _, _, _, _, _, _, d) => q * d

/-- `(q − p) · δ` — what it is. -/
def netEntry : Case → Int
  | (q, p, _, _, _, _, _, _, _, d) => (q - p) * d

/-- ### THE COLUMN ENTERS TWICE AND THE ENTRIES NET TO `q − p`, decided at every
    instance: moving the certified column by `δ` moves the cleared closed equation
    by `(q − p)·δ`. If the column entered only once the coefficient would be `q`. -/
theorem column_enters_twice_net_q_minus_p :
    (nonzeroCases.all (fun t => decide (moveOf t = netEntry t))
     && zeroCases.all (fun t => decide (moveOf t = netEntry t))) = true := by
  decide

/-- ### BOTH POLARITIES. At share zero the movement is exactly `q·δ` — the column
    enters ONCE and there is no double entry. At a nonzero share it is NOT `q·δ`,
    and that inequality is the negative witness the claim rests on. -/
theorem zero_share_has_no_double_entry :
    (zeroCases.all (fun t =>
      decide (shareOf t = 0) && decide (moveOf t = singleEntry t))
     && nonzeroCases.all (fun t =>
      !decide (shareOf t = 0) && !decide (moveOf t = singleEntry t))) = true := by
  decide

end DoubleEntryShadow

#print axioms DoubleEntryShadow.column_enters_twice_net_q_minus_p
#print axioms DoubleEntryShadow.zero_share_has_no_double_entry
