/-
  THE SELECTION ATTEMPT'S DECIDED CORE · RefinementArityShadow.lean
  ================================================================

  Ferry 2026-08-25 (b158). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  b158 asked whether file E's own requirements pick a member of the apportionment
  family. One candidate class was the invariance a compiled kernel statement might
  impose — and the only kernel statement in reach is `c1`'s `proj4_sum`, which
  decomposes the space into FOUR sectors (`lam⁴ = 1`), while b38's apportionment
  splits TWO (even modes and odd). ### THE BRIDGE BETWEEN THE TWO ARITIES IS THE
  E₁/EVEN IDENTIFICATION, WHICH THE RECORD CARRIES AS A READING AND NOT AS A
  DERIVATION (b154's NAVIGATOR-OPEN X5).

  This module decides the arithmetic underneath that verdict, and nothing else:
  ### A TWO-FOLD AGGREGATE DOES NOT DETERMINE A FOUR-FOLD SPLIT. Two different
  four-sector assignments can agree on both block sums — and therefore on the
  total — so a requirement stated at the two-fold level cannot reach through to
  the four-fold one.

  · `two_fold_aggregate_does_not_determine_four_fold` — at every instance the two
    four-tuples agree on block A, agree on block B, agree on the total, ### AND
    DIFFER. The last conjunct is the negative witness and is the half that carries
    the content; without it the statement would be satisfied by taking the same
    tuple twice.
  · The instances use TWO DIFFERENT block partitions, so the fact is not an
    artifact of which sectors were paired.

  ### WITNESS DISCIPLINE, AND ITS FIRST CATCH: every instance's polarity was
  ### verified before this file was written — and the pre-check FAILED on the
  ### fourth instance, whose block sums did not in fact agree. It was repaired
  ### before any Lean existed. b154's defect became b155's procedure; this is the
  ### first time the procedure caught something.

  Scope, on its face: instances of an elementary counting fact. ### NOTHING HERE
  SAYS WHICH MEMBER OF THE APPORTIONMENT FAMILY IS RIGHT, that any member is
  right, or that the E₁/even identification is false — it says only that a
  two-fold statement does not by itself fix a four-fold one. b38's recorded
  (I-differ) verdict stands untouched. Nothing here bears on `h2`.
  Bank: relay data/b158_selection.txt.
-/

set_option maxRecDepth 16384

namespace RefinementArityShadow

/-- a four-sector assignment. -/
abbrev Four : Type := Int × Int × Int × Int

/-- the four entries as a list, so a block can be summed by index. -/
def toList : Four → List Int
  | (a, b, c, d) => [a, b, c, d]

/-- the sum of the entries whose index lies in `blk`. -/
def blockSum (t : Four) (blk : List Nat) : Int :=
  ((toList t).zipIdx.filter (fun p => blk.contains p.2)).foldl (fun s p => s + p.1) 0

/-- instances: `(q, r, blockA)` with `blockB` the complement of `blockA` in
    `{0,1,2,3}`. The first three pair sectors 0,2 against 1,3; the fourth pairs
    0,1 against 2,3, so the fact does not depend on the pairing. -/
def cases : List (Four × Four × List Nat × List Nat) :=
  [ ((5, 1, 2, 3), (4, 0, 3, 4), [0, 2], [1, 3]),
    ((-2, 7, 6, 1), (10, 3, -6, 5), [0, 2], [1, 3]),
    ((0, 0, 0, 0), (9, 4, -9, -4), [0, 2], [1, 3]),
    ((5, 1, 2, 3), (2, 4, 7, -2), [0, 1], [2, 3]) ]

/-- ### A TWO-FOLD AGGREGATE DOES NOT DETERMINE A FOUR-FOLD SPLIT, decided at every
    instance: the two assignments agree on block A, on block B, and on the total,
    ### AND THEY DIFFER. A requirement phrased at the two-fold level therefore
    cannot reach the four-fold one. -/
theorem two_fold_aggregate_does_not_determine_four_fold :
    cases.all (fun t =>
      decide (blockSum t.1 t.2.2.1 = blockSum t.2.1 t.2.2.1)
      && decide (blockSum t.1 t.2.2.2 = blockSum t.2.1 t.2.2.2)
      && decide (blockSum t.1 t.2.2.1 + blockSum t.1 t.2.2.2
                 = blockSum t.2.1 t.2.2.1 + blockSum t.2.1 t.2.2.2)
      && !decide (t.1 = t.2.1)) = true := by
  decide

end RefinementArityShadow

#print axioms RefinementArityShadow.two_fold_aggregate_does_not_determine_four_fold
