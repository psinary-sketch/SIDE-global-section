/-
  THE APPORTIONMENT CHARACTERIZATION'S DECIDED CORE · ApportionmentShadow.lean
  ===========================================================================

  Ferry 2026-08-25 (b154). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  THE ACT ASKS A UNIQUENESS QUESTION about b38's registered apportionment:
  does every apportionment satisfying the owner-quotable requirements equal it?
  The answer is NO, and the failure has an exact shape. Two of the three steps
  behind that shape are not analysis at all — they are finite linear algebra on
  the definition itself, and THAT is what this module decides.

  b38's definition, at its owner: `w_n := tr_n_raw(n) - E2_n(n) - s_n * resid_N`
  with `resid_N := Tr_raw_N - A - E2_N` and `s_n := t(n) / Σ t(m)`. Replace the
  registered share vector `s` by an ARBITRARY share vector; rationals are cleared,
  so a share is the integer pair (q, p_n) meaning p_n/q, and every statement below
  is over ℤ and decidable.

  · `void_gate_is_exactly_normalization` — THE FIRST STEP, at decided instances:
    the void gate's residual `(total apportionment) − A`, cleared, equals
    `−resid · (Σ p − q)` EXACTLY. So the gate tests one thing and one thing only:
    whether the shares sum to one. ### It cannot see WHICH normalized share
    vector was used. The gate passing at 9e-16 is arithmetic, not canonicity.
  · `gate_verdict_both_polarities` — the same fact as a verdict, in BOTH
    polarities plus the degenerate case, because a gate that never fires decides
    nothing: normalized shares PASS; unnormalized shares with a nonzero residual
    FAIL; and when the residual VANISHES the gate passes for every share vector
    whatever, the shares being irrelevant to an apportionment that subtracts zero.
  · `sector_freedom_is_one_scalar` — THE SECOND STEP: two share vectors' sector
    shares differ by `−resid · (Σ_even p − Σ_even p′)`. The whole freedom, as it
    acts on the sector split, enters through ONE scalar — the even sector's share
    of the residual — and the second half of each instance witnesses that the
    difference is genuinely NONZERO when that scalar moves, so the freedom is not
    vacuous.
  · `within_sector_reshuffle_invisible` — its complement: share vectors that differ
    entrywise but agree on the even-sector total give the IDENTICAL sector share.
    The instances are checked to differ entrywise, so this is not vacuous either.

  Scope, on its face: these are the finite rearrangement's INSTANCES. The general
  statements are written longhand in the bank. ### NOTHING HERE DECIDES WHICH
  SHARE VECTOR IS RIGHT — the act's result is precisely that the owner-quotable
  requirements do not pin it, and no line of this module supplies what they lack.
  Nothing here bears on b38's (I-differ) verdict, on file E's identity, or on h2.
  Bank: relay data/b154_apportionment_characterization.txt.
-/

set_option maxRecDepth 16384

namespace ApportionmentShadow

abbrev Vec : Type := List Int

/-- the plain sum of a vector -/
def sumV : Vec → Int
  | [] => 0
  | x :: xs => x + sumV xs

/-- entries whose index has the given parity; `true` keeps the head. -/
def pickParity : Bool → Vec → Vec
  | _,     []      => []
  | true,  x :: xs => x :: pickParity false xs
  | false, _ :: xs => pickParity true xs

/-- entries at indices 0, 2, 4, … — the even sector (b38's E₁ sector, per its own
    reading; the reading is cited, never invented, and it is not decided here) -/
def evensOf (v : Vec) : Vec := pickParity true v

/-- `resid_N := Tr_raw_N − A − E2_N`, b38's own definition, on finite data. -/
def residOf (a b : Vec) (A : Int) : Int := sumV a - A - sumV b

/-- the TOTAL apportionment, cleared by the share denominator `q`:
    `q · Σ_n w_n` where `w_n = a_n − b_n − (p_n/q)·resid`. -/
def clearedTotal (q : Int) (a b p : Vec) (A : Int) : Int :=
  q * (sumV a - sumV b) - sumV p * residOf a b A

/-- the EVEN SECTOR's share, cleared the same way: `q · W₊`. -/
def clearedSector (q : Int) (a b p : Vec) (A : Int) : Int :=
  q * (sumV (evensOf a) - sumV (evensOf b)) - sumV (evensOf p) * residOf a b A

/-- the decided instances: `(q, A, a, b, p, p′)`, with `p` normalized (Σp = q)
    and `p′` a competitor. -/
def cases : List (Int × Int × Vec × Vec × Vec × Vec) :=
  [ (10, 2, [3, -2, 5, 1], [1, 1, -2, 0], [4, 2, 3, 1], [1, 5, 2, 4]),
    (4, -3, [2, 0, -1], [1, 2, 3], [2, 1, 1], [3, 0, 2]),
    (1000, 617, [12, -5, 8, 0, 4, 9], [2, 2, 2, 2, 2, 2],
                [200, 150, 300, 100, 150, 100], [617, 100, 83, 100, 50, 60]),
    (3, 11, [1], [4], [3], [1]),
    (7, 0, [5, 5, -5, -5], [0, 1, 0, 1], [2, 2, 2, 1], [7, 0, 0, 1]) ]

/-- the DEGENERATE instances: `resid = 0` by construction (`A = Σa − Σb`), where
    the share vector cannot matter because nothing is being apportioned. -/
def degenerateCases : List (Int × Int × Vec × Vec × Vec) :=
  [ (10, 7, [3, -2, 5, 1], [1, 1, -2, 0], [99, -5, 3, 1]),
    (6, -5, [2, 0, -1], [1, 2, 3], [0, 0, 0, 0]) ]

/-- pairs that agree on the EVEN-sector total but differ entrywise:
    `(q, A, a, b, p, p′)` with `Σ_even p = Σ_even p′` and `p ≠ p′`. -/
def reshuffleCases : List (Int × Int × Vec × Vec × Vec × Vec) :=
  [ (10, 7, [3, -2, 5, 1], [1, 1, -2, 0], [4, 2, 3, 1], [4, 6, 3, -3]),
    (4, -3, [2, 0, -1], [1, 2, 3], [2, 1, 1], [0, 3, 3]),
    (1000, 617, [12, -5, 8, 0, 4, 9], [2, 2, 2, 2, 2, 2],
                [200, 150, 300, 100, 150, 100], [300, 400, 100, 0, 250, 0]),
    (7, 0, [5, 5, -5, -5], [0, 1, 0, 1], [2, 2, 2, 1], [3, 9, 1, -8]) ]

/-- ### THE VOID GATE IS EXACTLY THE NORMALIZATION, decided at every instance:
    the gate's own residual equals `−resid·(Σp − q)`. b38 CHOSE a share vector
    that sums to one; this says the gate does not merely tolerate that choice, it
    FORCES the sum — and forces nothing else. The strongest recorded gate on the
    apportionment is silent on which normalized share vector was used. -/
theorem void_gate_is_exactly_normalization :
    cases.all (fun t =>
      decide (clearedTotal t.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.1 - t.1 * t.2.1
              = - residOf t.2.2.1 t.2.2.2.1 t.2.1 * (sumV t.2.2.2.2.1 - t.1))) = true := by
  decide

/-- THE GATE'S VERDICT IN BOTH POLARITIES, plus the degenerate case — because a
    gate that never fires decides nothing. On `cases`: the normalized vector `p`
    passes and the competitor `p′` (unnormalized, residual nonzero) FAILS. On
    `degenerateCases`: the residual is zero and an absurd share vector passes,
    which is correct and not a defect — with nothing to apportion, every share
    vector yields the same apportionment. -/
theorem gate_verdict_both_polarities :
    (cases.all (fun t =>
      decide (clearedTotal t.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.1 = t.1 * t.2.1)
      && !decide (clearedTotal t.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.2 t.2.1 = t.1 * t.2.1))
     && degenerateCases.all (fun t =>
      decide (residOf t.2.2.1 t.2.2.2.1 t.2.1 = 0)
      && decide (clearedTotal t.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 t.2.1 = t.1 * t.2.1))) = true := by
  decide

/-- ### THE SECTOR FREEDOM IS ONE SCALAR, decided: two share vectors' even-sector
    shares differ by `−resid · (Σ_even p − Σ_even p′)`. However many modes the
    vector has, the freedom reaches the sector split through a SINGLE number. The
    second conjunct witnesses that the difference is genuinely nonzero when that
    number moves — the freedom is real, not a vacuous re-description. -/
theorem sector_freedom_is_one_scalar :
    cases.all (fun t =>
      decide (clearedSector t.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.1
              - clearedSector t.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.2 t.2.1
              = - residOf t.2.2.1 t.2.2.2.1 t.2.1
                * (sumV (evensOf t.2.2.2.2.1) - sumV (evensOf t.2.2.2.2.2)))
      && (!decide (sumV (evensOf t.2.2.2.2.1) = sumV (evensOf t.2.2.2.2.2))
          && !decide (residOf t.2.2.1 t.2.2.2.1 t.2.1 = 0)
          → !decide (clearedSector t.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.1
                     = clearedSector t.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.2 t.2.1))) = true := by
  decide

/-- THE COMPLEMENT, decided: share vectors that DIFFER entrywise but agree on the
    even-sector total give the IDENTICAL sector share. The instances are checked
    to differ, so the statement is not vacuous. Together with the previous
    terminal: the apportionment's freedom is `(modes − 1)`-dimensional as a share
    vector and exactly ONE-dimensional where the sector question can see it. -/
theorem within_sector_reshuffle_invisible :
    reshuffleCases.all (fun t =>
      !decide (t.2.2.2.2.1 = t.2.2.2.2.2)
      && decide (sumV (evensOf t.2.2.2.2.1) = sumV (evensOf t.2.2.2.2.2))
      && decide (clearedSector t.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.1
                 = clearedSector t.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.2 t.2.1)) = true := by
  decide

end ApportionmentShadow

#print axioms ApportionmentShadow.void_gate_is_exactly_normalization
#print axioms ApportionmentShadow.gate_verdict_both_polarities
#print axioms ApportionmentShadow.sector_freedom_is_one_scalar
#print axioms ApportionmentShadow.within_sector_reshuffle_invisible
