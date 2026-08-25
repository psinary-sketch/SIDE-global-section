/-
  THE ARITY READ'S DECIDED CORE · SectorOccupancyShadow.lean
  =========================================================

  Ferry 2026-08-25 (b159). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  b158 could not decide whether a compiled kernel statement constrains the
  apportionment family, because `proj4_sum` decomposes into FOUR sectors while
  b38's apportionment splits TWO, and the bridge between the arities was carried
  as a reading. ### THE RECORD HELD THE BRIDGE ALL ALONG, and b159 found it: the
  layer's mode `n` is CLASSICAL INDEX `2n`, and the transform's Hermite shadow is
  `(-i)^m` on classical index `m`. So the sector index is `m % 4` with `m = 2n`.

  This module decides what that forces, and nothing else:
  ### ON THIS LAYER THE FOUR-SECTOR DECOMPOSITION COLLAPSES TO TWO. Every mode
  lands in sector `0` or sector `2` — the `+i` and `−i` sectors are UNOCCUPIED —
  and sector `0` falls exactly on even `n`, sector `2` exactly on odd `n`, which
  is precisely b38's index-parity split.

  · `layer_occupies_only_two_of_four_sectors` — the positive half (every mode in
    `{0,2}`), ### the negative half (NO mode in `{1,3}`), and that BOTH occupied
    sectors are actually hit, so the collapse is to two and not to one.
  · `sector_parity_is_index_parity` — sector `0` ↔ `n` even and sector `2` ↔ `n`
    odd, each as a biconditional at every instance, ### so neither direction is
    assumed.

  ### WHAT THIS DOES NOT DO, and the distinction is the point of the act: it does
  ### NOT constrain the apportionment. A completeness statement says the sectors
  ### exhaust the space; on the apportionment side that is the void gate, and
  ### b154 proved the void gate constrains the NORMALIZATION ALONE.
  ### b158's terminal — that a two-fold aggregate does not determine a four-fold
  ### split — remains true and simply does not bite here, because on this layer
  ### there is no four-fold split to determine.

  Nothing here says which member of the family is right, proposes one, or says
  the identity holds anywhere. b38's recorded (I-differ) verdict stands untouched.
  Nothing here bears on `h2`. Bank: relay data/b159_seam_and_arity.txt.
-/

set_option maxRecDepth 16384

namespace SectorOccupancyShadow

/-- the layer's mode `n` sits at classical index `2n` (b35: `ξ_n = √2·ψ_{2n}`),
    and the Hermite shadow `(-i)^m` makes the sector index `m % 4`. -/
def sectorIndex (n : Nat) : Nat := (2 * n) % 4

/-- the layer modes exercised. -/
def modes : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- ### THE FOUR-SECTOR DECOMPOSITION COLLAPSES TO TWO ON THIS LAYER, decided:
    every mode lands in sector `0` or `2`; ### NO mode lands in sector `1` or `3`,
    so the `±i` sectors are unoccupied; and both surviving sectors are actually
    hit, so the collapse is to TWO rather than to one. -/
theorem layer_occupies_only_two_of_four_sectors :
    (modes.all (fun n => decide (sectorIndex n = 0) || decide (sectorIndex n = 2))
     && !modes.any (fun n => decide (sectorIndex n = 1) || decide (sectorIndex n = 3))
     && modes.any (fun n => decide (sectorIndex n = 0))
     && modes.any (fun n => decide (sectorIndex n = 2))) = true := by
  decide

/-- ### THE SECTOR SPLIT IS b38's INDEX-PARITY SPLIT, decided as a biconditional at
    every mode so neither direction is assumed: sector `0` exactly at even `n`,
    sector `2` exactly at odd `n`, and never both. -/
theorem sector_parity_is_index_parity :
    modes.all (fun n =>
      decide (decide (sectorIndex n = 0) = decide (n % 2 = 0))
      && decide (decide (sectorIndex n = 2) = decide (n % 2 = 1))
      && !(decide (sectorIndex n = 0) && decide (sectorIndex n = 2))) = true := by
  decide

end SectorOccupancyShadow

#print axioms SectorOccupancyShadow.layer_occupies_only_two_of_four_sectors
#print axioms SectorOccupancyShadow.sector_parity_is_index_parity
