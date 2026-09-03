/-
  THE SCALING TRACE · ScalingTraceShadow.lean
  ============================================

  Ferry 2026-09-03 (b309). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  ### WHAT THIS MODULE CERTIFIES, AND -- SAID FIRST BECAUSE IT MATTERS MORE --
  ### WHAT IT DOES NOT.

  IT CERTIFIES ARITHMETIC. It does NOT certify the barrier.

  b309 computed `Tr(theta(p^k) Pi)` -- the compression of the scaling part of the
  local multiplicative group against the projection onto the object's own space --
  and found it EXACTLY ZERO at every nonzero power at seven cells, by two
  independent routes. The step from the arithmetic below to that vanishing is a
  DERIVATION, it lives in `relay/data/b309_the_scaling_trace.txt`, and IT IS NOT
  COMPILED HERE. A reader who takes these three theorems for the barrier statement
  has read them for more than they say.

  The order permitted a shadow ONLY IF the statement is finite-decidable AND
  carries its own scope in its own statement. All three below are decidable by
  finite evaluation, and each RANGES OVER AN EXPLICIT LIST NAMED IN ITS OWN
  STATEMENT -- so none of them can be read as a law about all `p`, `n`, `k`. The
  general law is the bank's derivation and is uncompiled, exactly as the finite
  two-radius family's dimension law was refused a terminal at b299 for the same
  reason: a terminal at one cell would sit in the kernel looking like the general
  statement.

  THE THREE, AND WHAT EACH IS FOR:
    (1) `frame_arithmetic` -- the composed map carries `V(n,n)` to `V(n-k, n+k)`,
        the sum of the two radii is invariant, and the smallest frame containing
        both source and target has the size the act computes in. This is the
        arithmetic that makes the trace WELL DEFINED at all; without an ambient
        there is no endomorphism and no trace.
    (2) `support_ranges_split_at_the_level` -- the object vanishes on the ball, so
        its support sits at absolute values `p^1 .. p^n` and the image's at
        `p^(1+j) .. p^(n+j)`. These MEET exactly when `j < n`. BOTH ARMS ARE
        ASSERTED: the disjoint arm alone would be a check that could not fail.
    (3) `no_offball_fixed_point_of_scaling` -- the two residue counts that the
        derivation's regime-B argument turns on are zero at every listed cell and
        power. This is the arithmetic core of the mechanism -- `p^j - 1` is a unit,
        so the scaling map fixes nothing off the ball in either congruence -- and
        it is NOT the mechanism's conclusion.

  Bank: relay `data/b309_the_scaling_trace.txt`.
  Registration: relay `data/b309_registration_2026-09-03.txt`, sealed before any
  of this existed.
-/

namespace B309

/-- The cells this act computed, as `(p, n)`: b304's six plus b295's level-3
    discriminator. NOT ONE OF THEM IS CHOSEN BY b309. -/
def cells : List (Nat × Nat) := [(2, 1), (2, 2), (3, 1), (3, 2), (5, 1), (7, 1), (2, 3)]

/-- The grid of the model frame, `p^(2n)`. -/
def gridN (p n : Nat) : Nat := p ^ (2 * n)

/-- The ball's modulus, `q = p^n`: the object vanishes exactly on the multiples. -/
def ballQ (p n : Nat) : Nat := p ^ n

/-- `(p, n, j)` for every cell and every power `1 ≤ j ≤ 2n` the act reached. -/
def cellPowers : List (Nat × Nat × Nat) :=
  cells.flatMap (fun c => (List.range (2 * c.2)).map (fun i => (c.1, c.2, i + 1)))

-- ============================================================================
-- (1) THE FRAME ARITHMETIC.
-- ============================================================================

/-- The target frame's support radius index, `n - k`, over `Int` because `k` runs
    in both directions and `n - k` leaves `Nat` at the high powers. -/
def tgtR (n k : Int) : Int := n - k

/-- The target frame's constancy radius index, `n + k`. -/
def tgtS (n k : Int) : Int := n + k

/-- The ambient's support radius index: `max n (n - k)`, written without `max` so
    the module keeps to what core `Int` decides. -/
def ambR (n k : Int) : Int := if k ≤ 0 then n - k else n

/-- The ambient's constancy radius index: `max n (n + k)`. -/
def ambS (n k : Int) : Int := if k ≤ 0 then n else n + k

/-- `(n, k)` pairs, both signs, from `cellPowers`. -/
def framePairs : List (Int × Int) :=
  cellPowers.flatMap (fun c => [((c.2.1 : Int), (c.2.2 : Int)),
                                ((c.2.1 : Int), -(c.2.2 : Int))])

/-- THE FRAME ARITHMETIC, decided over the listed `(n, k)` pairs and no others:
    the two radii of the target sum to `2n` (so the scaling part preserves the
    grid size); the ambient contains BOTH the source frame `(n,n)` and the target
    frame, each radius separately; and the ambient's own radii sum to `2n + |k|`.

    THIS IS WHY THE TRACE IS DEFINED. It says nothing about its value. -/
theorem frame_arithmetic :
    (framePairs.all (fun c =>
      let n := c.1; let k := c.2
      (tgtR n k + tgtS n k == 2 * n)
      && (ambR n k ≥ n) && (ambS n k ≥ n)
      && (ambR n k ≥ tgtR n k) && (ambS n k ≥ tgtS n k)
      && (ambR n k + ambS n k == 2 * n + (if k ≤ 0 then -k else k)))) = true := by
  decide

-- ============================================================================
-- (2) THE SUPPORT RANGES.
-- ============================================================================

/-- Do the object's support range `[1, n]` and its image's `[1+j, n+j]` meet? -/
def rangesMeet (n j : Nat) : Bool := 1 + j ≤ n

/-- THE SPLIT AT THE LEVEL, decided over the listed `(n, j)` and no others: the
    two ranges meet EXACTLY when `j < n`.

    BOTH ARMS ARE IN THE STATEMENT. A theorem asserting only that they are
    disjoint above the level would be satisfied by ranges that never meet at all,
    and the act's regime B -- where they DO meet and the trace vanishes anyway --
    would then rest on nothing checked. -/
theorem support_ranges_split_at_the_level :
    (cellPowers.all (fun c => rangesMeet c.2.1 c.2.2 == (c.2.2 < c.2.1))) = true := by
  decide

-- ============================================================================
-- (3) THE OFF-BALL FIXED-POINT COUNTS.
-- ============================================================================

/-- How many `t` off the ball does the scaling map fix modulo the whole grid? -/
def offBallFixedGrid (p n j : Nat) : Nat :=
  ((List.range (gridN p n)).filter
    (fun t => !(t % ballQ p n == 0) && ((p ^ j - 1) * t) % gridN p n == 0)).length

/-- How many `t` off the ball does it fix modulo the ball's own modulus? -/
def offBallFixedBall (p n j : Nat) : Nat :=
  ((List.range (gridN p n)).filter
    (fun t => !(t % ballQ p n == 0) && ((p ^ j - 1) * t) % ballQ p n == 0)).length

/-- THE ARITHMETIC CORE OF THE MECHANISM, decided over the listed `(p, n, j)` and
    no others: BOTH counts are zero, and `p^j - 1` is coprime to the grid and to
    the ball's modulus.

    The derivation reads this as: the scaling map has no fixed point off the ball
    in either congruence, because `p^j - 1` is a unit, and the only fixed point it
    has is the one place the object is required to vanish.

    THAT READING IS THE BANK'S AND IS NOT COMPILED. What is compiled is that the
    counts are zero at these cells and these powers. -/
theorem no_offball_fixed_point_of_scaling :
    (cellPowers.all (fun c =>
      (offBallFixedGrid c.1 c.2.1 c.2.2 == 0)
      && (offBallFixedBall c.1 c.2.1 c.2.2 == 0)
      && (Nat.gcd (c.1 ^ c.2.2 - 1) (gridN c.1 c.2.1) == 1)
      && (Nat.gcd (c.1 ^ c.2.2 - 1) (ballQ c.1 c.2.1) == 1))) = true := by
  decide

end B309

-- The three terminals, printed in the order the file states them: the frame
-- arithmetic that makes the trace well defined, the support split with BOTH its
-- arms, and the arithmetic core of the mechanism.
#print axioms B309.frame_arithmetic
#print axioms B309.support_ranges_split_at_the_level
#print axioms B309.no_offball_fixed_point_of_scaling
