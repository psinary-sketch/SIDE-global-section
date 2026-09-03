/-
  THE SMEAR'S COLLAPSE · SmearCollapseShadow.lean
  ================================================

  Ferry 2026-09-03 (b310). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  ### WHAT THIS MODULE CERTIFIES, AND -- FIRST, BECAUSE IT MATTERS MORE --
  ### WHAT IT DOES NOT.

  IT CERTIFIES ARITHMETIC. It does NOT certify the collapse.

  b310 assembled the source's construction on the local-field instrument: at a
  finite place the scaling part of the multiplicative group is the powers of the
  prime, so the source's integral is a SUM, and the compressed smear is
  `T(w) = SUM over k of w_k Tr(theta(p^k) Pi)`. Every term with `k` nonzero
  vanishes, so `T(w) = w_0 (p^n - 1)^2`: the test function read at ONE point,
  times a dimension count, with no logarithm of the prime in it and no sampling
  at the prime's powers.

  THE STEP FROM THE COUNTS BELOW TO THAT SENTENCE IS A DERIVATION. It lives in
  `relay/data/b310_the_smear_collapses.txt` and IT IS NOT COMPILED HERE. A reader
  who takes these two theorems for the collapse has read them for more than they
  say.

  The order permitted a shadow ONLY IF the statement is finite-decidable AND
  carries its own scope in its statement. Both below are decidable by finite
  evaluation, and each RANGES OVER AN EXPLICIT LIST NAMED IN ITS OWN STATEMENT --
  so neither can be read as a law about all `p`, `n`, `k`.

  THE TWO, AND WHY THE SECOND IS NOT A COPY OF b309's:
    (1) `signed_count_at_the_identity_is_the_dimension` -- at `t = 1` every
        off-ball point is fixed, and the signed count is exactly `(p^n - 1)^2`,
        the constrained dimension. Stated in integer form (multiplied through by
        the ball's modulus) so no rational arithmetic is needed.
    (2) `identity_term_survives_alone` -- BOTH ARMS IN ONE STATEMENT: the counts
        vanish at every listed nonzero power AND the identity's count does not.
        b309's terminal asserted the vanishing arm alone; that arm by itself is
        satisfied by a count that is zero everywhere, and `alone` is a claim about
        BOTH. THE SURVIVING ARM IS THE NEW CONTENT.

  Bank: relay `data/b310_the_smear_collapses.txt`.
  Registration: relay `data/b310_registration_2026-09-03.txt`, sealed before any
  of this existed.
-/

namespace B310

/-- The cells b310 computed, as `(p, n)`: b304's six plus b295's level-3
    discriminator. NOT ONE OF THEM IS CHOSEN BY b310. -/
def cells : List (Nat × Nat) := [(2, 1), (2, 2), (3, 1), (3, 2), (5, 1), (7, 1), (2, 3)]

/-- The grid of the model frame, `p^(2n)`. -/
def gridN (p n : Nat) : Nat := p ^ (2 * n)

/-- The ball's modulus, `q = p^n`: the object vanishes exactly on the multiples. -/
def ballQ (p n : Nat) : Nat := p ^ n

/-- `(p, n, j)` for every cell and every power `1 ≤ j ≤ 2n` the act carried
    from b309. -/
def cellPowers : List (Nat × Nat × Nat) :=
  cells.flatMap (fun c => (List.range (2 * c.2)).map (fun i => (c.1, c.2, i + 1)))

/-- The off-ball points that multiplication by `t` fixes modulo `m`, counted.
    Both indices must lie off the ball, which is what the projector's closed form
    requires before either term of it is nonzero. -/
def offBallFixed (p n t m : Nat) : Nat :=
  ((List.range (gridN p n)).filter
    (fun s => !(s % ballQ p n == 0)
              && !((t * s) % gridN p n % ballQ p n == 0)
              && ((t - 1) * s) % m == 0)).length

/-- THE IDENTITY'S COUNT, decided over the listed cells and no others: at `t = 1`
    the two counts coincide and the signed combination
    `A_N - (1/q) A_q` is exactly `(p^n - 1)^2`.

    Stated multiplied through by `q` so the whole statement is about naturals:
    `q * A_N - A_q = q * (p^n - 1)^2`. -/
theorem signed_count_at_the_identity_is_the_dimension :
    (cells.all (fun c =>
      let p := c.1; let n := c.2
      let q := ballQ p n
      let aN := offBallFixed p n 1 (gridN p n)
      let aQ := offBallFixed p n 1 q
      (aN == aQ) && (q * aN - aQ == q * (p ^ n - 1) * (p ^ n - 1)))) = true := by
  decide

/-- THE IDENTITY TERM SURVIVES ALONE, decided over the listed cells and powers
    and no others. BOTH ARMS ARE IN THE STATEMENT:

      the counts VANISH at every listed nonzero power -- so every term of the
      assembled smear away from the identity contributes nothing;

      and the identity's count DOES NOT vanish -- so the surviving term is not
      itself zero.

    A theorem carrying only the first arm would be satisfied by a count that is
    zero everywhere, and `alone` is a claim about both. -/
theorem identity_term_survives_alone :
    (cellPowers.all (fun c =>
      let p := c.1; let n := c.2.1; let j := c.2.2
      let q := ballQ p n
      (offBallFixed p n (p ^ j) (gridN p n) == 0)
      && (offBallFixed p n (p ^ j) q == 0)
      && !(offBallFixed p n 1 (gridN p n) == 0)
      && !(offBallFixed p n 1 q == 0))) = true := by
  decide

end B310

-- The two terminals, printed in the order the file states them.
#print axioms B310.signed_count_at_the_identity_is_the_dimension
#print axioms B310.identity_term_survives_alone
