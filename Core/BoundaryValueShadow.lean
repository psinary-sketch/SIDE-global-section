/-
  b298 · BoundaryValueShadow.lean — THE VANILLA LEG (zero axioms)
  ===============================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES, AND — far more importantly — WHAT IT DOES NOT.

  IT COMPILES ONE EXISTENCE FACT, BANKED AT b295 AND RE-DERIVED AT b296:

      AT THE CELL (p,n) = (2,2), THE MEMBER `Son(2,2; -1, 0)` CONTAINS A VECTOR
      WHOSE FIRST-LEVEL VALUE IS `4/3`, AND THAT VECTOR IS NOT IN `Son(2,2)` ITSELF.

  THE MEMBER'S RADII AND THE CELL APPEAR IN THE STATEMENT ITSELF, NOT IN THIS COMMENT.
  That is the whole reason this candidate was built and the other four in b297's kernel
  plan were refused. b294 refused a terminal reading "the first-level value is -1"
  because it would sit in the kernel beside the barrier's terminals WITH NO ROOM TO
  CARRY THE SENTENCE THAT THE VECTOR IS NOT A `Son` VECTOR. A terminal that NAMES THE
  MEMBER carries that sentence inherently: `inMember 2 2 (-1) 0` says the function-side
  radius is one step BELOW the object's own, and `inMember 2 2 0 0 w = false` — decided
  in this file, beside the value — says the object's own space REJECTS this vector.

  WHAT IS NOT COMPILED HERE, AND MUST NOT BE READ INTO IT:

    · THE CRITERION. b295's `a >= 0 or b >= n-1` and b296's equivalence quantify over
      ALL levels and ALL places. They are NOT finite and nothing here certifies them.
      THIS FILE IS ABOUT ONE CELL AND SAYS SO IN EVERY STATEMENT.
    · THE FAMILY'S DIMENSION LAW, and THE DIAGONAL IDENTIFICATION (b293) — both are
      finite-decidable at a cell and both were REFUSED at b297, because a terminal
      certifying either at one cell reads as the general law.
    · THE TRANSFORM-SIDE FIBER-SUM COLLAPSE at the reading scale (b296) — refused on
      the same ground.
    · ANY ROUTE, ANY AGGREGATION. M-2 is owed and stays owed.
    · ANYTHING ABOUT `h2`, which stands exactly where the deposit left it.

  THE OTHER SIDE OF THE BOUNDARY IS ALREADY IN THE KERNEL AND IS NOT REBUILT HERE:
  `B270.absorb_2_2` decides that at `(2,2)` every index lands in the ball under the
  operator, which is why a vector vanishing on the ball kills the pairing. THIS FILE
  SUPPLIES THE OTHER SIDE AT THE SAME CELL: relax the ball-vanishing by one step and
  the pairing is NOT zero. THE PAIR CERTIFIES SHARPNESS AT THAT CELL. IT DOES NOT
  CERTIFY THE EQUIVALENCE IN GENERAL, AND NEITHER TERMINAL SAYS OTHERWISE.

  THE ESCAPED-MASS ARTIFACT (b284, b293) IS A STANDING HAZARD, AND THE SHOWING THAT
  THIS STATEMENT IS NOT EXPOSED TO IT IS NOT A SENTENCE — IT IS THE MODULE'S CONTENT:
  the only index maps below are `m ↦ (p^n * m) % N`, the pairing's own pullback, and
  `m ↦ (p^(n-1-v_p m) * m) % N`, the class terminal. BOTH STAY INSIDE ONE LEVEL.
  NO LEVEL-SHIFTING MAP APPEARS. The artifact lives in b284's `g` and `h`, and neither
  is written here.

  ON THE RATIONAL VALUE, AND WHY NO DIVISION APPEARS: vanilla Lean has no rationals.
  The only denominator in the pairing is the class size, so IT IS CLEARED RATHER THAN
  APPROXIMATED — `pairTimesClass` is `|C|` times the value and is an INTEGER. The class
  size is itself a decided terminal (`class_size_2_2 : classSize 2 2 = 3`), so a reader
  reconstructs `4/3` from two decided integers. NO FLOATING POINT ANYWHERE.
-/

namespace B298

/-! ### THE MODEL. b8's `model`, as b270 uses it: modulus `N = p^(2n)`. -/

/-- `N = p^(2n)` — the modulus of the truncated cell. -/
def N (p n : Nat) : Nat := p ^ (2 * n)

/-- The `p`-adic valuation of `m`, computed by bounded descent. `vp p n 0` is `2n+1`,
    which is above every threshold this file uses — `0` lies in every ball. -/
def vpAux (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | (fuel + 1), m => if m % p == 0 then 1 + vpAux p fuel (m / p) else 0

/-- The valuation, with `0` handled separately so the descent always terminates. -/
def vp (p n m : Nat) : Nat := if m == 0 then 2 * n + 1 else vpAux p (2 * n + 1) m

/-- The ball of exponent `e`: `{ m : v_p(m) ≥ n - e }`. The radius `e` is an INTEGER,
    which is what lets a member sit one step BELOW the object's own ball. -/
def inBallExp (p n : Nat) (e : Int) (m : Nat) : Bool :=
  (Int.ofNat (vp p n m)) ≥ (Int.ofNat n) - e

/-- The corpus's own ball — the exponent-`0` case. -/
def inBall (p n m : Nat) : Bool := inBallExp p n 0 m

/-! ### THE MEMBER. `Son(p,n; a,b)`, b293's two-radius family, at its own definition. -/

/-- Condition one: `f` vanishes on the ball of exponent `a`. -/
def cond1 (p n : Nat) (a : Int) (f : Nat → Int) : Bool :=
  (List.range (N p n)).all (fun m => !(inBallExp p n a m) || (f m == 0))

/-- Condition two, COLLAPSED exactly as b293 derived it: the transform-side condition
    at exponent `b` says every fiber sum of the reduction `Z/p^(2n) → Z/p^(n+b)`
    vanishes. THE COLLAPSE IS b293's DERIVATION AND IS NOT RE-DERIVED HERE. -/
def cond2 (p n : Nat) (b : Int) (f : Nat → Int) : Bool :=
  let M := p ^ ((Int.ofNat n) + b).toNat
  (List.range M).all (fun r =>
    ((List.range (N p n)).foldl (fun s m => if m % M == r then s + f m else s) 0) == 0)

/-- Membership in `Son(p,n; a,b)`, by BOTH of the member's conditions. -/
def inMember (p n : Nat) (a b : Int) (f : Nat → Int) : Bool :=
  cond1 p n a f && cond2 p n b f

/-! ### THE OPERATOR. b281's `A` at `k = n`, through `S_quot`'s classes. -/

/-- The terminal of `m` under `x ~ px` restricted off the ball: the class of `m` is the
    set of off-ball indices sharing this value. -/
def terminalIdx (p n m : Nat) : Nat := (p ^ (n - 1 - vp p n m) * m) % N p n

/-- `S_quot`'s class of `m` — off-ball indices with the same terminal. -/
def classOf (p n m : Nat) : List Nat :=
  (List.range (N p n)).filter
    (fun x => !(inBall p n x) && terminalIdx p n x == terminalIdx p n m)

/-- The class size — the ONLY denominator the pairing carries. -/
def classSize (p n : Nat) : Nat := (classOf p n 1).length

/-- `|C|` times `(S_quot f)(m)`: the class sum off the ball, and `0` on it. -/
def classSum (p n : Nat) (f : Nat → Int) (m : Nat) : Int :=
  if inBall p n m then 0 else (classOf p n m).foldl (fun s x => s + f x) 0

/-- `|C| · ⟨A f, f⟩`, AN INTEGER. The pairing is `Σ_m (S_quot f)(m) · f(p^n m mod N)`,
    and multiplying by the class size clears its only denominator.
    THE MAP `m ↦ (p^n * m) % N` IS THE PAIRING'S OWN PULLBACK AND STAYS INSIDE ONE
    LEVEL — no level-shifting map appears in this file. -/
def pairTimesClass (p n : Nat) (f : Nat → Int) : Int :=
  (List.range (N p n)).foldl
    (fun s m => s + classSum p n f m * f ((p ^ n * m) % N p n)) 0

/-- Every off-ball class has the same size — checked, not assumed. -/
def classesUniform (p n : Nat) : Bool :=
  (List.range (N p n)).all
    (fun m => inBall p n m || ((classOf p n m).length == classSize p n))

/-! ### THE VECTORS. -/

/-- The witness banked at b295: `w = e_2 - e_6 + e_4 - e_12`. -/
def w : Nat → Int := fun m =>
  if m == 2 then 1 else if m == 4 then 1 else
  if m == 6 then -1 else if m == 12 then -1 else 0

/-- b271's not-dead witness `g_0`, in b294's own normalisation. -/
def g0 (p n : Nat) : Nat → Int := fun m =>
  if m == 0 then 2 + 2 * Int.ofNat (p ^ n) else 2

/-! ### b296's GENERAL CONSTRUCTION, ONLY SO ITS DEGENERACY CAN BE DECIDED. -/

/-- The four points of b296's witness construction. -/
def ctorPts (p n : Nat) : List Nat :=
  [p ^ (n - 1), (p ^ (n - 1) + p ^ (2 * n - 2)) % N p n,
   p ^ n, (p ^ n + p ^ (2 * n - 1)) % N p n]

def allDistinct : List Nat → Bool
  | [] => true
  | (x :: xs) => !(xs.contains x) && allDistinct xs

def ctorDistinct (p n : Nat) : Bool := allDistinct (ctorPts p n)

/-! ### (0) THE DEFINITIONS AGREE WITH b270's, AT THE CELL THIS FILE IS ABOUT.

    This file reaches the ball through an INTEGER radius; b270 reaches it through
    `m % p^n == 0`. IF THOSE TWO DISAGREED, THE PAIR AT COMPONENT 2 WOULD BE TWO
    STATEMENTS ABOUT TWO DIFFERENT BALLS. They are decided equal here. -/

theorem ball_agrees_with_b270_2_2 :
    (List.range (N 2 2)).all (fun m => inBall 2 2 m == (m % (2 ^ 2) == 0)) = true := by decide

/-! ### (1) THE POLARITY CONTROLS, FIRST — before any value is read.

    A positive terminal with no refusal beside it is a terminal nobody has shown can
    fail. Each of these is decided FALSE. -/

/-- THE SCOPE CONTROL, AND THE REASON THIS FILE IS ALLOWED TO EXIST:
    THE OBJECT'S OWN SPACE REJECTS THE WITNESS. `Son(2,2)` is the member with radii
    `(0,0)`, and `w` IS NOT IN IT. -/
theorem witness_not_in_object_2_2 : inMember 2 2 0 0 w = false := by decide

/-- And the reason it is rejected, decided rather than asserted: the witness has mass
    ON the ball, which the object's first condition forbids outright. -/
theorem witness_has_mass_on_ball_2_2 : (inBall 2 2 4 && !(w 4 == 0)) = true := by decide

/-- The witness leaves the member at `b = n - 1 = 1` — b296's own negative control,
    decided here. THE CONSTRUCTION STOPS EXACTLY AT THE THRESHOLD. -/
theorem witness_leaves_member_at_b_eq_1_2_2 : inMember 2 2 (-1) 1 w = false := by decide

/-- The value is not some other integer. -/
theorem refuse_value_five_2_2 : (pairTimesClass 2 2 w == 5) = false := by decide

/-! ### (2) THE NOT-DEAD WITNESS. A nonzero from a dead instrument is not a nonzero,
    so the SAME definitions are shown to reproduce b271's banked value first. -/

theorem not_dead_2_2 : pairTimesClass 2 2 (g0 2 2) = 144 := by decide

/-- And it is b271's banked `4(N - q)`, times the class size — not a coincidence of
    magnitude but the banked quantity itself. -/
theorem not_dead_matches_banked_2_2 :
    pairTimesClass 2 2 (g0 2 2)
      = Int.ofNat (classSize 2 2) * (4 * (Int.ofNat (N 2 2) - Int.ofNat (2 ^ 2))) := by decide

/-! ### (3) THE CLASSES — the denominator, decided. -/

theorem class_size_2_2 : classSize 2 2 = 3 := by decide

theorem classes_uniform_2_2 : classesUniform 2 2 = true := by decide

/-! ### (4) THE BOUNDARY TERMINAL.

    THE MEMBER'S RADII `(-1, 0)` AND THE CELL `(2,2)` ARE IN THE STATEMENT.
    So is the object's own rejection of the witness. A reader who sees ONLY this
    terminal reads: at cell (2,2), on the member whose function-side radius is one
    step below the object's own, there is a vector of value `4 / 3` — AND THE OBJECT'S
    OWN SPACE DOES NOT CONTAIN IT. -/
theorem boundary_value_at_cell_2_2_on_member_radii_neg1_0 :
    inMember 2 2 (-1) 0 w = true
    ∧ inMember 2 2 0 0 w = false
    ∧ classSize 2 2 = 3
    ∧ pairTimesClass 2 2 w = 4 := by decide

/-! ### (5) THE UNAVAILABLE ARM. An arm that cannot exist reports UNAVAILABLE, never
    a pass (the b280 convention). b296's general construction COLLIDES at `(2,1)`, so
    NO ANALOGOUS TERMINAL IS OFFERED THERE — and that is decided, not commented. -/

theorem ctor_distinct_2_2 : ctorDistinct 2 2 = true := by decide

theorem ctor_degenerate_2_1 : ctorDistinct 2 1 = false := by decide

/-! ### THE AXIOM PROFILE, PRINTED BY THIS FILE ITSELF.

    b227's standard: a claimed compile is reported ONLY from its printed profile.
    These prints live in the banked file so the profile is produced by compiling the
    artefact that was banked — not by compiling a copy of it. -/

#print axioms B298.ball_agrees_with_b270_2_2
#print axioms B298.witness_not_in_object_2_2
#print axioms B298.witness_has_mass_on_ball_2_2
#print axioms B298.witness_leaves_member_at_b_eq_1_2_2
#print axioms B298.refuse_value_five_2_2
#print axioms B298.not_dead_2_2
#print axioms B298.not_dead_matches_banked_2_2
#print axioms B298.class_size_2_2
#print axioms B298.classes_uniform_2_2
#print axioms B298.boundary_value_at_cell_2_2_on_member_radii_neg1_0
#print axioms B298.ctor_distinct_2_2
#print axioms B298.ctor_degenerate_2_1

end B298
