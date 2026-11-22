/-
  Pair-system exclusion of agreement counts (balanced 9-variable, nonlinearity 242).

  Setting (see ../T92_CLOSED.md and ../../AGREEMENT_RANGE.md).  For a hypothetical table with
  agreement count t, let (a,b,c) count high coefficients with |H| = 1, 5, 3 and let r be the
  polar rank of the global quadratic phase.  For each of the 255 nonzero directions w the two
  complementary frequency hyperplanes carry 7-variable sections.  Record the counts (x,y,z) on
  one of them and whether its phase rank dropped to r - 2.  Both sections then satisfy the
  section facts encoded in `half`, and Parseval on
  the three frequency sets together with the count of rank-dropping hyperplanes gives the eight
  moment identities in `rhs`.

  This file proves `no_assignment`: for every t whose finite check passes (`rowCheck t a = true`
  for every a), no profile, rank and assignment of admissible splits satisfies the moment
  identities `rhs`.  The checks themselves (one kernel `decide` per value of a, so the kernel
  cache stays small) live in the `Balanced242PairCheck*.lean` files; the section facts and the
  Farkas certificates live in `Balanced242PairData.lean`.
-/
import Balanced242PairData

namespace Balanced242Pair


/-! ## Finite sums over directions -/

def fsum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => fsum n f + f n

theorem fsum_nonneg (n : Nat) (f : Nat → Int) (h : ∀ w < n, 0 ≤ f w) : 0 ≤ fsum n f := by
  induction n with
  | zero => simp [fsum]
  | succ k ih =>
    have h1 := ih (fun w hw => h w (by omega))
    have h2 := h k (by omega)
    simp only [fsum]
    omega

/-! ## Rows and the combination -/

def V8.dot (v w : V8) : Int :=
  v.c0 * w.c0 + v.c1 * w.c1 + v.c2 * w.c2 + v.c3 * w.c3 +
  v.c4 * w.c4 + v.c5 * w.c5 + v.c6 * w.c6 + v.c7 * w.c7

def vsum (n : Nat) (f : Nat → V8) : V8 :=
  ⟨fsum n (fun w => (f w).c0), fsum n (fun w => (f w).c1), fsum n (fun w => (f w).c2),
   fsum n (fun w => (f w).c3), fsum n (fun w => (f w).c4), fsum n (fun w => (f w).c5),
   fsum n (fun w => (f w).c6), fsum n (fun w => (f w).c7)⟩

theorem dot_vsum (v : V8) (n : Nat) (f : Nat → V8) :
    v.dot (vsum n f) = fsum n (fun w => v.dot (f w)) := by
  induction n with
  | zero => simp [vsum, fsum, V8.dot]
  | succ k ih =>
    simp only [vsum, fsum, V8.dot, Int.mul_add] at ih ⊢
    omega

/-- Split row for direction counts (x,y,z) of a global profile (a,b,c). -/
def row (a b c x y z : Nat) (d : Bool) : V8 :=
  let A : Int := 2 * (x : Int) - a
  let B : Int := 2 * (y : Int) - b
  let C : Int := 2 * (z : Int) - c
  ⟨1, A * A, B * B, C * C, A * B, A * C, B * C, if d then 1 else 0⟩

/-- Totals: direction count, Parseval for the three disjoint frequency sets, rank drops. -/
def rhs (a b c r : Nat) : V8 :=
  ⟨255, (a : Int) * (256 - a), (b : Int) * (256 - b), (c : Int) * (256 - c),
   -((a : Int) * b), -((a : Int) * c), -((b : Int) * c), 2 ^ r - 1⟩

theorem row_compl (a b c x y z : Nat) (d : Bool) (hx : x ≤ a) (hy : y ≤ b) (hz : z ≤ c) :
    row a b c (a - x) (b - y) (c - z) d = row a b c x y z d := by
  have e1 : 2 * ((a - x : Nat) : Int) - a = -(2 * (x : Int) - a) := by omega
  have e2 : 2 * ((b - y : Nat) : Int) - b = -(2 * (y : Int) - b) := by omega
  have e3 : 2 * ((c - z : Nat) : Int) - c = -(2 * (z : Int) - c) := by omega
  simp only [row, e1, e2, e3, Int.neg_mul_neg]

/-! ## Section facts and admissible splits -/

def testBit (s i : Nat) : Bool := (s >>> i) % 2 == 1

/-- Index of a section profile in the fact bitsets (mass determines b). -/
def factIndex (a c m : Nat) : Nat := (a * 64 + c) * 64 + m / 8

def inRange (a c m : Nat) : Bool := a < 64 && c < 64 && m / 8 < 64

/-- A section profile (a,b,c) with phase rank s is admissible.  This is the complete list
    of section facts the exclusion uses:
    * mass >= 88 and 8 | mass, at least 19 exceptional frequencies;
    * rank at most six and |T7| <= 128 * 2^(rank/2);
    * not the mass-96 profile (0,32,0);
    * not a profile without sections of any rank (`exclAll`), and, at rank six, not a
      profile without rank-six sections (`excl6`); both from exhaustive enumeration logs. -/
def half (a b c s : Nat) : Bool :=
  let m := 6 * a + 3 * b + 5 * c
  let t7 : Int := -896 + 8 * (a : Int) + 12 * b + 4 * c
  decide (88 ≤ m) && m % 8 == 0 && decide (19 ≤ a + b + c) && decide (s ≤ 6) &&
  decide (t7.natAbs ≤ 128 * 2 ^ (s / 2)) && !(m == 96 && a + c == 0) &&
  !(inRange a c m && testBit exclAll (factIndex a c m)) &&
  !(s == 6 && inRange a c m && testBit excl6 (factIndex a c m))

def secRank (r : Nat) (d : Bool) : Nat := if d then r - 2 else r

def admissible (a b c r x y z : Nat) (d : Bool) : Bool :=
  (!d || decide (2 ≤ r)) && decide (x ≤ a) && decide (y ≤ b) && decide (z ≤ c) &&
  half x y z (secRank r d) && half (a - x) (b - y) (c - z) (secRank r d)

theorem admissible_compl (a b c r x y z : Nat) (d : Bool) (hx : x ≤ a) (hy : y ≤ b) (hz : z ≤ c)
    (h : admissible a b c r x y z d = true) : admissible a b c r (a - x) (b - y) (c - z) d = true := by
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨⟨h0, -⟩, -⟩, -⟩, h4⟩, h5⟩ := h
  rw [Nat.sub_sub_self hx, Nat.sub_sub_self hy, Nat.sub_sub_self hz]
  exact ⟨⟨⟨⟨⟨h0, by omega⟩, by omega⟩, by omega⟩, h5⟩, h4⟩

/-! ## Global phase ranks permitted by the energy and phase conditions -/

def rankOK (t k r : Nat) : Bool :=
  let amp := 256 >>> (r / 2)
  let zs := [128 - amp / 2, 128 + amp / 2] ++ (if r < 8 then [128] else [])
  let q : Int := 32 * (2 * (t : Int) - 232 - k)
  zs.any (fun z0 => decide (0 < z0) && z0 != 64 && decide (1024 * t + 320 * z0 + 256 ≤ 147456)) &&
  q % (amp : Int) == 0 && decide ((q / (amp : Int)).natAbs ≤ min (2 ^ r) (256 - t))

def ranks (t k : Nat) : List Nat := [0, 2, 4, 6, 8].filter (rankOK t k)

/-! ## The finite check -/

def allBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p n && allBelow n p

theorem allBelow_spec {n : Nat} {p : Nat → Bool} (h : allBelow n p = true) : ∀ i < n, p i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ k ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact ih h.2 i hi
    · subst hi; exact h.1

/-- Every admissible split with x <= a/2 has nonnegative combination with v. -/
def splitsOK (v : V8) (t a b c r : Nat) : Bool :=
  let T := 8 * t - 480
  allBelow (a / 2 + 1) fun x =>
  allBelow ((T - 88 - 6 * x) / 5 + 1) fun z =>
  let y0 := (5 * (6 * x + 5 * z)) % 8
  allBelow ((b - y0) / 8 + 1) fun k =>
    let y := y0 + 8 * k
    [false, true].all fun d => !(admissible a b c r x y z d) || decide (0 ≤ v.dot (row a b c x y z d))

def sysCheck (v : V8) (t a b c r : Nat) : Bool :=
  decide (v.dot (rhs a b c r) < 0) && splitsOK v t a b c r

def certFor (t a c r : Nat) : V8 :=
  match (entries t).find? (fun e => e.1 == a && e.2.1 == c && e.2.2.1 == r) with
  | some e => e.2.2.2
  | none => ⟨-1, 0, 0, 0, 0, 0, 0, 0⟩

/-- All systems with a given number a of magnitude-one coefficients. -/
def rowCheck (t a : Nat) : Bool :=
  let T := 8 * t - 480
  allBelow ((T - 6 * a) / 5 + 1) fun c =>
  let rest := T - 6 * a - 5 * c
  rest % 3 != 0 || (ranks t (a + c)).all fun r => sysCheck (certFor t a c r) t a (rest / 3) c r

/-! ## No assignment survives a passing check -/

theorem half_mass {a b c s : Nat} (h : half a b c s = true) :
    88 ≤ 6 * a + 3 * b + 5 * c ∧ (6 * a + 3 * b + 5 * c) % 8 = 0 := by
  unfold half at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨h1, h2⟩

theorem admissible_parts {a b c r x y z : Nat} {d : Bool} (h : admissible a b c r x y z d = true) :
    x ≤ a ∧ y ≤ b ∧ z ≤ c ∧ half x y z (secRank r d) = true ∧
      half (a - x) (b - y) (c - z) (secRank r d) = true := by
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem split_nonneg (v : V8) (t a b c r : Nat) (hT : 6 * a + 3 * b + 5 * c = 8 * t - 480)
    (hs : splitsOK v t a b c r = true) (x y z : Nat) (d : Bool) (hx2 : x ≤ a / 2)
    (h : admissible a b c r x y z d = true) : 0 ≤ v.dot (row a b c x y z d) := by
  obtain ⟨hxa, hyb, hzc, hlo, hhi⟩ := admissible_parts h
  obtain ⟨hm1, hm2'⟩ := half_mass hlo
  obtain ⟨hM1, -⟩ := half_mass hhi
  have hz : z < (8 * t - 480 - 88 - 6 * x) / 5 + 1 := by omega
  have hy0 : y % 8 = (5 * (6 * x + 5 * z)) % 8 := by omega
  have hk : (y - (5 * (6 * x + 5 * z)) % 8) / 8 < (b - (5 * (6 * x + 5 * z)) % 8) / 8 + 1 := by omega
  have hyy : (5 * (6 * x + 5 * z)) % 8 + 8 * ((y - (5 * (6 * x + 5 * z)) % 8) / 8) = y := by omega
  have s1 := allBelow_spec hs x (by omega)
  have s2 := allBelow_spec s1 z hz
  have s3 := allBelow_spec s2 _ hk
  simp only [hyy, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq] at s3
  cases d
  · rcases s3.1 with s | s
    · rw [h] at s; exact absurd s (by decide)
    · exact s
  · rcases s3.2 with s | s
    · rw [h] at s; exact absurd s (by decide)
    · exact s

theorem no_assignment (t a b c r : Nat) (hc : ∀ a < (8 * t - 480) / 6 + 1, rowCheck t a = true)
    (hT : 6 * a + 3 * b + 5 * c = 8 * t - 480) (hr : r ∈ ranks t (a + c))
    (x y z : Nat → Nat) (drop : Nat → Bool)
    (hadm : ∀ w < 255, admissible a b c r (x w) (y w) (z w) (drop w) = true)
    (hmom : vsum 255 (fun w => row a b c (x w) (y w) (z w) (drop w)) = rhs a b c r) : False := by
  -- locate the system in the check
  have ha : a < (8 * t - 480) / 6 + 1 := by omega
  have hcc : c < (8 * t - 480 - 6 * a) / 5 + 1 := by omega
  have e1 := allBelow_spec (hc a ha) c hcc
  have hrest : (8 * t - 480 - 6 * a - 5 * c) % 3 = 0 := by omega
  have hb : (8 * t - 480 - 6 * a - 5 * c) / 3 = b := by omega
  simp only [hrest, hb, bne_self_eq_false, Bool.false_or, List.all_eq_true] at e1
  have e2 := e1 r hr
  simp only [sysCheck, Bool.and_eq_true, decide_eq_true_eq] at e2
  obtain ⟨hneg, hs⟩ := e2
  generalize hv : certFor t a c r = v at hneg hs
  -- every direction contributes a nonnegative amount
  have hw : ∀ w < 255, 0 ≤ v.dot (row a b c (x w) (y w) (z w) (drop w)) := by
    intro w hw
    have h := hadm w hw
    obtain ⟨hxa, hyb, hzc, -, -⟩ := admissible_parts h
    by_cases hx2 : x w ≤ a / 2
    · exact split_nonneg v t a b c r hT hs _ _ _ _ hx2 h
    · rw [← row_compl a b c _ _ _ _ hxa hyb hzc]
      exact split_nonneg v t a b c r hT hs _ _ _ _ (by omega)
        (admissible_compl a b c r _ _ _ _ hxa hyb hzc h)
  have hsum := fsum_nonneg 255 _ hw
  rw [← dot_vsum, hmom] at hsum
  omega

end Balanced242Pair
