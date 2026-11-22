/-
  From a pair of halves to the pair system.

  For halves f, g with high block `hi f g` (all values 4 mod 8, magnitude at most 28) this file
  derives, inside Lean:
  * the profile identity 6a + 3b + 5c = 8t - 480, where a, b, c count high coefficients of
    magnitude 4, 20, 12 (|H| = 1, 5, 3) and t is the number of agreeing input pairs;
  * the seven Parseval moment identities of the pair system, with the split counts defined as
    the numbers of A, B, C frequencies on each frequency hyperplane `w . a = 0`.

  What remains a hypothesis is stated explicitly in `no_242_from_halves`:
  * `hrank`: the global phase rank r passes the phase test `ranks`;
  * `hdrop`: exactly 2^r - 1 directions drop the section rank;
  * `hsec`: for every direction both sections satisfy the section facts (`admissible`).
-/
import Balanced242Support
import Balanced242Pair

namespace Balanced242Reduction
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support
open Balanced242Pair (V8 V8.dot row rhs admissible ranks rowCheck sysCheck certFor allBelow_spec
  split_nonneg admissible_parts admissible_compl row_compl)

/-! ## Indicators, counts and hyperplane counts -/

def ind (P : W n → Bool) (a : W n) : Int := if P a then 1 else 0
def cnt (P : W n → Bool) : Int := total n (ind P)
/-- Members of P on the frequency hyperplane `w . a = 0`. -/
def low (P : W n → Bool) (w : W n) : Int := total n (fun a => if P a && !dot n w a then 1 else 0)
/-- Mask removing the zero direction. -/
def nz (w : W n) : Int := if w = zero n then 0 else 1

theorem total_nonneg (F : W n → Int) (h : ∀ w, 0 ≤ F w) : 0 ≤ total n F := by
  have := total_mono n (fun _ => (0 : Int)) F h
  rwa [total_zero] at this

theorem cnt_nonneg (P : W n → Bool) : 0 ≤ cnt P :=
  total_nonneg _ (fun a => by unfold ind; split <;> omega)

theorem low_nonneg (P : W n → Bool) (w : W n) : 0 ≤ low P w :=
  total_nonneg _ (fun a => by split <;> omega)

theorem low_spec (P : W n → Bool) (w : W n) : 2 * low P w - cnt P = transform (ind P) w := by
  unfold low cnt transform
  rw [← total_scale, ← total_sub]
  apply congrArg (total n); funext a
  simp only [ind, chr]
  cases P a <;> cases dot n w a <;> simp [sign]

theorem transform_ind_zero (P : W n → Bool) : transform (ind P) (zero n) = cnt P := by
  unfold transform cnt; apply congrArg (total n); funext a; simp [chr, dot_zero, sign]

theorem nz_total (F : W n → Int) : total n (fun w => nz w * F w) = total n F - F (zero n) := by
  have h := select n (zero n) F
  conv => rhs; rw [← h]
  rw [← total_sub]; apply congrArg (total n); funext w
  by_cases hw : w = zero n
  · subst hw; simp [nz, hits]
  · have hw' : ¬ zero n = w := fun e => hw e.symm
    simp [nz, hits, hw, hw']

/-- Polarized Parseval. -/
theorem parseval2 (u v : W n → Int) :
    total n (fun a => transform u a * transform v a) = many n * total n (fun x => u x * v x) := by
  unfold transform
  simp only [rectangular]
  rw [swap]
  have inner (x : W n) :
      total n (fun a => total n (fun y => (u x * chr a x) * (v y * chr a y))) =
        many n * (u x * v x) := by
    rw [swap]
    have fact (a y : W n) : (u x * chr a x) * (v y * chr a y) =
        (u x * v y) * (chr a x * chr a y) := by ac_rfl
    simp only [fact, total_scale, orthogonal]
    have rearr (y : W n) : (u x * v y) * (many n * hits x y) =
        (many n * u x) * (hits x y * v y) := by ac_rfl
    simp only [rearr, total_scale, select, Int.mul_assoc]
  exact (congrArg (total n) (funext inner)).trans (total_scale ..)

/-- Second moments of the hyperplane splits over the nonzero directions. -/
theorem moment_self (P : W n → Bool) :
    total n (fun w => nz w * (transform (ind P) w * transform (ind P) w)) =
      many n * cnt P - cnt P * cnt P := by
  rw [nz_total, parseval2, transform_ind_zero]
  congr 2; unfold cnt; apply congrArg (total n); funext a; unfold ind; split <;> simp

theorem moment_cross (P Q : W n → Bool) (disj : ∀ a, (P a && Q a) = false) :
    total n (fun w => nz w * (transform (ind P) w * transform (ind Q) w)) = - (cnt P * cnt Q) := by
  rw [nz_total, parseval2, transform_ind_zero, transform_ind_zero]
  have : total n (fun x => ind P x * ind Q x) = 0 := by
    rw [← total_zero n]; apply congrArg (total n); funext a
    have d := disj a; unfold ind
    cases hp : P a <;> cases hq : Q a <;> simp_all
  rw [this]; omega

theorem moment_self' (P : W n → Bool) :
    total n (fun w => transform (ind P) w * (nz w * transform (ind P) w)) =
      many n * cnt P - cnt P * cnt P := by
  rw [← moment_self]; apply congrArg (total n); funext w; ac_rfl

theorem moment_cross' (P Q : W n → Bool) (disj : ∀ a, (P a && Q a) = false) :
    total n (fun w => transform (ind P) w * (nz w * transform (ind Q) w)) = - (cnt P * cnt Q) := by
  rw [← moment_cross P Q disj]; apply congrArg (total n); funext w; ac_rfl

theorem nz_count : total n (fun w : W n => nz w * 1) = many n - 1 := by
  rw [nz_total, total_const]; simp

/-! ## The three frequency classes of the high block -/

def clsA (f g : Half) (a : W 8) : Bool := (hi f g a).natAbs == 4
def clsC (f g : Half) (a : W 8) : Bool := (hi f g a).natAbs == 12
def clsB (f g : Half) (a : W 8) : Bool := (hi f g a).natAbs == 20

theorem hi_values (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)
    (a : W 8) : hi f g a = -28 ∨ hi f g a = -20 ∨ hi f g a = -12 ∨ hi f g a = -4 ∨
      hi f g a = 4 ∨ hi f g a = 12 ∨ hi f g a = 20 ∨ hi f g a = 28 := by
  have h1 := res a; have h2 := cap a; omega

theorem energy_point (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)
    (a : W 8) : hi f g a * hi f g a =
      784 - 128 * (6 * ind (clsA f g) a + 3 * ind (clsB f g) a + 5 * ind (clsC f g) a) := by
  unfold ind clsA clsB clsC
  rcases hi_values f g res cap a with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

/-- High energy identity: 6a + 3b + 5c = 8t - 480. -/
theorem profile_mass (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28) :
    6 * cnt (clsA f g) + 3 * cnt (clsB f g) + 5 * cnt (clsC f g) = 8 * agreements f g - 480 := by
  have e := diffEnergy f g
  simp only [energy_point f g res cap] at e
  simp only [Int.mul_add, total_sub, total_const, total_add, total_scale] at e
  unfold cnt agreements
  rw [show many 8 = 256 from rfl] at e
  omega

theorem disjAB (f g : Half) (a : W 8) : (clsA f g a && clsB f g a) = false := by
  unfold clsA clsB; cases h : (hi f g a).natAbs == 4 <;> simp_all
theorem disjAC (f g : Half) (a : W 8) : (clsA f g a && clsC f g a) = false := by
  unfold clsA clsC; cases h : (hi f g a).natAbs == 4 <;> simp_all
theorem disjBC (f g : Half) (a : W 8) : (clsB f g a && clsC f g a) = false := by
  unfold clsB clsC; cases h : (hi f g a).natAbs == 20 <;> simp_all

/-! ## Profile, splits, and the end-to-end statement -/

def pa (f g : Half) : Nat := (cnt (clsA f g)).toNat
def pb (f g : Half) : Nat := (cnt (clsB f g)).toNat
def pc (f g : Half) : Nat := (cnt (clsC f g)).toNat
def sx (f g : Half) (w : W 8) : Nat := (low (clsA f g) w).toNat
def sy (f g : Half) (w : W 8) : Nat := (low (clsB f g) w).toNat
def sz (f g : Half) (w : W 8) : Nat := (low (clsC f g) w).toNat

theorem toNat_cast {z : Int} (h : 0 ≤ z) : ((z.toNat : Nat) : Int) = z := Int.toNat_of_nonneg h

/-- The row of a direction in terms of the Walsh spectra of the three classes. -/
theorem row_dot (v : V8) (f g : Half) (w : W 8) (d : Bool) :
    v.dot (row (pa f g) (pb f g) (pc f g) (sx f g w) (sy f g w) (sz f g w) d) =
      v.c0 * 1
      + v.c1 * (transform (ind (clsA f g)) w * transform (ind (clsA f g)) w)
      + v.c2 * (transform (ind (clsB f g)) w * transform (ind (clsB f g)) w)
      + v.c3 * (transform (ind (clsC f g)) w * transform (ind (clsC f g)) w)
      + v.c4 * (transform (ind (clsA f g)) w * transform (ind (clsB f g)) w)
      + v.c5 * (transform (ind (clsA f g)) w * transform (ind (clsC f g)) w)
      + v.c6 * (transform (ind (clsB f g)) w * transform (ind (clsC f g)) w)
      + v.c7 * (if d then 1 else 0) := by
  have eA : 2 * ((sx f g w : Nat) : Int) - ((pa f g : Nat) : Int) = transform (ind (clsA f g)) w := by
    unfold sx pa; rw [toNat_cast (low_nonneg _ _), toNat_cast (cnt_nonneg _)]; exact low_spec _ _
  have eB : 2 * ((sy f g w : Nat) : Int) - ((pb f g : Nat) : Int) = transform (ind (clsB f g)) w := by
    unfold sy pb; rw [toNat_cast (low_nonneg _ _), toNat_cast (cnt_nonneg _)]; exact low_spec _ _
  have eC : 2 * ((sz f g w : Nat) : Int) - ((pc f g : Nat) : Int) = transform (ind (clsC f g)) w := by
    unfold sz pc; rw [toNat_cast (low_nonneg _ _), toNat_cast (cnt_nonneg _)]; exact low_spec _ _
  simp only [V8.dot, row, eA, eB, eC]

/-- Sum of the rows over the nonzero directions equals the pair-system right-hand side, given
    the rank-drop count. -/
theorem rows_sum (v : V8) (f g : Half) (r : Nat) (drop : W 8 → Bool)
    (hdrop : total 8 (fun w => nz w * (if drop w then 1 else 0)) = 2 ^ r - 1) :
    total 8 (fun w => nz w * v.dot (row (pa f g) (pb f g) (pc f g) (sx f g w) (sy f g w) (sz f g w) (drop w)))
      = v.dot (rhs (pa f g) (pb f g) (pc f g) r) := by
  simp only [row_dot, Int.mul_add]
  have comm (k X : Int) (w : W 8) : nz w * (k * X) = k * (nz w * X) := by ac_rfl
  simp only [comm, total_add, total_scale]
  rw [nz_count, moment_self', moment_self', moment_self', moment_cross' _ _ (disjAB f g),
    moment_cross' _ _ (disjAC f g), moment_cross' _ _ (disjBC f g), hdrop]
  have ca : ((pa f g : Nat) : Int) = cnt (clsA f g) := toNat_cast (cnt_nonneg _)
  have cb : ((pb f g : Nat) : Int) = cnt (clsB f g) := toNat_cast (cnt_nonneg _)
  have cc : ((pc f g : Nat) : Int) = cnt (clsC f g) := toNat_cast (cnt_nonneg _)
  have k1 (z : Int) : z * (256 - z) = 256 * z - z * z := by rw [Int.mul_sub, Int.mul_comm z 256]
  simp only [V8.dot, rhs, ca, cb, cc, k1, show many 8 = 256 from rfl]
  rfl

theorem low_le_cnt (P : W n → Bool) (w : W n) : low P w ≤ cnt P :=
  total_mono n _ _ (fun a => by unfold ind; cases P a <;> cases dot n w a <;> simp)

/-- **End-to-end exclusion.**  For halves f, g whose high block takes values 4 mod 8 of
    magnitude at most 28 and with t agreeing input pairs, the profile and the split counts are
    computed from (f, g) and the moment identities are proved here.  If the finite check for t
    passes, no global phase rank r and rank-drop pattern can satisfy the phase test, the drop
    count and the section facts. -/
theorem no_242_from_halves (t : Nat) (hc : ∀ a < (8 * t - 480) / 6 + 1, rowCheck t a = true)
    (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)
    (ht : agreements f g = t) (ht60 : 60 ≤ t)
    (r : Nat) (drop : W 8 → Bool)
    (hrank : r ∈ ranks t (pa f g + pc f g))
    (hdrop : total 8 (fun w => nz w * (if drop w then 1 else 0)) = 2 ^ r - 1)
    (hsec : ∀ w, w ≠ zero 8 →
      admissible (pa f g) (pb f g) (pc f g) r (sx f g w) (sy f g w) (sz f g w) (drop w) = true) :
    False := by
  have ca : ((pa f g : Nat) : Int) = cnt (clsA f g) := toNat_cast (cnt_nonneg _)
  have cb : ((pb f g : Nat) : Int) = cnt (clsB f g) := toNat_cast (cnt_nonneg _)
  have cc : ((pc f g : Nat) : Int) = cnt (clsC f g) := toNat_cast (cnt_nonneg _)
  have hT : 6 * pa f g + 3 * pb f g + 5 * pc f g = 8 * t - 480 := by
    have m := profile_mass f g res cap
    rw [ht, ← ca, ← cb, ← cc] at m
    omega
  have ha : pa f g < (8 * t - 480) / 6 + 1 := by omega
  have hcc : pc f g < (8 * t - 480 - 6 * pa f g) / 5 + 1 := by omega
  have e1 := allBelow_spec (hc _ ha) _ hcc
  have hrest : (8 * t - 480 - 6 * pa f g - 5 * pc f g) % 3 = 0 := by omega
  have hb : (8 * t - 480 - 6 * pa f g - 5 * pc f g) / 3 = pb f g := by omega
  simp only [hrest, hb, bne_self_eq_false, Bool.false_or, List.all_eq_true] at e1
  have e2 := e1 r hrank
  simp only [sysCheck, Bool.and_eq_true, decide_eq_true_eq] at e2
  obtain ⟨hneg, hs⟩ := e2
  generalize hv : certFor t (pa f g) (pc f g) r = v at hneg hs
  have hw : ∀ w, 0 ≤ nz w *
      v.dot (row (pa f g) (pb f g) (pc f g) (sx f g w) (sy f g w) (sz f g w) (drop w)) := by
    intro w
    by_cases hz : w = zero 8
    · simp [nz, hz]
    · have h := hsec w hz
      obtain ⟨hxa, hyb, hzc, -, -⟩ := admissible_parts h
      have key : 0 ≤ v.dot (row (pa f g) (pb f g) (pc f g) (sx f g w) (sy f g w) (sz f g w) (drop w)) := by
        by_cases hx2 : sx f g w ≤ pa f g / 2
        · exact split_nonneg v t _ _ _ r hT hs _ _ _ _ hx2 h
        · rw [← row_compl _ _ _ _ _ _ _ hxa hyb hzc]
          exact split_nonneg v t _ _ _ r hT hs _ _ _ _ (by omega)
            (admissible_compl _ _ _ r _ _ _ _ hxa hyb hzc h)
      simpa [nz, hz] using key
  have hsum := total_nonneg _ hw
  rw [rows_sum v f g r drop hdrop] at hsum
  omega

end Balanced242Reduction

#print axioms Balanced242Reduction.no_242_from_halves

