/-
  The proved section facts, transported to every affine frequency hyperplane of a pair of
  Boolean halves (f, g).

  For w ≠ 0 and c : Bool the hyperplane {a : dot w a = c} is the 7-variable section with
  folded table D = secFun 7 w c U (values in [-2, 2]) and half-spectrum H = hi / 4.  With
  X, Y, Z the numbers of masks there with |hi| = 4, 20, 12 (|H| = 1, 5, 3):

    * 8 | 6X + 3Y + 5Z when the agreement count is even (`hyperplane_mass`);
    * X = Z = 0 forces Y = 80, so no (0,32,0) or (0,48,0) hyperplane (`hyperplane_0b0`);
    * the phase of H has a plateau height m in {16, 32, 64, 128} and
      m * |-896 + 8X + 12Y + 4Z| <= 16384 (`hyperplane_t7`).

  The c = false counts are `low` (the pair system's sx, sy, sz); see `low_eq_secCnt`.
-/
import Balanced242Reduction
import Balanced242Hyperplane
import Balanced242Plateau

namespace Balanced242SectionFacts
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support
open Balanced242Reduction (ind cnt low clsA clsB clsC hi_values)
open Balanced242Hyperplane

def U (f g : Half) (x : W 8) : Int := if f x = g x then 0 else sign (f x)

theorem U_bound (f g : Half) (x : W 8) : -1 ≤ U f g x ∧ U f g x ≤ 1 := by
  unfold U; cases f x <;> cases g x <;> decide

theorem hi_U (f g : Half) (a : W 8) : hi f g a = 2 * transform (U f g) a := by
  unfold hi spec transform
  rw [← total_sub, ← total_scale]
  apply congrArg (total 8); funext x
  show sign (f x) * chr a x - sign (g x) * chr a x = 2 * (U f g x * chr a x)
  unfold U
  cases f x <;> cases g x <;> simp [sign] <;> omega

def secD (f g : Half) (w : W 8) (c : Bool) : W 7 → Int := secFun 7 w c (U f g)
def secH (f g : Half) (w : W 8) (c : Bool) (a : W 7) : Int := hi f g (secPt 7 w c a) / 4
def secCnt (P : W 8 → Bool) (w : W 8) (c : Bool) : Int := total 7 (fun a => ind P (secPt 7 w c a))

section
variable (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)
  (w : W 8) (hw : w ≠ zero 8) (c : Bool)

theorem secD_bound (y : W 7) : -2 ≤ secD f g w c y ∧ secD f g w c y ≤ 2 :=
  secFun_bound 7 w c (U f g) (U_bound f g) y

include res hw in
theorem secH_spec (a : W 7) : transform (secD f g w c) a = 2 * secH f g w c a := by
  unfold secD secH
  rw [← sec_transform 7 w hw c (U f g) a]
  have h1 := hi_U f g (secPt 7 w c a)
  have h2 := res (secPt 7 w c a)
  omega

include res in
theorem secH_odd (a : W 7) : secH f g w c a % 2 = 1 := by
  unfold secH; have := res (secPt 7 w c a); omega

include hw in
theorem low_eq_secCnt (P : W 8 → Bool) : low P w = secCnt P w false := by
  unfold low secCnt
  rw [← sec_total 7 w hw false (ind P)]
  apply congrArg (total 8); funext a
  unfold ind; cases P a <;> cases dot 8 w a <;> rfl

include hw in
theorem cnt_split (P : W 8 → Bool) : cnt P = secCnt P w false + secCnt P w true := by
  unfold cnt secCnt
  rw [← sec_total 7 w hw false (ind P), ← sec_total 7 w hw true (ind P), ← total_add]
  apply congrArg (total 8); funext a
  cases dot 8 w a <;> simp

include res cap in
theorem t7_point (a : W 7) :
    Balanced242Section0320.phase (secH f g w c a) * secH f g w c a =
      -7 + 8 * ind (clsA f g) (secPt 7 w c a) + 12 * ind (clsB f g) (secPt 7 w c a) +
        4 * ind (clsC f g) (secPt 7 w c a) := by
  unfold secH ind clsA clsB clsC
  rcases hi_values f g res cap (secPt 7 w c a) with h | h | h | h | h | h | h | h <;>
    rw [h] <;> decide

include res cap in
theorem sq_point (a : W 7) :
    secH f g w c a * secH f g w c a =
      49 - 8 * (6 * ind (clsA f g) (secPt 7 w c a) + 3 * ind (clsB f g) (secPt 7 w c a) +
        5 * ind (clsC f g) (secPt 7 w c a)) := by
  unfold secH ind clsA clsB clsC
  rcases hi_values f g res cap (secPt 7 w c a) with h | h | h | h | h | h | h | h <;>
    rw [h] <;> decide

include res cap in
theorem t7_sum :
    total 7 (fun a => Balanced242Section0320.phase (secH f g w c a) * secH f g w c a) =
      -896 + 8 * secCnt (clsA f g) w c + 12 * secCnt (clsB f g) w c +
        4 * secCnt (clsC f g) w c := by
  simp only [t7_point f g res cap w c, total_add, total_scale, total_const]
  rfl

theorem point_le_total : ∀ (n : Nat) (F : W n → Int), (∀ x, 0 ≤ F x) → ∀ a, F a ≤ total n F := by
  intro n
  induction n with
  | zero => intro F _ a; cases a; exact Int.le_refl _
  | succ m ih =>
    intro F hF a
    rcases a with ⟨b, a⟩
    have h0 := Balanced242Plateau.total_nonneg' (fun x => F (false, x)) (fun x => hF _)
    have h1 := Balanced242Plateau.total_nonneg' (fun x => F (true, x)) (fun x => hF _)
    show F (b, a) ≤ total m _ + total m _
    cases b
    · have := ih (fun x => F (false, x)) (fun x => hF _) a; omega
    · have := ih (fun x => F (true, x)) (fun x => hF _) a; omega

theorem ind_nonneg' (P : W 8 → Bool) (a : W 8) : 0 ≤ ind P a := by
  unfold ind; cases P a <;> decide

include res cap hw in
/-- No hyperplane with only |H| in {5, 7} unless exactly 80 have magnitude 5. -/
theorem hyperplane_0b0 (hx : secCnt (clsA f g) w c = 0) (hz : secCnt (clsC f g) w c = 0) :
    secCnt (clsB f g) w c = 80 := by
  have zA (a : W 7) : ind (clsA f g) (secPt 7 w c a) = 0 := by
    have := point_le_total 7 (fun a => ind (clsA f g) (secPt 7 w c a)) (fun x => ind_nonneg' _ _) a
    have := ind_nonneg' (clsA f g) (secPt 7 w c a)
    unfold secCnt at hx; omega
  have zC (a : W 7) : ind (clsC f g) (secPt 7 w c a) = 0 := by
    have := point_le_total 7 (fun a => ind (clsC f g) (secPt 7 w c a)) (fun x => ind_nonneg' _ _) a
    have := ind_nonneg' (clsC f g) (secPt 7 w c a)
    unfold secCnt at hz; omega
  apply Balanced242Plateau.section_0_b_0 (secD f g w c) (secH f g w c) _
    (secD_bound f g w c) (secH_spec f g res w hw c)
  · intro a
    have hA := zA a; have hC := zC a
    unfold secH; unfold ind clsA at hA; unfold ind clsC at hC
    rcases hi_values f g res cap (secPt 7 w c a) with h | h | h | h | h | h | h | h <;>
      rw [h] at hA hC ⊢ <;> first | decide | (exfalso; revert hA; decide) | (exfalso; revert hC; decide)
  · unfold secCnt
    apply congrArg (total 7); funext a
    unfold secH ind clsB
    rcases hi_values f g res cap (secPt 7 w c a) with h | h | h | h | h | h | h | h <;>
      rw [h] <;> decide

include res cap hw in
/-- The T7 phase bound on every hyperplane, with the section's own plateau height. -/
theorem hyperplane_t7 : ∃ m : Int, (m = 16 ∨ m = 32 ∨ m = 64 ∨ m = 128) ∧
    (∀ y, transform (fun a => Balanced242Section0320.phase (secH f g w c a)) y = 0 ∨
      transform (fun a => Balanced242Section0320.phase (secH f g w c a)) y = m ∨
      transform (fun a => Balanced242Section0320.phase (secH f g w c a)) y = -m) ∧
    -16384 ≤ m * (-896 + 8 * secCnt (clsA f g) w c + 12 * secCnt (clsB f g) w c +
        4 * secCnt (clsC f g) w c) ∧
    m * (-896 + 8 * secCnt (clsA f g) w c + 12 * secCnt (clsB f g) w c +
        4 * secCnt (clsC f g) w c) ≤ 16384 := by
  obtain ⟨m, hm, hplat, h1, h2⟩ := Balanced242Plateau.t7_bound (secD f g w c) (secH f g w c)
    (secD_bound f g w c) (secH_spec f g res w hw c) (secH_odd f g res w c)
  rw [t7_sum f g res cap w c] at h1 h2
  exact ⟨m, hm, hplat, h1, h2⟩

theorem U_parity (x : W 8) : U f g x + (sameBit false (f x) (g x) + sameBit true (f x) (g x)) - 1 =
    2 * (if f x = g x then 0 else if f x then -1 else 0) := by
  unfold U sameBit; cases f x <;> cases g x <;> decide

include hw in
/-- The folded energy is even when the agreement count is even. -/
theorem secD_sq_even (ht : agreements f g % 2 = 0) :
    total 7 (fun a => secD f g w c a * secD f g w c a) % 2 = 0 := by
  have dsq (a : W 7) : secD f g w c a * secD f g w c a =
      secD f g w c a + 2 * ((secD f g w c a * secD f g w c a - secD f g w c a) / 2) := by
    have := secD_bound f g w c a
    have hd : secD f g w c a = -2 ∨ secD f g w c a = -1 ∨ secD f g w c a = 0 ∨
        secD f g w c a = 1 ∨ secD f g w c a = 2 := by omega
    rcases hd with h | h | h | h | h <;> rw [h] <;> decide
  have e1 : total 7 (fun a => secD f g w c a * secD f g w c a) =
      total 7 (secD f g w c) + 2 * total 7
        (fun a => (secD f g w c a * secD f g w c a - secD f g w c a) / 2) := by
    rw [← total_scale, ← total_add]; apply congrArg (total 7); funext a; exact dsq a
  obtain ⟨k, hk⟩ := secFun_total 7 w hw c (U f g)
  change total 7 (secD f g w c) = _ at hk
  have e3 : total 8 (U f g) + agreements f g - 256 =
      2 * total 8 (fun x => if f x = g x then 0 else if f x then -1 else 0) := by
    unfold agreements countPair
    rw [← total_scale]
    have := total_add 8 (fun x => sameBit false (f x) (g x)) (fun x => sameBit true (f x) (g x))
    have h256 : total 8 (fun _ => (1 : Int)) = 256 := by rw [total_const]; decide
    have := congrArg (total 8) (funext (U_parity f g))
    simp only [total_sub, total_add] at this
    omega
  rw [e1, hk]
  change (total 8 (U f g) + 2 * k + _) % 2 = 0
  omega

include res cap hw in
/-- Every hyperplane mass is a multiple of eight when the agreement count is even. -/
theorem hyperplane_mass (ht : agreements f g % 2 = 0) :
    (6 * secCnt (clsA f g) w c + 3 * secCnt (clsB f g) w c + 5 * secCnt (clsC f g) w c) % 8 = 0 := by
  -- Parseval on the section
  have par := Balanced242Section0320.parseval (secD f g w c)
  simp only [secH_spec f g res w hw c] at par
  have r (a : W 7) : 2 * secH f g w c a * (2 * secH f g w c a) =
      196 - 32 * (6 * ind (clsA f g) (secPt 7 w c a) + 3 * ind (clsB f g) (secPt 7 w c a) +
        5 * ind (clsC f g) (secPt 7 w c a)) := by
    have := sq_point f g res cap w c a
    generalize secH f g w c a = h at this ⊢
    have h4 : 2 * h * (2 * h) = 4 * (h * h) := by
      rw [Int.mul_assoc, Int.mul_left_comm h 2 h, ← Int.mul_assoc]; try omega
    rw [h4, this]; omega
  simp only [r, total_sub, total_const, total_scale, total_add] at par
  have hm7 : many 7 = 128 := by decide
  rw [hm7] at par
  have ev := secD_sq_even f g w hw c ht
  generalize total 7 (fun y => secD f g w c y * secD f g w c y) = E at par ev
  unfold secCnt
  generalize total 7 (fun a => ind (clsA f g) (secPt 7 w c a)) = X at par ⊢
  generalize total 7 (fun a => ind (clsB f g) (secPt 7 w c a)) = Y at par ⊢
  generalize total 7 (fun a => ind (clsC f g) (secPt 7 w c a)) = Z at par ⊢
  omega

end

end Balanced242SectionFacts

#print axioms Balanced242SectionFacts.hyperplane_0b0
#print axioms Balanced242SectionFacts.hyperplane_t7
#print axioms Balanced242SectionFacts.hyperplane_mass
#print axioms Balanced242SectionFacts.low_eq_secCnt
#print axioms Balanced242SectionFacts.cnt_split
#print axioms Balanced242SectionFacts.secD_sq_even
