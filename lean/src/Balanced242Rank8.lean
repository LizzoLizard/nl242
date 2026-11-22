/-
  Exact rank-8 section exception-weight identity:

    secExc(section 0) + secExc(section 1) = N_+ = (3t - 208)/2 - k,

  where for a global phase rank-8 table (transform q8 takes values in {+16, -16} everywhere,
  sigma = transform q8 / 16), N_+ counts inputs x with U(x) * sigma(x) = +1, and for each
  7-variable rank-6 hyperplane section D with phase transform qhat in {0, +16, -16},
    secExc D qhat = sum_{y : qhat y = +-16} max(0, D(y) * (qhat y / 16))
                  + #{y : qhat y = 0 and |D(y)| = 2}.
-/
import Balanced242RankCond

namespace Balanced242Rank8
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Hyperplane Balanced242Global
open Balanced242Reduction (cnt clsA clsC)
open Balanced242SectionFacts (U U_bound secD secH)
open Balanced242RankCond (q8 phase_identity)

local notation "phase" => Balanced242Section0320.phase

/-- Pointwise contribution to the rank-6 section exception weight `E(D)`. -/
def excPt (d qh : Int) : Int :=
  if qh = 16 then (if 0 < d then d else 0)
  else if qh = -16 then (if d < 0 then -d else 0)
  else if d = 2 ∨ d = -2 then 1 else 0

/-- Total exception weight `E(D)` of a 7-variable rank-6 section `D` with phase transform `qhat`. -/
def secExc (D qhat : W 7 → Int) : Int :=
  total 7 (fun y => excPt (D y) (qhat y))

/-- Exact pointwise pair identity for all `u0, u1 ∈ {-1, 0, 1}` and `s0, s1 ∈ {-1, 1}`. -/
private theorem pair_exc_pt (u0 u1 s0 s1 : Int)
    (hu0 : u0 = -1 ∨ u0 = 0 ∨ u0 = 1) (hu1 : u1 = -1 ∨ u1 = 0 ∨ u1 = 1)
    (hs0 : s0 = -1 ∨ s0 = 1) (hs1 : s1 = -1 ∨ s1 = 1) :
    excPt (u0 + u1) (8 * (s0 + s1)) + excPt (u0 - u1) (8 * (s0 - s1)) =
      (if u0 * s0 = 1 then 1 else 0) + (if u1 * s1 = 1 then 1 else 0) := by
  rcases hu0 with rfl | rfl | rfl <;>
  rcases hu1 with rfl | rfl | rfl <;>
  rcases hs0 with rfl | rfl <;>
  rcases hs1 with rfl | rfl <;>
  decide

/-- Summing the pair identity over all `2^n` folded pairs along any nonzero direction `w`. -/
private theorem secFun_exc_sum : ∀ (n : Nat) (w : W (n+1)), w ≠ zero (n+1) →
    ∀ (U σ : W (n+1) → Int),
      (∀ x, U x = -1 ∨ U x = 0 ∨ U x = 1) →
      (∀ x, σ x = -1 ∨ σ x = 1) →
      total n (fun y => excPt (secFun n w false U y) (8 * secFun n w false σ y) +
                        excPt (secFun n w true U y) (8 * secFun n w true σ y)) =
        total (n+1) (fun x => if U x * σ x = 1 then 1 else 0) := by
  have tcase (n : Nat) (w' : W n) (U σ : W (n+1) → Int)
      (hU : ∀ x, U x = -1 ∨ U x = 0 ∨ U x = 1) (hσ : ∀ x, σ x = -1 ∨ σ x = 1) :
      total n (fun y => excPt (secFun n (true, w') false U y) (8 * secFun n (true, w') false σ y) +
                        excPt (secFun n (true, w') true U y) (8 * secFun n (true, w') true σ y)) =
        total (n+1) (fun x => if U x * σ x = 1 then 1 else 0) := by
    have pt (y : W n) :
        excPt (secFun n (true, w') false U y) (8 * secFun n (true, w') false σ y) +
        excPt (secFun n (true, w') true U y) (8 * secFun n (true, w') true σ y) =
          (if U (false, y) * σ (false, y) = 1 then 1 else 0) +
          (if U (true, add n w' y) * σ (true, add n w' y) = 1 then 1 else 0) := by
      have hneg (z : Int) : -1 * z = -z := by omega
      simp only [secFun_true, sign, Bool.false_eq_true, if_false, if_true,
        Int.one_mul, hneg, ← Int.sub_eq_add_neg]
      exact pair_exc_pt _ _ _ _ (hU (false, y)) (hU (true, add n w' y))
        (hσ (false, y)) (hσ (true, add n w' y))
    rw [funext pt, total_add, sum_shift n w' (fun y => if U (true, y) * σ (true, y) = 1 then 1 else 0)]
    rfl
  intro n
  induction n with
  | zero =>
    intro w hw U σ hU hσ
    rcases w with ⟨b, w'⟩
    cases b
    · exact absurd rfl hw
    · exact tcase 0 w' U σ hU hσ
  | succ m ih =>
    intro w hw U σ hU hσ
    rcases w with ⟨b, w'⟩
    cases b
    · have hw' : w' ≠ zero (m+1) := fun h => hw (by rw [h]; rfl)
      show total m _ + total m _ = total (m+1) _ + total (m+1) _
      have h0 := ih w' hw' (fun y => U (false, y)) (fun y => σ (false, y))
        (fun y => hU (false, y)) (fun y => hσ (false, y))
      have h1 := ih w' hw' (fun y => U (true, y)) (fun y => σ (true, y))
        (fun y => hU (true, y)) (fun y => hσ (true, y))
      simp only [secFun_false]
      rw [h0, h1]
    · exact tcase (m+1) w' U σ hU hσ

/-- At global rank 8 (`transform (q8 f g) x ∈ {±16}`), the Walsh transform of a hyperplane
section's phase equals `8 * secFun 7 w c σ`, where `σ x = transform (q8 f g) x / 16`. -/
theorem sec_phase_transform (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (h8 : ∀ x, transform (q8 f g) x = 16 ∨ transform (q8 f g) x = -16)
    (w : W 8) (hw : w ≠ zero 8) (c : Bool) (y : W 7) :
    transform (fun a => phase (secH f g w c a)) y =
      8 * secFun 7 w c (fun x => transform (q8 f g) x / 16) y := by
  let σ : W 8 → Int := fun x => transform (q8 f g) x / 16
  have hσ16 (x : W 8) : 16 * σ x = transform (q8 f g) x := by
    dsimp only [σ]; rcases h8 x with h | h <;> rw [h] <;> decide
  have hts (a : W 8) : transform σ a = 16 * q8 f g a := by
    have hinv := inversion (q8 f g) a
    have h256 : many 8 = 256 := by decide
    rw [h256] at hinv
    have h16 : 16 * transform σ a = transform (transform (q8 f g)) a := by
      rw [← transform_smul]; apply congrArg (fun F => transform F a); funext x; exact hσ16 x
    have hsym : transform (transform (q8 f g)) a = total 8 (fun x => transform (q8 f g) x * chr x a) := by
      unfold transform; apply congrArg (total 8); funext x; simp only [chr, dot_comm 8 a x]
    rw [hsym, hinv] at h16
    omega
  have hsec_eq (a : W 7) : transform (secFun 7 w c σ) a = 16 * phase (secH f g w c a) := by
    rw [← sec_transform 7 w hw c σ a, hts (secPt 7 w c a)]
    congr 1
    unfold q8 β8 Balanced242SectionFacts.secH
    exact (Balanced242Plateau.phase_bt _ (Balanced242Global.odd8 f g res (secPt 7 w c a))).symm
  have hinv7 := inversion (secFun 7 w c σ) y
  have h128 : many 7 = 128 := by decide
  rw [h128] at hinv7
  have h16 : 16 * transform (fun a => phase (secH f g w c a)) y =
      total 7 (fun a => transform (secFun 7 w c σ) a * chr a y) := by
    show 16 * total 7 (fun a => phase (secH f g w c a) * chr y a) = _
    rw [← total_scale]
    apply congrArg (total 7); funext a
    rw [hsec_eq a]
    simp only [chr, dot_comm 7 y a]
    rw [Int.mul_assoc]
  rw [hinv7] at h16
  change 16 * transform (fun a => phase (secH f g w c a)) y =
    128 * secFun 7 w c (fun x => transform (q8 f g) x / 16) y at h16
  omega

/-- Number of `+1` exception sites `N_+ = #{x : U(x) * σ(x) = 1}` at global rank 8. -/
def Nplus (f g : Half) : Int :=
  total 8 (fun x => if U f g x * (transform (q8 f g) x / 16) = 1 then 1 else 0)

/-- Exact formula `2 * N_+ = 3t - 208 - 2k` at global rank 8. -/
theorem rank8_Nplus_formula (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28)
    (h8 : ∀ x, transform (q8 f g) x = 16 ∨ transform (q8 f g) x = -16) :
    2 * Nplus f g = 3 * agreements f g - 208 - 2 * (cnt (clsA f g) + cnt (clsC f g)) := by
  let σ : W 8 → Int := fun x => transform (q8 f g) x / 16
  have hpt (x : W 8) :
      2 * (if U f g x * σ x = 1 then (1 : Int) else 0) =
        U f g x * σ x + (1 - (sameBit false (f x) (g x) + sameBit true (f x) (g x))) := by
    have hσ : σ x = -1 ∨ σ x = 1 := by
      dsimp only [σ]; rcases h8 x with h | h <;> rw [h] <;> decide
    unfold U sameBit
    rcases hσ with hs | hs <;> rw [hs] <;> cases f x <;> cases g x <;> decide
  have hsum : 2 * Nplus f g =
      total 8 (fun x => U f g x * σ x) + (256 - agreements f g) := by
    unfold Nplus
    rw [← total_scale]
    have e := congrArg (total 8) (funext hpt)
    rw [total_add, total_sub, total_const, total_add] at e
    have h256 : many 8 * (1 : Int) = 256 := by decide
    rw [h256] at e
    unfold agreements countPair
    exact e
  have hpi := phase_identity f g res cap
  have h16 : total 8 (fun x => U f g x * transform (q8 f g) x) =
      16 * total 8 (fun x => U f g x * σ x) := by
    rw [← total_scale]; apply congrArg (total 8); funext x
    have hσ16 : transform (q8 f g) x = 16 * σ x := by
      dsimp only [σ]; rcases h8 x with h | h <;> rw [h] <;> decide
    rw [hσ16, Int.mul_left_comm]
  rw [h16] at hpi
  omega

/-- Exact rank-8 pair exception-weight identity: for every nonzero direction `w`,
the two complementary rank-6 sections satisfy `E(D0) + E(D1) = N_+`. -/
theorem rank8_secExc_sum (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (h8 : ∀ x, transform (q8 f g) x = 16 ∨ transform (q8 f g) x = -16)
    (w : W 8) (hw : w ≠ zero 8) :
    secExc (secD f g w false) (transform (fun a => phase (secH f g w false a))) +
    secExc (secD f g w true) (transform (fun a => phase (secH f g w true a))) =
      Nplus f g := by
  unfold secExc secD Nplus
  rw [← total_add]
  have heq : (fun y =>
      excPt (secFun 7 w false (U f g) y) (transform (fun a => phase (secH f g w false a)) y) +
      excPt (secFun 7 w true (U f g) y) (transform (fun a => phase (secH f g w true a)) y)) =
      (fun y =>
      excPt (secFun 7 w false (U f g) y) (8 * secFun 7 w false (fun x => transform (q8 f g) x / 16) y) +
      excPt (secFun 7 w true (U f g) y) (8 * secFun 7 w true (fun x => transform (q8 f g) x / 16) y)) := by
    funext y
    rw [sec_phase_transform f g res h8 w hw false y, sec_phase_transform f g res h8 w hw true y]
  rw [heq]
  exact secFun_exc_sum 7 w hw (U f g) (fun x => transform (q8 f g) x / 16)
    (fun x => by have := U_bound f g x; omega)
    (fun x => by dsimp only; rcases h8 x with h | h <;> rw [h] <;> decide)

end Balanced242Rank8

#print axioms Balanced242Rank8.rank8_Nplus_formula
#print axioms Balanced242Rank8.rank8_secExc_sum
