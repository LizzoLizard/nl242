/-
  Global phase rank: support coset, drop directions, and section plateau heights.

  For cubic-free phase bits beta on W n (radical R = {d : rad beta d}, |R| = rr):
    * the Walsh support of q = sign o beta is {y : good y}, a coset of R^perp, and
      q^(y)^2 = 2^n rr on it (`spec_good`);
    * rr * #good = 2^n and rr * #perp = 2^n (`rr_good`, `rr_perp`);
    * folding along a direction w gives the section spectrum (q^(p) + sign(c) q^(p+w)) / 2,
      so the section plateau height is the global height when w is in R^perp (rank drop),
      and half of it otherwise (`section_levels`).
-/
import Balanced242Plateau
import Balanced242SectionFacts

namespace Balanced242Rank
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom Balanced242Support
open Balanced242Plateau (Cube ell rad phi rad_spec spec_sq rad_add phi_add ind all_false_exists
  add_assoc' add_zero_right total_nonneg' ind_nonneg sign_sq sq_cases)

section General
variable {n : Nat} (β : W n → Bool)

/-- A character of the radical sums to 0 or |R| over it. -/
theorem char_radical (χ : W n → Bool)
    (hχ : ∀ e, rad β e = true → ∀ d, χ (add n e d) = xor (χ e) (χ d)) :
    ((worlds n).all (fun e => !(rad β e && χ e)) = false →
      total n (fun d => ind (rad β d) * sign (χ d)) = 0) ∧
    ((worlds n).all (fun e => !(rad β e && χ e)) = true →
      total n (fun d => ind (rad β d) * sign (χ d)) = total n (fun d => ind (rad β d))) := by
  constructor
  · intro hb
    obtain ⟨e, _, he⟩ := all_false_exists _ _ hb
    have he : rad β e = true ∧ χ e = true := by
      revert he; cases rad β e <;> cases χ e <;> decide
    have sh := sum_shift n e (fun d => ind (rad β d) * sign (χ d))
    simp only [rad_add β e he.1, hχ e he.1, he.2, signMul] at sh
    have neg (d : W n) : ind (rad β d) * (sign true * sign (χ d)) =
        -1 * (ind (rad β d) * sign (χ d)) := by
      simp only [sign, if_true]; rw [Int.mul_left_comm]
    simp only [neg, total_scale] at sh
    omega
  · intro hb
    rw [List.all_eq_true] at hb
    apply congrArg (total n); funext d
    have := hb d (all_worlds n d)
    cases h : rad β d
    · simp [ind]
    · rw [h] at this
      simp only [Bool.true_and, Bool.not_eq_true'] at this
      simp [ind, this, sign]

def good (y : W n) : Bool := (worlds n).all (fun e => !(rad β e && phi β y e))
def perp (w : W n) : Bool := (worlds n).all (fun e => !(rad β e && dot n w e))
def rr : Int := total n (fun d => ind (rad β d))

theorem all_spec {p : W n → Bool} : (worlds n).all p = true ↔ ∀ e, p e = true := by
  rw [List.all_eq_true]
  exact ⟨fun h e => h e (all_worlds n e), fun h e _ => h e⟩

theorem good_spec {y : W n} : good β y = true ↔ ∀ e, rad β e = true → phi β y e = false := by
  unfold good; rw [all_spec]
  constructor
  · intro h e he; have := h e; rw [he] at this; revert this; cases phi β y e <;> decide
  · intro h e; cases he : rad β e
    · rfl
    · rw [h e he]; rfl

theorem perp_spec {w : W n} : perp β w = true ↔ ∀ e, rad β e = true → dot n w e = false := by
  unfold perp; rw [all_spec]
  constructor
  · intro h e he; have := h e; rw [he] at this; revert this; cases dot n w e <;> decide
  · intro h e; cases he : rad β e
    · rfl
    · rw [h e he]; rfl

theorem rad_zero : rad β (zero n) = true := by
  rw [rad_spec]; intro a
  unfold ell; rw [add_zero_right]; cases β a <;> cases β (zero n) <;> rfl

theorem rr_pos : 1 ≤ rr β := by
  have := Balanced242SectionFacts.point_le_total n (fun d => ind (rad β d))
    (fun d => ind_nonneg _) (zero n)
  rw [rad_zero] at this; exact this

/-- The signed radical sum is rr on good frequencies and 0 elsewhere. -/
theorem S_good (y : W n) :
    total n (fun d => ind (rad β d) * sign (phi β y d)) = rr β * ind (good β y) := by
  have h := char_radical β (phi β y) (fun e he d => phi_add β y e he d)
  cases hg : good β y
  · rw [h.1 hg]; simp [ind]
  · rw [h.2 hg]; simp [ind, rr]

theorem spec_good (hc : Cube β) (y : W n) :
    transform (fun a => sign (β a)) y * transform (fun a => sign (β a)) y =
      many n * (rr β * ind (good β y)) := by
  rw [spec_sq β hc, S_good]

theorem rr_good (hc : Cube β) : rr β * total n (fun y => ind (good β y)) = many n := by
  have par := Balanced242Section0320.parseval (fun a => sign (β a))
  simp only [sign_sq, total_const, Int.mul_one, spec_good β hc, total_scale] at par
  exact Int.eq_of_mul_eq_mul_left (by have := many_pos n; omega) par

theorem chr_sum (d : W n) : total n (fun w => sign (dot n w d)) = many n * ind (decide (d = zero n)) := by
  have h := identity_spectrum n d
  have e : (fun w => sign (dot n w d)) = fun w => chr d w := by
    funext w; simp only [chr, dot_comm n w d]
  rw [e]
  change total n (chr d) = _ at h
  rw [h]
  by_cases z : d = zero n <;> simp [z, ind]

theorem rr_perp : rr β * total n (fun w => ind (perp β w)) = many n := by
  have row (w : W n) : total n (fun d => ind (rad β d) * sign (dot n w d)) = rr β * ind (perp β w) := by
    have h := char_radical β (dot n w) (fun e _ d => dot_right n w e d)
    cases hp : perp β w
    · rw [h.1 hp]; simp [ind]
    · rw [h.2 hp]; simp [ind, rr]
  have dbl := swap n n (fun w d => ind (rad β d) * sign (dot n w d))
  simp only [row, total_scale] at dbl
  rw [dbl]
  simp only [chr_sum]
  have e2 (d : W n) : ind (rad β d) * (many n * ind (decide (d = zero n))) = many n * hits (zero n) d := by
    by_cases z : d = zero n
    · subst z; simp [ind, hits, rad_zero]
    · have : ¬ zero n = d := fun h => z h.symm
      simp [ind, hits, z, this]
  simp only [e2, total_scale, diagonal, Int.mul_one]

theorem good_perp {y y' : W n} (hy : good β y = true) (hy' : good β y' = true) :
    perp β (add n y y') = true := by
  rw [perp_spec]; intro e he
  have a := (good_spec β).1 hy e he
  have b := (good_spec β).1 hy' e he
  unfold phi at a b
  rw [dot_add]
  revert a b
  cases dot n y e <;> cases dot n y' e <;> cases β (zero n) <;> cases β e <;> decide

theorem good_shift {y u : W n} (hy : good β y = true) (hu : perp β u = true) :
    good β (add n y u) = true := by
  rw [good_spec]; intro e he
  have a := (good_spec β).1 hy e he
  have b := (perp_spec β).1 hu e he
  unfold phi at a ⊢
  rw [dot_add, b]
  revert a
  cases dot n y e <;> cases β (zero n) <;> cases β e <;> decide

end General

/-! ## Section spectra from the global spectrum -/

open Balanced242Hyperplane in
theorem secFun_pair : ∀ (n : Nat) (w : W (n+1)), w ≠ zero (n+1) →
    ∀ (c : Bool) (F : W (n+1) → Int) (x : W n),
      ∃ p, secFun n w c F x = F p + sign c * F (add (n+1) w p) := by
  intro n
  induction n with
  | zero =>
    intro w hw c F x
    rcases w with ⟨b, w'⟩
    cases b
    · exact absurd rfl hw
    · exact ⟨(false, x), by rw [secFun_true]; rfl⟩
  | succ m ih =>
    intro w hw c F x
    rcases w with ⟨b, w'⟩
    cases b
    · have hw' : w' ≠ zero (m+1) := fun h => hw (by rw [h]; rfl)
      rcases x with ⟨b, x⟩
      obtain ⟨p, hp⟩ := ih w' hw' c (fun y => F (b, y)) x
      exact ⟨(b, p), by rw [secFun_false, hp]; simp only [add, Bool.false_xor]⟩
    · exact ⟨(false, x), by rw [secFun_true]; rfl⟩

theorem transform_transform {n : Nat} (v : W n → Int) (x : W n) :
    transform (transform v) x = many n * v x := by
  rw [← inversion v x]
  unfold transform
  apply congrArg (total n); funext a
  rw [Balanced242Section0320.chr_comm]

open Balanced242Hyperplane in
theorem section_spectrum (n : Nat) (w : W (n+1)) (hw : w ≠ zero (n+1)) (c : Bool)
    (q : W (n+1) → Int) (y : W n) :
    2 * transform (fun a => q (secPt n w c a)) y = secFun n w c (transform q) y := by
  have inv1 (a : W n) : many (n+1) * q (secPt n w c a) = transform (secFun n w c (transform q)) a := by
    rw [← sec_transform n w hw c (transform q) a, transform_transform]
  have e := congrArg (fun F => transform F y) (funext inv1)
  simp only [transform_smul, transform_transform] at e
  have h2 : many (n+1) = 2 * many n := by unfold many; rw [Int.pow_succ, Int.mul_comm]
  rw [h2, Int.mul_comm 2 (many n), Int.mul_assoc] at e
  exact Int.eq_of_mul_eq_mul_left (by have := many_pos n; omega) e

section Levels
variable {n : Nat} (β : W (n+1) → Bool)

theorem spec_values (hc : Cube β) (M : Int) (hMM : M * M = many (n+1) * rr β) (p : W (n+1)) :
    (good β p = true → transform (fun a => sign (β a)) p = M ∨ transform (fun a => sign (β a)) p = -M) ∧
    (good β p = false → transform (fun a => sign (β a)) p = 0) := by
  have h := spec_good β hc p
  constructor
  · intro hg
    rw [hg] at h; simp only [ind, if_true, Int.mul_one] at h
    rw [← hMM] at h
    exact sq_cases _ M h
  · intro hg
    rw [hg] at h; simp only [ind, Bool.false_eq_true, if_false, Int.mul_zero] at h
    rcases sq_cases _ 0 (by rw [h, Int.mul_zero]) with h' | h' <;> omega

theorem add_back (w p : W (n+1)) : add (n+1) (add (n+1) w p) w = p := by
  rw [add_comm (n+1) w p, add_assoc', add_self, add_zero_right]

theorem pair_add (w p : W (n+1)) : add (n+1) p (add (n+1) w p) = w := by
  rw [add_comm (n+1) w p, ← add_assoc', add_self, add_zero_left]

open Balanced242Hyperplane in
/-- Section plateau heights: the global height M on rank-drop directions, M/2 otherwise. -/
theorem section_levels (hc : Cube β) (w : W (n+1)) (hw : w ≠ zero (n+1)) (c : Bool)
    (M : Int) (hMM : M * M = many (n+1) * rr β) (y : W n) :
    (perp β w = true →
      transform (fun a => sign (β (secPt n w c a))) y = 0 ∨
      transform (fun a => sign (β (secPt n w c a))) y = M ∨
      transform (fun a => sign (β (secPt n w c a))) y = -M) ∧
    (perp β w = false →
      2 * transform (fun a => sign (β (secPt n w c a))) y = 0 ∨
      2 * transform (fun a => sign (β (secPt n w c a))) y = M ∨
      2 * transform (fun a => sign (β (secPt n w c a))) y = -M) := by
  have e := section_spectrum n w hw c (fun a => sign (β a)) y
  obtain ⟨p, hp⟩ := secFun_pair n w hw c (transform (fun a => sign (β a))) y
  rw [hp] at e
  generalize transform (fun a => sign (β (secPt n w c a))) y = s at e ⊢
  have vp := spec_values β hc M hMM p
  have vq := spec_values β hc M hMM (add (n+1) w p)
  have sc : sign c = 1 ∨ sign c = -1 := by cases c <;> decide
  constructor
  · intro hperp
    have back : good β (add (n+1) w p) = good β p := by
      cases hg : good β p
      · cases hg' : good β (add (n+1) w p)
        · rfl
        · have := good_shift β hg' hperp; rw [add_back] at this; simp [hg] at this
      · have := good_shift β hg hperp; rw [add_comm (n+1) p w] at this; exact this
    cases hg : good β p
    · have a := vp.2 hg; have b := vq.2 (by rw [back, hg])
      rw [a, b] at e; omega
    · have a := vp.1 hg; have b := vq.1 (by rw [back, hg])
      rcases a with a | a <;> rcases b with b | b <;> rw [a, b] at e <;>
        rcases sc with h | h <;> rw [h] at e <;> omega
  · intro hperp
    have notboth : ¬ (good β p = true ∧ good β (add (n+1) w p) = true) := by
      intro ⟨h1, h2⟩
      have := good_perp β h1 h2
      rw [pair_add] at this; rw [this] at hperp; exact Bool.noConfusion hperp
    cases hg : good β p
    · have a := vp.2 hg
      cases hg' : good β (add (n+1) w p)
      · have b := vq.2 hg'; rw [a, b] at e; omega
      · have b := vq.1 hg'
        rcases b with b | b <;> rw [a, b] at e <;> rcases sc with h | h <;> rw [h] at e <;> omega
    · cases hg' : good β (add (n+1) w p)
      · have a := vp.1 hg; have b := vq.2 hg'
        rcases a with a | a <;> rw [a, b] at e <;> omega
      · exact absurd ⟨hg, hg'⟩ notboth

end Levels

end Balanced242Rank

#print axioms Balanced242Rank.rr_perp
#print axioms Balanced242Rank.rr_good
#print axioms Balanced242Rank.good_shift
#print axioms Balanced242Rank.section_levels
