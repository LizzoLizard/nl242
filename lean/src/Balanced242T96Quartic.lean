/-
  Balanced242T96Quartic.lean — Unconditional rank-8 barycenter pairing and the
  7-variable rank-6 `y + z ≠ 18` quartic obstruction.

  Zero Mathlib, zero `sorry`, zero `native_decide`, zero `SectionEnum`,
  zero `Classical.choice` (`[propext, Quot.sound]` only!).

  Main exported theorems:
    1. `rank8_barycenters_paired`: for any rank-8 halves `f, g` (`rr (β8 f g) = 1`),
       * `(pb f g + pc f g) % 4 = 2` and `pb f g % 2 = pc f g % 2`,
       * `barycenter (clsB f g) = barycenter (clsC f g)` and
         `barycenter (clsA f g) = barycenter (clsD f g)` — proving unconditionally that
         the two odd-size classes ALWAYS have identical barycenter!
       * for every `w ≠ zero 8`,
         `((halfCnt w (clsB f g) + halfCnt w (clsC f g)) / 2) % 2 =
            if dot 8 w (add 8 (barycenter (clsA f g)) (barycenter (clsC f g))) then 1 else 0`.
    2. `rank8_a0_far_yz_div4`: whenever `pa f g = 0` at rank 8, translating by
       `P = barycenter (clsC f g)` forces EVERY nonzero direction `w` to have
       `halfCnt w (translate (clsB f g) P) % 2 = 0`,
       `halfCnt w (translate (clsC f g) P) % 2 = 0`, and
       `(halfCnt w (translate (clsB f g) P) + halfCnt w (translate (clsC f g) P)) % 4 = 0`.
    3. `no_section_yz_eq_18`: no 7-variable rank-6 section (`transform D = 2 * H`,
       `H` odd, `|H| ≤ 7`, `Cube β`, `phase (H a) = sign (β a)`, `rr β = 2`) has
       `y + z = 18` (proved constructively via radical-transverse 6-flat slicing,
       Parseval, 4th-order Walsh differences, `Cube`, and `spec_good` + `rr_good`).
-/
import Balanced242Quartic
import Balanced242Centered
import Balanced242Parity
import Balanced242Global

namespace Balanced242T96Quartic

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Blocks Balanced242Hyperplane
open Balanced242Reduction Balanced242Plateau Balanced242Rank Balanced242Global
open Balanced242SectionFacts (U)
open Balanced242Quartic
open Balanced242Krawtchouk (suppList halfCnt halfCntFalse halfCnt_add_false)
open Balanced242Centered (barycenter translate halfCnt_translate halfCnt_mod2_eq_dot_barycenter
  barycenter_translate_odd)
open Balanced242AnchorPair (sec_cube)

local notation "phase" => Balanced242Section0320.phase
local notation "bind" => Balanced242Plateau.ind

/-! ## Local constructive helpers -/

private def embedCompl : ∀ {m : Nat}, W (m + 1) → W m → W (m + 1)
  | 0, _, () => (false, ())
  | _ + 1, (true, _), v => (false, v)
  | _ + 1, (false, ur), (vb, vr) => (vb, embedCompl ur vr)

private theorem find_true_of_pos {n : Nat} (p : W n → Bool)
    (hpos : 0 < total n (fun x => bind (p x))) : ∃ x : W n, p x = true := by
  cases hall : (worlds n).all (fun x => !p x)
  · obtain ⟨x, _, hx⟩ := all_false_exists _ _ hall
    cases hpx : p x
    · rw [hpx] at hx; simp at hx
    · exact ⟨x, hpx⟩
  · exfalso
    rw [List.all_eq_true] at hall
    have hz : (fun x => bind (p x)) = fun _ => (0 : Int) := by
      funext x
      have hx := hall x (all_worlds n x)
      cases hpx : p x
      · rfl
      · rw [hpx] at hx; simp at hx
    rw [hz, total_zero] at hpos; omega

private theorem rr_from_plateau' {n : Nat} (β : W n → Bool) (hc : Cube β) (M : Int)
    (hplat : ∀ y, transform (fun a => sign (β a)) y = 0 ∨
      transform (fun a => sign (β a)) y = M ∨ transform (fun a => sign (β a)) y = -M) :
    many n * rr β = M * M := by
  have hrg := rr_good β hc
  have hrr := rr_pos β
  have hmn := many_pos n
  have hpos : 0 < total n (fun y => bind (good β y)) := by
    if h : 0 < total n (fun y => bind (good β y)) then exact h
    else
      exfalso
      have hle : rr β * total n (fun y => bind (good β y)) ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
  obtain ⟨y, hy⟩ := find_true_of_pos (good β) hpos
  have hsg := spec_good β hc y
  rw [hy] at hsg
  simp only [Balanced242Plateau.ind, if_true, Int.mul_one] at hsg
  rcases hplat y with h | h | h
  · rw [h] at hsg
    have hprod : 0 < many n * rr β := Int.mul_pos hmn (by omega)
    omega
  · rw [h] at hsg; exact hsg.symm
  · rw [h, Int.neg_mul_neg] at hsg; exact hsg.symm

private theorem total_exc35_eq_bc' {n : Nat} (H : W n → Int) :
    total n (fun a => exc35 (H a)) =
      total n (fun a => if (H a).natAbs = 5 then (1 : Int) else 0) +
      total n (fun a => if (H a).natAbs = 3 then (1 : Int) else 0) := by
  rw [← total_add]; apply congrArg (total n); funext a
  unfold exc35
  by_cases h3 : (H a).natAbs = 3
  · have h5 : (H a).natAbs ≠ 5 := by omega
    simp [h3, h5]
  · by_cases h5 : (H a).natAbs = 5
    · simp [h3, h5]
    · simp [h3, h5]

private theorem suppList_length_eq_cnt_nat (P : W 8 → Bool) :
    ((suppList P).length : Int) = cnt P := by
  have h1 := Balanced242Farkas.suppList_length_eq_total P
  unfold cnt Balanced242Reduction.ind
  exact h1

private theorem halfCnt_eq_total_true (w : W 8) (P : W 8 → Bool) :
    (halfCnt w P : Int) = total 8 (fun a => if P a && dot 8 w a then (1 : Int) else 0) := by
  unfold halfCnt suppList
  rw [List.filter_filter]
  have hfn : (fun a => dot 8 w a && P a) = (fun a => P a && dot 8 w a) :=
    funext (fun a => Bool.and_comm _ _)
  rw [hfn]
  have h := Balanced242Farkas.suppList_length_eq_total (fun a => P a && dot 8 w a)
  exact h

/-! ## Part 1: Unconditional rank-8 barycenter pairing & mod-4 law -/

/-- Complementary class `D`: masks with `|hi| = 28` (`|H| = 7`). -/
def clsD (f g : Half) (a : W 8) : Bool := (hi f g a).natAbs == 28

private theorem dot_eq_all_implies_eq : ∀ {n : Nat} (x y : W n),
    (∀ w : W n, dot n w x = dot n w y) → x = y
  | 0, (), (), _ => rfl
  | m + 1, (bx, x'), (by_, y'), h => by
    have hb : bx = by_ := by
      have h0 := h (true, zero m)
      simp only [dot, Bool.true_and, dot_zero, Bool.xor_false] at h0
      exact h0
    have hr : x' = y' := dot_eq_all_implies_eq x' y' (fun w' => by
      have h1 := h (false, w')
      simp only [dot, Bool.false_and, Bool.false_xor] at h1
      exact h1)
    rw [hb, hr]

private theorem halfCnt_add_eq_sec_total (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (w : W 8) (hw : w ≠ zero 8) :
    (halfCnt w (clsA f g) : Int) =
      total 7 (fun a => if (H8 f g (secPt 7 w true a)).natAbs = 1 then (1 : Int) else 0) ∧
    (halfCnt w (clsB f g) : Int) =
      total 7 (fun a => if (H8 f g (secPt 7 w true a)).natAbs = 5 then (1 : Int) else 0) ∧
    (halfCnt w (clsC f g) : Int) =
      total 7 (fun a => if (H8 f g (secPt 7 w true a)).natAbs = 3 then (1 : Int) else 0) := by
  have hpart (P : W 8 → Bool) :
      (halfCnt w P : Int) = total 7 (fun a => if P (secPt 7 w true a) then (1 : Int) else 0) := by
    rw [halfCnt_eq_total_true, sec_sum 7 w hw]
    have h0 : total 7 (fun a => if P (secPt 7 w false a) && dot 8 w (secPt 7 w false a) then (1 : Int) else 0) = 0 := by
      have hz : (fun a => if P (secPt 7 w false a) && dot 8 w (secPt 7 w false a) then (1 : Int) else 0) = fun _ => 0 := by
        funext a; rw [secPt_dot 7 w hw false a]; simp
      rw [hz, total_zero]
    have h1 : total 7 (fun a => if P (secPt 7 w true a) && dot 8 w (secPt 7 w true a) then (1 : Int) else 0) =
        total 7 (fun a => if P (secPt 7 w true a) then (1 : Int) else 0) := by
      apply congrArg (total 7); funext a
      rw [secPt_dot 7 w hw true a]; simp
    rw [h0, h1, Int.zero_add]
  have hnat (k : Nat) (x : W 8) :
      ((hi f g x).natAbs == 4 * k) = decide ((H8 f g x).natAbs = k) := by
    have hr := res x
    have h4 : hi f g x = 4 * H8 f g x := by unfold H8; omega
    rw [h4, Int.natAbs_mul]
    have h4n : (4 : Int).natAbs = 4 := rfl
    rw [h4n]
    cases h : ((4 * (H8 f g x).natAbs) == 4 * k)
    · symm; rw [decide_eq_false_iff_not]; intro heq; rw [heq] at h; simp at h
    · symm; rw [decide_eq_true_eq]; have := beq_iff_eq.mp h; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hpart (clsA f g)]; apply congrArg (total 7); funext a
    unfold clsA; have := hnat 1 (secPt 7 w true a); simp only [Nat.mul_one] at this
    rw [this]; cases h : decide ((H8 f g (secPt 7 w true a)).natAbs = 1) <;> simp_all
  · rw [hpart (clsB f g)]; apply congrArg (total 7); funext a
    unfold clsB; have := hnat 5 (secPt 7 w true a)
    rw [this]; cases h : decide ((H8 f g (secPt 7 w true a)).natAbs = 5) <;> simp_all
  · rw [hpart (clsC f g)]; apply congrArg (total 7); funext a
    unfold clsC; have := hnat 3 (secPt 7 w true a)
    rw [this]; cases h : decide ((H8 f g (secPt 7 w true a)).natAbs = 3) <;> simp_all

/-- For a global rank-8 phase (`rr (β8 f g) = 1`), EVERY affine hyperplane section has
    section rank 6 (`rr = 2`). -/
theorem rank8_sec_rr_eq_2 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (hrr8 : rr (β8 f g) = 1) (w : W 8) (hw : w ≠ zero 8) (c : Bool) :
    rr (fun a => β8 f g (secPt 7 w c a)) = 2 := by
  have hc8 : Cube (β8 f g) := cube8 f g res
  have hMM : (16 : Int) * 16 = many 8 * rr (β8 f g) := by rw [hrr8]; decide
  have hperp : perp (β8 f g) w = true := by
    rw [perp_spec]; intro e he
    have he0 : e = zero 8 := by
      by_cases hz : e = zero 8
      · exact hz
      · exfalso
        have h2 : (2 : Int) ≤ total 8 (fun d => bind (rad (β8 f g) d)) := by
          have hpt (d : W 8) : hits (zero 8) d + hits e d ≤ bind (rad (β8 f g) d) := by
            unfold hits
            by_cases h1 : zero 8 = d
            · subst h1
              have hne : ¬ e = zero 8 := hz
              simp only [if_true, hne, if_false, Int.add_zero, rad_zero]
              decide
            · by_cases h2 : e = d
              · subst h2
                simp only [h1, if_false, if_true, Int.zero_add, he]
                decide
              · simp only [h1, h2, if_false, Int.add_zero]
                exact Balanced242Plateau.ind_nonneg _
          have hm := total_mono 8 _ _ hpt
          rw [total_add, diagonal, diagonal] at hm
          omega
        change (2 : Int) ≤ rr (β8 f g) at h2
        omega
    rw [he0, dot_comm, dot_zero]
  let β7 : W 7 → Bool := fun a => β8 f g (secPt 7 w c a)
  have hc7 : Cube β7 := sec_cube (β8 f g) hc8 w c
  have hplat (y : W 7) :
      transform (fun a => sign (β7 a)) y = 0 ∨
      transform (fun a => sign (β7 a)) y = 16 ∨
      transform (fun a => sign (β7 a)) y = -16 :=
    (section_levels (β8 f g) hc8 w hw c 16 hMM y).1 hperp
  have hrr := rr_from_plateau' β7 hc7 16 hplat
  have hm : many 7 = 128 := by decide
  rw [hm] at hrr
  dsimp only [β7] at hrr
  omega

/-- Every nonzero hyperplane `w` of a rank-8 function satisfies:
    `16 ≤ h_B(w) + h_C(w)`, `2 ∣ (h_B(w) + h_C(w))`, and `8 ∣ (6 h_A(w) + 3 h_B(w) + 5 h_C(w))`. -/
theorem rank8_half_mod_laws (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (hrr8 : rr (β8 f g) = 1)
    (w : W 8) (hw : w ≠ zero 8) :
    16 ≤ halfCnt w (clsB f g) + halfCnt w (clsC f g) ∧
    (halfCnt w (clsB f g) + halfCnt w (clsC f g)) % 2 = 0 ∧
    (6 * halfCnt w (clsA f g) + 3 * halfCnt w (clsB f g) + 5 * halfCnt w (clsC f g)) % 8 = 0 := by
  let D7 : W 7 → Int := secFun 7 w true (U f g)
  let H7 : W 7 → Int := fun a => H8 f g (secPt 7 w true a)
  let β7 : W 7 → Bool := fun a => β8 f g (secPt 7 w true a)
  have hspec7 (a : W 7) : transform D7 a = 2 * H7 a := by
    dsimp only [D7, H7]
    rw [← sec_transform 7 w hw true (U f g) a]
    exact spec8 f g res (secPt 7 w true a)
  have hH7 (a : W 7) : H7 a % 2 = 1 ∧ (H7 a).natAbs ≤ 7 := by
    dsimp only [H7]
    have ho := odd8 f g res (secPt 7 w true a)
    have hc := cap (secPt 7 w true a)
    have h4 : hi f g (secPt 7 w true a) = 4 * H8 f g (secPt 7 w true a) := by
      have hr := res (secPt 7 w true a); unfold H8; omega
    exact ⟨ho, by omega⟩
  have hph7 (a : W 7) : phase (H7 a) = sign (β7 a) :=
    phase_bt (H7 a) (hH7 a).1
  have hrr7 : rr β7 = 2 := rank8_sec_rr_eq_2 f g res hrr8 w hw true
  have hyz := half_yz_ge_16 D7 H7 hspec7 hH7 β7 (sec_cube (β8 f g) (cube8 f g res) w true) hph7 hrr7
  have hdiv := half_mass_div8 D7 H7 hspec7 hH7
  dsimp only at hyz hdiv
  obtain ⟨hA, hB, hC⟩ := halfCnt_add_eq_sec_total f g res w hw
  rw [← hA, ← hB, ← hC] at hdiv
  rw [← hB, ← hC] at hyz
  exact ⟨by omega, by omega, by omega⟩

private theorem halfCnt_sum_all_classes (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (w : W 8) (hw : w ≠ zero 8) :
    halfCnt w (clsA f g) + halfCnt w (clsB f g) + halfCnt w (clsC f g) + halfCnt w (clsD f g) = 128 := by
  have hpt (a : W 8) :
      (if clsA f g a && dot 8 w a then (1 : Int) else 0) +
      (if clsB f g a && dot 8 w a then (1 : Int) else 0) +
      (if clsC f g a && dot 8 w a then (1 : Int) else 0) +
      (if clsD f g a && dot 8 w a then (1 : Int) else 0) =
      (if dot 8 w a then (1 : Int) else 0) := by
    unfold clsA clsB clsC clsD
    rcases hi_values f g res cap a with h | h | h | h | h | h | h | h <;>
      rw [h] <;> cases dot 8 w a <;> decide
  have hsum := congrArg (total 8) (funext hpt)
  rw [total_add, total_add, total_add] at hsum
  rw [← halfCnt_eq_total_true, ← halfCnt_eq_total_true, ← halfCnt_eq_total_true, ← halfCnt_eq_total_true] at hsum
  have h128 : total 8 (fun a => if dot 8 w a then (1 : Int) else 0) = 128 := by
    have hsc := sec_sum 7 w hw (fun a => if dot 8 w a then (1 : Int) else 0)
    have h0 : total 7 (fun a => if dot 8 w (secPt 7 w false a) then (1 : Int) else 0) = 0 := by
      rw [← total_zero 7]; apply congrArg (total 7); funext a; rw [secPt_dot 7 w hw false a]; rfl
    have h1 : total 7 (fun a => if dot 8 w (secPt 7 w true a) then (1 : Int) else 0) = 128 := by
      have : (fun a => if dot 8 w (secPt 7 w true a) then (1 : Int) else 0) = fun _ => (1 : Int) := by
        funext a; rw [secPt_dot 7 w hw true a]; rfl
      rw [this, total_const]; decide
    rw [hsc, h0, h1]; omega
  rw [h128] at hsum; omega

private theorem cntGood_256_of_rr1 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (hrr8 : rr (β8 f g) = 1) : cntGood f g = 256 := by
  have hrg := rr_good (β8 f g) (cube8 f g res)
  have hm : many 8 = 256 := by decide
  rw [hrr8, Int.one_mul, hm] at hrg
  unfold cntGood; omega

/-- **Theorem 1 (`rank8_barycenters_paired`)**: For EVERY global rank-8 balanced NL-242 half pair,
    1. `(pb + pc) % 4 = 2` and `pb % 2 = pc % 2` (so the two odd classes are `{A, D}` or `{B, C}`);
    2. `barycenter (clsB f g) = barycenter (clsC f g)` and
       `barycenter (clsA f g) = barycenter (clsD f g)` — the two odd barycenters ALWAYS coincide!
    3. For every `w ≠ zero 8`,
       `((halfCnt w B + halfCnt w C) / 2) % 2 = if dot 8 w (barycenter A ⊕ barycenter C) then 1 else 0`. -/
theorem rank8_barycenters_paired (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (hrr8 : rr (β8 f g) = 1) :
    (pb f g + pc f g) % 4 = 2 ∧
    pb f g % 2 = pc f g % 2 ∧
    barycenter (clsB f g) = barycenter (clsC f g) ∧
    barycenter (clsA f g) = barycenter (clsD f g) ∧
    (∀ w : W 8, w ≠ zero 8 →
      ((halfCnt w (clsB f g) + halfCnt w (clsC f g)) / 2) % 2 =
        if dot 8 w (add 8 (barycenter (clsA f g)) (barycenter (clsC f g))) then 1 else 0) := by
  have hmass := profile_mass f g res cap
  have hodd_cnt : (cnt (clsA f g) + cnt (clsC f g)) % 2 = 1 :=
    (Balanced242Parity.rank8_iff_k_odd f g res cap).1 (cntGood_256_of_rr1 f g res hrr8)
  have hpa : (pa f g : Int) = cnt (clsA f g) := Int.toNat_of_nonneg (cnt_nonneg _)
  have hpb : (pb f g : Int) = cnt (clsB f g) := Int.toNat_of_nonneg (cnt_nonneg _)
  have hpc : (pc f g : Int) = cnt (clsC f g) := Int.toNat_of_nonneg (cnt_nonneg _)
  have hodd : (pa f g + pc f g) % 2 = 1 := by omega
  have hmod8 : (6 * pa f g + 3 * pb f g + 5 * pc f g) % 8 = 0 := by omega
  have hbc4 : (pb f g + pc f g) % 4 = 2 := by omega
  have hbc2 : pb f g % 2 = pc f g % 2 := by omega
  have hbarBC : barycenter (clsB f g) = barycenter (clsC f g) := by
    apply dot_eq_all_implies_eq; intro w
    by_cases hw : w = zero 8
    · subst hw; rw [dot_zero, dot_zero]
    · have hl := (rank8_half_mod_laws f g res cap hrr8 w hw).2.1
      have hB := halfCnt_mod2_eq_dot_barycenter w (clsB f g)
      have hC := halfCnt_mod2_eq_dot_barycenter w (clsC f g)
      cases h1 : dot 8 w (barycenter (clsB f g)) <;> cases h2 : dot 8 w (barycenter (clsC f g)) <;>
        rw [h1] at hB <;> rw [h2] at hC <;> simp at hB hC <;> first | rfl | omega
  have hbarAD : barycenter (clsA f g) = barycenter (clsD f g) := by
    apply dot_eq_all_implies_eq; intro w
    by_cases hw : w = zero 8
    · subst hw; rw [dot_zero, dot_zero]
    · have hl := (rank8_half_mod_laws f g res cap hrr8 w hw).2.1
      have hsum := halfCnt_sum_all_classes f g res cap w hw
      have hA := halfCnt_mod2_eq_dot_barycenter w (clsA f g)
      have hD := halfCnt_mod2_eq_dot_barycenter w (clsD f g)
      cases h1 : dot 8 w (barycenter (clsA f g)) <;> cases h2 : dot 8 w (barycenter (clsD f g)) <;>
        rw [h1] at hA <;> rw [h2] at hD <;> simp at hA hD <;> first | rfl | omega
  have hqF : ∀ w : W 8, w ≠ zero 8 →
      ((halfCnt w (clsB f g) + halfCnt w (clsC f g)) / 2) % 2 =
        if dot 8 w (add 8 (barycenter (clsA f g)) (barycenter (clsC f g))) then 1 else 0 := by
    intro w hw
    obtain ⟨_, hyz2, hm8⟩ := rank8_half_mod_laws f g res cap hrr8 w hw
    have hA := halfCnt_mod2_eq_dot_barycenter w (clsA f g)
    have hC := halfCnt_mod2_eq_dot_barycenter w (clsC f g)
    rw [dot_right]
    cases h1 : dot 8 w (barycenter (clsA f g)) <;> cases h2 : dot 8 w (barycenter (clsC f g)) <;>
      rw [h1] at hA <;> rw [h2] at hC <;> simp at hA hC ⊢ <;> omega
  exact ⟨hbc4, hbc2, hbarBC, hbarAD, hqF⟩

/-- **Corollary (`rank8_a0_far_yz_div4`)**: Whenever `pa f g = 0` at rank 8, translating by
    `P = barycenter (clsC f g)` makes every nonzero hyperplane's far-side counts satisfy
    `y % 2 = 0`, `z % 2 = 0`, AND `(y + z) % 4 = 0`! -/
theorem rank8_a0_far_yz_div4 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (hrr8 : rr (β8 f g) = 1) (ha0 : pa f g = 0) :
    let P := barycenter (clsC f g)
    ∀ w : W 8, w ≠ zero 8 →
      halfCnt w (translate (clsB f g) P) % 2 = 0 ∧
      halfCnt w (translate (clsC f g) P) % 2 = 0 ∧
      (halfCnt w (translate (clsB f g) P) + halfCnt w (translate (clsC f g) P)) % 4 = 0 := by
  intro P w hw
  have hodd_cnt : (cnt (clsA f g) + cnt (clsC f g)) % 2 = 1 :=
    (Balanced242Parity.rank8_iff_k_odd f g res cap).1 (cntGood_256_of_rr1 f g res hrr8)
  have hpaI : (pa f g : Int) = cnt (clsA f g) := Int.toNat_of_nonneg (cnt_nonneg _)
  have hpbI : (pb f g : Int) = cnt (clsB f g) := Int.toNat_of_nonneg (cnt_nonneg _)
  have hpcI : (pc f g : Int) = cnt (clsC f g) := Int.toNat_of_nonneg (cnt_nonneg _)
  have hodd : (pa f g + pc f g) % 2 = 1 := by omega
  have hc_odd : (suppList (clsC f g)).length % 2 = 1 := by
    have h1 := suppList_length_eq_cnt_nat (clsC f g)
    omega
  have hz2 : halfCnt w (translate (clsC f g) P) % 2 = 0 :=
    barycenter_translate_odd (clsC f g) hc_odd w
  have ha_empty : ∀ x, clsA f g x = false := by
    intro x
    have hcnt0 : cnt (clsA f g) = 0 := by omega
    cases hx : clsA f g x
    · rfl
    · exfalso
      have hge := Balanced242SectionFacts.point_le_total 8 (Balanced242Reduction.ind (clsA f g))
        (fun y => by unfold Balanced242Reduction.ind; split <;> omega) x
      change (if clsA f g x then (1 : Int) else 0) ≤ cnt (clsA f g) at hge
      rw [hx] at hge; simp only [if_true] at hge; omega
  have hAx0 : halfCnt w (clsA f g) = 0 := by
    have h1 := halfCnt_eq_total_true w (clsA f g)
    have h0 : (fun a => if clsA f g a && dot 8 w a then (1 : Int) else 0) = fun _ => 0 := by
      funext a; rw [ha_empty a]; rfl
    rw [h0, total_zero] at h1; omega
  obtain ⟨_, hyz2, hm8⟩ := rank8_half_mod_laws f g res cap hrr8 w hw
  have hsumB := halfCnt_add_false w (clsB f g)
  have hsumC := halfCnt_add_false w (clsC f g)
  have hlenB : ((suppList (clsB f g)).length : Int) = (pb f g : Int) := by
    rw [suppList_length_eq_cnt_nat]; exact hpbI.symm
  have hlenC : ((suppList (clsC f g)).length : Int) = (pc f g : Int) := by
    rw [suppList_length_eq_cnt_nat]; exact hpcI.symm
  have hmass := profile_mass f g res cap
  have hgm8 : (3 * pb f g + 5 * pc f g) % 8 = 0 := by omega
  have hgb2 : (pb f g + pc f g) % 2 = 0 := by omega
  rw [halfCnt_translate] at hz2
  rw [halfCnt_translate, halfCnt_translate]
  cases hdw : dot 8 w P <;> simp only [hdw, Bool.false_eq_true, if_false, if_true] at hz2 ⊢
  · exact ⟨by omega, hz2, by omega⟩
  · exact ⟨by omega, hz2, by omega⟩

/-! ## Part 2: Unconditional 7-variable rank-6 `y + z ≠ 18` obstruction -/

private theorem exists_dot_true : ∀ {n : Nat} (r : W n), r ≠ zero n → ∃ u : W n, dot n u r = true
  | 0, (), hr => absurd rfl hr
  | m + 1, (true, r'), _ => ⟨(true, zero m), by simp [dot, dot_zero]⟩
  | m + 1, (false, r'), hr => by
    have hr' : r' ≠ zero m := fun h => hr (by rw [h]; rfl)
    obtain ⟨u', hu'⟩ := exists_dot_true r' hr'
    exact ⟨(false, u'), by simp [dot, hu']⟩

private theorem secPt_false_add : ∀ (m : Nat) (u : W (m + 1)), u ≠ zero (m + 1) →
    ∀ (x y : W m), secPt m u false (add m x y) = add (m + 1) (secPt m u false x) (secPt m u false y)
  | 0, (true, ()), _, (), () => by rw [secPt_true]; rfl
  | 0, (false, ()), hu, _, _ => absurd rfl hu
  | k + 1, (true, u'), _, x, y => by
    rw [secPt_true, secPt_true, secPt_true, dot_right]
    simp only [Bool.false_xor]
    rfl
  | k + 1, (false, u'), hu, (bx, x'), (by_, y') => by
    have hu' : u' ≠ zero (k + 1) := fun h => hu (by rw [h]; rfl)
    show secPt (k + 1) (false, u') false (xor bx by_, add k x' y') =
      (xor bx by_, add (k + 1) (secPt k u' false x') (secPt k u' false y'))
    rw [secPt_false, secPt_false_add k u' hu' x' y']

private theorem dot_embedCompl_secPt_false :
    ∀ (m : Nat) (u : W (m + 1)), u ≠ zero (m + 1) → ∀ (v a : W m),
      dot (m + 1) (embedCompl u v) (secPt m u false a) = dot m v a
  | 0, _, _, (), () => by simp [embedCompl, dot, zero]
  | m + 1, (true, ur), _, v, a => by
    rw [secPt_true]; simp [embedCompl, dot]
  | m + 1, (false, ur), hu, (vb, vr), (ab, ar) => by
    have hur : ur ≠ zero (m + 1) := fun h => hu (by rw [h]; rfl)
    rw [secPt_false]
    show xor (vb && ab) (dot (m + 1) (embedCompl ur vr) (secPt m ur false ar)) =
      xor (vb && ab) (dot m vr ar)
    rw [dot_embedCompl_secPt_false m ur hur vr ar]

private theorem total_pair_radical {m : Nat} (u r : W (m + 1)) (hur : dot (m + 1) u r = true)
    (F : W (m + 1) → Int) :
    total (m + 1) F =
      total m (fun x => F (secPt m u false x) + F (add (m + 1) (secPt m u false x) r)) := by
  have hu : u ≠ zero (m + 1) := by intro hz; rw [hz, dot_zero] at hur; exact Bool.noConfusion hur
  have h1 := sec_sum m u hu F
  let G : W (m + 1) → Int := fun z => if dot (m + 1) u z then F z else 0
  have hG1 : total (m + 1) G = total m (fun x => F (secPt m u true x)) := by
    rw [sec_sum m u hu G]
    have h0 : total m (fun x => G (secPt m u false x)) = 0 := by
      rw [← total_zero m]; apply congrArg (total m); funext x
      dsimp only [G]; rw [secPt_dot m u hu false x]; rfl
    have h1' : total m (fun x => G (secPt m u true x)) = total m (fun x => F (secPt m u true x)) := by
      apply congrArg (total m); funext x
      dsimp only [G]; rw [secPt_dot m u hu true x]; rfl
    rw [h0, h1', Int.zero_add]
  have hG2 : total (m + 1) G = total m (fun x => F (add (m + 1) (secPt m u false x) r)) := by
    have hsh : total (m + 1) G = total (m + 1) (fun z => G (add (m + 1) z r)) := by
      rw [← sum_shift (m + 1) r G]
      apply congrArg (total (m + 1)); funext z; rw [add_comm]
    rw [hsh, sec_sum m u hu (fun z => G (add (m + 1) z r))]
    have h0 : total m (fun x => G (add (m + 1) (secPt m u false x) r)) =
        total m (fun x => F (add (m + 1) (secPt m u false x) r)) := by
      apply congrArg (total m); funext x
      dsimp only [G]; rw [dot_right, secPt_dot m u hu false x, hur]; rfl
    have h1' : total m (fun x => G (add (m + 1) (secPt m u true x) r)) = 0 := by
      rw [← total_zero m]; apply congrArg (total m); funext x
      dsimp only [G]; rw [dot_right, secPt_dot m u hu true x, hur]; rfl
    rw [h0, h1', Int.add_zero]
  rw [h1, ← hG1, hG2, ← total_add]

private theorem exists_nonzero_rad (β : W 7 → Bool) (hrr : rr β = 2) :
    ∃ r : W 7, r ≠ zero 7 ∧ rad β r = true := by
  cases hall : (worlds 7).all (fun d => decide (d = zero 7) || !rad β d)
  · obtain ⟨r, _, hr⟩ := all_false_exists _ _ hall
    have hne : r ≠ zero 7 := by
      intro hz; subst hz; simp at hr
    have hrad : rad β r = true := by
      cases h : rad β r
      · rw [h] at hr; simp at hr
      · rfl
    exact ⟨r, hne, hrad⟩
  · exfalso
    rw [List.all_eq_true] at hall
    have hle : rr β ≤ 1 := by
      have hpt (d : W 7) : bind (rad β d) ≤ hits (zero 7) d := by
        have hd := hall d (all_worlds 7 d)
        by_cases hz : d = zero 7
        · subst hz; unfold hits; simp only [if_true]
          cases rad β (zero 7) <;> decide
        · have hne : ¬ zero 7 = d := fun h => hz h.symm
          have hfalse : rad β d = false := by
            have hdec : decide (d = zero 7) = false := decide_eq_false hz
            rw [hdec, Bool.false_or] at hd
            cases h : rad β d <;> rw [h] at hd <;> simp_all
          unfold hits; simp only [hne, if_false, hfalse]; decide
      have hm := total_mono 7 _ _ hpt
      rw [diagonal] at hm
      exact hm
    omega

private theorem no_cube6_wt4 (g : W 6 → Bool) (hcg : Cube g)
    (hwt : total 6 (fun x => bind (g x)) = 4) : False := by
  have htr0 : transform (fun x => sign (g x)) (zero 6) = 56 := by
    unfold transform
    have hpt (x : W 6) : sign (g x) * chr (zero 6) x = 1 - 2 * bind (g x) := by
      simp only [chr, dot_zero, sign, Balanced242Plateau.ind]
      cases g x <;> decide
    rw [funext hpt, total_sub, total_const, total_scale, hwt]
    have hm : many 6 = 64 := by decide
    rw [hm]; omega
  have hsq := spec_good g hcg (zero 6)
  rw [htr0] at hsq
  have hm : many 6 = 64 := by decide
  rw [hm] at hsq
  have hgood0 : bind (good g (zero 6)) = 1 := by
    cases h : good g (zero 6)
    · rw [h] at hsq; change (56 : Int) * 56 = 64 * (rr g * 0) at hsq; omega
    · rfl
  rw [hgood0, Int.mul_one] at hsq
  have hrr49 : rr g = 49 := by omega
  have hdiv := rr_good g hcg
  rw [hrr49, hm] at hdiv
  have hmod : (49 * total 6 (fun y => bind (good g y))) % 49 = 0 := Int.mul_emod_right _ _
  rw [hdiv] at hmod
  omega

private theorem cube_diff_even (β : W 7 → Bool) (hc : Cube β) (A B C X : W 7) :
    differences [A, B, C] (fun z => bind (β z)) X % 2 = 0 := by
  have h8 := hc A B C X
  simp only [differences, Balanced242Plateau.ind]
  generalize β (add 7 A (add 7 B (add 7 C X))) = b7 at h8 ⊢
  generalize β (add 7 B (add 7 C X)) = b6 at h8 ⊢
  generalize β (add 7 A (add 7 C X)) = b5 at h8 ⊢
  generalize β (add 7 C X) = b4 at h8 ⊢
  generalize β (add 7 A (add 7 B X)) = b3 at h8 ⊢
  generalize β (add 7 B X) = b2 at h8 ⊢
  generalize β (add 7 A X) = b1 at h8 ⊢
  generalize β X = b0 at h8 ⊢
  revert h8; clear hc A B C X
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> decide

private theorem cube_of_diff_even (g : W 6 → Bool)
    (heven : ∀ u v w a : W 6,
      differences [u, v, w] (fun x => bind (g x)) a % 2 = 0) : Cube g := by
  intro u v w a
  have h := heven u v w a
  simp only [differences, Balanced242Plateau.ind] at h
  generalize g (add 6 u (add 6 v (add 6 w a))) = b7 at h ⊢
  generalize g (add 6 v (add 6 w a)) = b6 at h ⊢
  generalize g (add 6 u (add 6 w a)) = b5 at h ⊢
  generalize g (add 6 w a) = b4 at h ⊢
  generalize g (add 6 u (add 6 v a)) = b3 at h ⊢
  generalize g (add 6 v a) = b2 at h ⊢
  generalize g (add 6 u a) = b1 at h ⊢
  generalize g a = b0 at h ⊢
  revert h
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> decide

private theorem diff_const_zero {n : Nat} (p : W n) (ps : List (W n)) (c : Int) (a : W n) :
    differences (p :: ps) (fun _ => c) a = 0 := by
  simp only [differences, Int.sub_self]
  have h0 : ∀ (l : List (W n)) (x : W n), differences l (fun _ => (0 : Int)) x = 0 := by
    intro l; induction l with
    | nil => intro _; rfl
    | cons d r ih => intro x; simp only [differences, Int.sub_self, ih]
  exact h0 ps a

private theorem diff_mod_zero {n : Nat} (ds : List (W n)) (m : Int) (F : W n → Int)
    (hF : ∀ z, F z % m = 0) (a : W n) : differences ds F a % m = 0 := by
  induction ds generalizing F with
  | nil => exact hF a
  | cons d rest ih =>
    simp only [differences]
    exact ih (fun b => F (add n d b) - F b) (fun b => by rw [Int.sub_emod, hF, hF]; simp)

/-- **Theorem 2 (`no_section_yz_eq_18`)**: Unconditional 7-variable rank-6 quartic obstruction
    excluding `y + z = 18` (zero `SectionEnum`, zero `Classical.choice`). -/
theorem no_section_yz_eq_18 (D H : W 7 → Int) (hspec : ∀ a, transform D a = 2 * H a)
    (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7)
    (β : W 7 → Bool) (hc : Cube β) (hph : ∀ a, phase (H a) = sign (β a))
    (hrr : rr β = 2) :
    let y := total 7 (fun a => if (H a).natAbs = 5 then (1 : Int) else 0)
    let z := total 7 (fun a => if (H a).natAbs = 3 then (1 : Int) else 0)
    y + z ≠ 18 := by
  intro y z h18
  have hyz18 : total 7 (fun a => exc35 (H a)) = 18 := by
    rw [total_exc35_eq_bc' H]; exact h18
  obtain ⟨r, hr_ne, hr_rad⟩ := exists_nonzero_rad β hrr
  obtain ⟨u, hur⟩ := exists_dot_true r hr_ne
  have hu : u ≠ zero 7 := by intro hz; rw [hz, dot_zero] at hur; exact Bool.noConfusion hur
  let emb : W 6 → W 7 := secPt 6 u false
  let DF : W 6 → Int := fun x => exc35 (H (emb x)) - exc35 (H (add 7 (emb x) r))
  -- Step 1: Every Walsh coefficient `transform DF w` equals `±2`!
  have hDF_spec (w : W 6) : transform DF w = 2 ∨ transform DF w = -2 := by
    let v0 : W 7 := embedCompl u w
    let v : W 7 := if dot 7 v0 r then v0 else add 7 v0 u
    have hvr : dot 7 v r = true := by
      dsimp only [v]
      cases h : dot 7 v0 r
      · simp only [Bool.false_eq_true, if_false]
        rw [dot_comm 7 (add 7 v0 u) r, dot_right, dot_comm 7 r v0, dot_comm 7 r u, h, hur]; rfl
      · simp only [if_true]; exact h
    have hv_ne : v ≠ zero 7 := by intro hz; rw [hz, dot_zero] at hvr; exact Bool.noConfusion hvr
    have hv_np : perp β v = false := by
      cases hp : perp β v
      · rfl
      · exfalso
        have h0 := (perp_spec β).1 hp r hr_rad
        rw [hvr] at h0; exact Bool.noConfusion h0
    have hv_emb (x : W 6) : dot 7 v (emb x) = dot 6 w x := by
      dsimp only [v, v0, emb]
      have h0 := dot_embedCompl_secPt_false 6 u hu w x
      cases dot 7 (embedCompl u w) r
      · simp only [Bool.false_eq_true, if_false]
        rw [dot_comm 7 (add 7 (embedCompl u w) u) _, dot_right,
            dot_comm 7 _ (embedCompl u w), dot_comm 7 _ u,
            h0, secPt_dot 6 u hu false x, Bool.xor_false]
      · simp only [if_true]; exact h0
    have hway1 : total 7 (fun a => chr v a * exc35 (H a)) = transform DF w := by
      rw [total_pair_radical u r hur]
      unfold transform
      apply congrArg (total 6); funext x
      have hc0 : chr v (emb x) = chr w x := by unfold chr; rw [hv_emb x]
      have hc1 : chr v (add 7 (emb x) r) = -chr w x := by
        unfold chr; rw [dot_right, hv_emb x, hvr]
        cases dot 6 w x <;> decide
      dsimp only [DF, emb] at hc0 hc1 ⊢
      change chr v (secPt 6 u false x) * exc35 (H (secPt 6 u false x)) +
        chr v (add 7 (secPt 6 u false x) r) * exc35 (H (add 7 (secPt 6 u false x) r)) =
        (exc35 (H (secPt 6 u false x)) - exc35 (H (add 7 (secPt 6 u false x) r))) * chr w x
      rw [hc0, hc1, Int.sub_mul, Int.mul_comm (chr w x), Int.neg_mul, Int.mul_comm (chr w x)]
      omega
    have hway2 : total 7 (fun a => chr v a * exc35 (H a)) =
        total 6 (fun a => exc35 (H (secPt 6 v false a))) -
        total 6 (fun a => exc35 (H (secPt 6 v true a))) := by
      rw [sec_sum 6 v hv_ne]
      have h0 : total 6 (fun a => chr v (secPt 6 v false a) * exc35 (H (secPt 6 v false a))) =
          total 6 (fun a => exc35 (H (secPt 6 v false a))) := by
        apply congrArg (total 6); funext a
        unfold chr; rw [secPt_dot 6 v hv_ne false a]; simp [sign]
      have h1 : total 6 (fun a => chr v (secPt 6 v true a) * exc35 (H (secPt 6 v true a))) =
          -total 6 (fun a => exc35 (H (secPt 6 v true a))) := by
        have hpt (a : W 6) : chr v (secPt 6 v true a) * exc35 (H (secPt 6 v true a)) =
            (-1 : Int) * exc35 (H (secPt 6 v true a)) := by
          unfold chr; rw [secPt_dot 6 v hv_ne true a]; rfl
        rw [funext hpt, total_scale]; omega
      rw [h0, h1]; omega
    have hMM : (16 : Int) * 16 = many 7 * rr β := by rw [hrr]; decide
    have hside (d : Bool) :
        8 ≤ total 6 (fun a => exc35 (H (secPt 6 v d a))) ∧
        total 6 (fun a => exc35 (H (secPt 6 v d a))) % 2 = 0 := by
      let βd : W 6 → Bool := fun a => β (secPt 6 v d a)
      have hcd : Cube βd := sec_cube β hc v d
      have hplat (y : W 6) :
          transform (fun a => sign (βd a)) y = 0 ∨
          transform (fun a => sign (βd a)) y = 8 ∨
          transform (fun a => sign (βd a)) y = -8 := by
        have hlv := (section_levels β hc v hv_ne d 16 hMM y).2 hv_np
        change 2 * transform (fun a => sign (βd a)) y = 0 ∨
          2 * transform (fun a => sign (βd a)) y = 16 ∨
          2 * transform (fun a => sign (βd a)) y = -16 at hlv
        rcases hlv with h | h | h
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))
      have hrr6 : rr βd = 1 := by
        have h := rr_from_plateau' βd hcd 8 hplat
        have hm : many 6 = 64 := by decide
        rw [hm] at h; omega
      have hspec6 (a : W 6) : transform (secFun 6 v d D) a = 2 * H (secPt 6 v d a) := by
        rw [← sec_transform 6 v hv_ne d D a, hspec]
      have h6 := six_bc_ge_8 (secFun 6 v d D) (fun a => H (secPt 6 v d a)) hspec6
        (fun a => hH (secPt 6 v d a)) βd hcd (fun a => hph (secPt 6 v d a)) hrr6
      dsimp only at h6
      rw [total_exc35_eq_bc' (fun a => H (secPt 6 v d a))]
      exact h6
    have hsum18 := sec_sum 6 v hv_ne (fun a => exc35 (H a))
    rw [hyz18] at hsum18
    have hs0 := hside false
    have hs1 := hside true
    rw [← hway1, hway2]
    omega
  -- Step 2: Parseval gives `total 6 (fun x => DF x * DF x) = 4`, so `g x := (DF x != 0)` has weight 4!
  let g : W 6 → Bool := fun x => decide (DF x ≠ 0)
  have hDF_sq_eq (x : W 6) : DF x * DF x = bind (g x) := by
    dsimp only [DF, g, exc35, Balanced242Plateau.ind]
    split <;> split <;> decide
  have hwt4 : total 6 (fun x => bind (g x)) = 4 := by
    have hpar := Balanced242Reduction.parseval2 DF DF
    have hsq4 (w : W 6) : transform DF w * transform DF w = 4 := by
      rcases hDF_spec w with h | h <;> rw [h] <;> decide
    rw [funext hsq4, total_const, funext hDF_sq_eq] at hpar
    have hm : many 6 = 64 := by decide
    rw [hm] at hpar
    omega
  -- Step 3: Prove `Cube g` via `mod8_phase_exc` + 4th-order Walsh differences + `rad_shift`!
  have hcg : Cube g := by
    apply cube_of_diff_even
    intro a b c x
    let A : W 7 := emb a; let B : W 7 := emb b; let C : W 7 := emb c; let X : W 7 := emb x
    have hemb_add (p q : W 6) : emb (add 6 p q) = add 7 (emb p) (emb q) :=
      secPt_false_add 6 u hu p q
    let F7 : W 7 → Int := fun z => exc35 (H (add 7 r z)) - exc35 (H z)
    let Hdiff : W 7 → Int := fun z => H (add 7 r z) - H z
    let Pdiff : W 7 → Int := fun z => sign (β (add 7 r z)) - sign (β z)
    have hmod8 (z : W 7) : (Hdiff z - Pdiff z - 4 * F7 z) % 8 = 0 := by
      have m1 := mod8_phase_exc (H (add 7 r z)) (hH (add 7 r z)).1 (hH (add 7 r z)).2
      have m2 := mod8_phase_exc (H z) (hH z).1 (hH z).2
      rw [hph (add 7 r z)] at m1; rw [hph z] at m2
      dsimp only [Hdiff, Pdiff, F7]; omega
    -- 1. `differences [A, B, C] Hdiff X % 8 = 0` from `diff_transform_dvd [r, A, B, C] D X`:
    have hH8 : differences [A, B, C] Hdiff X % 8 = 0 := by
      have hd4 := diff_transform_dvd [r, A, B, C] D X
      rw [show transform D = fun z => 2 * H z from funext hspec, diff_scale] at hd4
      simp only [List.length_cons, List.length_nil] at hd4
      change (2 : Int) ^ 4 ∣ 2 * differences [A, B, C] Hdiff X at hd4
      obtain ⟨k, hk⟩ := hd4
      have hpow : (2 : Int) ^ (4 : Nat) = 16 := by decide
      rw [hpow] at hk
      omega
    -- 2. `differences [A, B, C] Pdiff X % 8 = 0` from `rad_shift` + `Cube β`:
    have hP8 : differences [A, B, C] Pdiff X % 8 = 0 := by
      let c0 : Bool := xor (β (zero 7)) (β r)
      have hsh (z : W 7) : β (add 7 r z) = xor (β z) c0 := by
        rw [add_comm 7 r z]
        have h := rad_shift β r hr_rad z
        dsimp only [c0]; rw [h, Bool.xor_assoc]
      cases hc0 : c0
      · have h0 : Pdiff = fun _ => 0 := by
          funext z; dsimp only [Pdiff]; rw [hsh z, hc0, Bool.xor_false]; omega
        rw [h0, diff_const_zero]; rfl
      · have hpt : Pdiff = fun z => (-2 : Int) + 4 * bind (β z) := by
          funext z; dsimp only [Pdiff, Balanced242Plateau.ind]; rw [hsh z, hc0]
          cases β z <;> decide
        have hpt' : Pdiff = fun z => 4 * bind (β z) - 2 := by
          funext z; rw [hpt]; dsimp only; omega
        rw [hpt', diff_sub, diff_scale, diff_const_zero, Int.sub_zero]
        have hev := cube_diff_even β hc A B C X
        omega
    -- 3. Combine to get `differences [A, B, C] F7 X % 2 = 0`:
    have hcomb := diff_mod_zero [A, B, C] 8 (fun z => Hdiff z - Pdiff z - 4 * F7 z) hmod8 X
    rw [diff_sub, diff_sub, diff_scale] at hcomb
    have hF2 : differences [A, B, C] F7 X % 2 = 0 := by omega
    have hmod_g (y : W 6) : (F7 (emb y) - bind (g y)) % 2 = 0 := by
      have hrc : add 7 r (emb y) = add 7 (emb y) r := add_comm 7 r (emb y)
      dsimp only [F7, g, DF, exc35, Balanced242Plateau.ind]
      rw [hrc]; split <;> split <;> decide
    have hF7_emb :
        differences [a, b, c] (fun y => F7 (emb y)) x = differences [A, B, C] F7 X := by
      simp only [differences, A, B, C, X, hemb_add]
    rw [← hF7_emb] at hF2
    have hdiff_sub := diff_sub [a, b, c] (fun y => F7 (emb y)) (fun y => bind (g y)) x
    have hdiff_mod := diff_mod_zero [a, b, c] 2 (fun y => F7 (emb y) - bind (g y)) hmod_g x
    rw [hdiff_sub] at hdiff_mod
    omega
  -- Step 4: Contradiction with `no_cube6_wt4`!
  exact no_cube6_wt4 g hcg hwt4

end Balanced242T96Quartic

#print axioms Balanced242T96Quartic.rank8_sec_rr_eq_2
#print axioms Balanced242T96Quartic.rank8_half_mod_laws
#print axioms Balanced242T96Quartic.rank8_barycenters_paired
#print axioms Balanced242T96Quartic.rank8_a0_far_yz_div4
#print axioms Balanced242T96Quartic.no_section_yz_eq_18
