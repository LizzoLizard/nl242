/-
  Balanced242T96Arith.lean — Unconditional Lean 4 formalization of the Walsh mod-16
  energy & Parseval dichotomy for `t = 96`, rank 8, profile `(0, 31, 39)`
  (`t96/check_03139.py` lines 1–16 & 53–63).

  Proves unconditionally (zero `SectionEnum`, zero `sorry`, zero `native_decide`, zero Mathlib)
  that for any balanced 9-variable NL242 function with `t = 96` and profile `(0, 31, 39)`:
    1. Every hyperplane section satisfies `3b + 5c ≡ 0 (mod 8)`, hence `b ≡ c (mod 8)`.
    2. For `fBC = 1_B - 1_C`, every Walsh coefficient satisfies `W_BC(w) ≡ 8 (mod 16)`,
       `W_BC(0) = -8`, `∑_w (W_BC(w)^2 - 64) = 1536`, and `|W_BC(w)| ≤ 40`.
    3. Exact spectral dichotomy:
       - EITHER there is a unique `w ≠ 0` with `|W_BC(w)| = 40` (and all other `|W_BC(v)| = 8`),
         which automatically has a side with `c ≤ 16` and `|2(b - c) + 8| = 40`;
       - OR `∀ w, |W_BC(w)| ≤ 24` (with total excess `1536 = 3 * 512`, i.e., exactly three 24s),
         and Parseval on `clsC` alone (`|C| = 39`) forces a nonzero hyperplane with a side
         having `c ≤ 16` and `|2(b - c) + 8| ≤ 24`.
-/
import Balanced242Farkas

namespace Balanced242T96Arith

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Reduction Balanced242SectionFacts
open Balanced242Krawtchouk (suppList halfCnt halfCntFalse halfCnt_zero halfCnt_add_false)
open Balanced242Farkas (suppList_length_eq_total halfCnt_eq_total halfCntFalse_eq_total)

private theorem clsB_clsC_disj (f g : Half) (x : W 8) : (clsB f g x && clsC f g x) = false := by
  unfold clsB clsC
  cases h : ((hi f g x).natAbs == 20)
  · rfl
  · have h20 : (hi f g x).natAbs = 20 := beq_iff_eq.mp h
    rw [h20]; decide

private theorem total_nonneg {n : Nat} (F : W n → Int) (h : ∀ x, 0 ≤ F x) : 0 ≤ total n F := by
  have hm := total_mono n (fun _ => (0 : Int)) F h
  rw [total_zero] at hm; exact hm

private theorem point_le_total' {n : Nat} (F : W n → Int) (h : ∀ x, 0 ≤ F x) (a : W n) :
    F a ≤ total n F :=
  Balanced242SectionFacts.point_le_total n F h a

private theorem exists_gt_of_total_gt {n : Nat} (F : W n → Int) (B : Int)
    (hgt : many n * B < total n F) : ∃ w : W n, B < F w := by
  have haux : ∀ (m : Nat) (G : W m → Int), many m * B < total m G → ∃ w : W m, B < G w := by
    intro m; induction m with
    | zero =>
      intro G h
      refine ⟨(), ?_⟩
      change (1 : Int) * B < G () at h
      omega
    | succ k ih =>
      intro G h
      have hm : many (k + 1) = 2 * many k := by unfold many; rw [Int.pow_succ]; omega
      change many (k + 1) * B < total k (fun x => G (false, x)) + total k (fun x => G (true, x)) at h
      rw [hm, Int.mul_assoc] at h
      if h0 : many k * B < total k (fun x => G (false, x)) then
        rcases ih (fun x => G (false, x)) h0 with ⟨w, hw⟩
        exact ⟨(false, w), hw⟩
      else
        have h1 : many k * B < total k (fun x => G (true, x)) := by omega
        rcases ih (fun x => G (true, x)) h1 with ⟨w, hw⟩
        exact ⟨(true, w), hw⟩
  exact haux n F hgt

private theorem total_split_point {n : Nat} (F : W n → Int) (a : W n) :
    total n F = F a + total n (fun x => if x = a then 0 else F x) := by
  have hpt (x : W n) : F x = F a * hits a x + (if x = a then 0 else F x) := by
    unfold hits
    if h : x = a then subst h; simp
    else have h' : a ≠ x := Ne.symm h; simp [h, h']
  have htot := congrArg (total n) (funext hpt)
  rw [total_add, total_scale, diagonal, Int.mul_one] at htot
  exact htot

private theorem transform_ind_eq (P : W 8 → Bool) (w : W 8) :
    transform (fun x => Balanced242Plateau.ind (P x)) w =
      ((suppList P).length : Int) - 2 * (halfCnt w P : Int) := by
  unfold transform
  rw [suppList_length_eq_total P, halfCnt_eq_total w P]
  have hpt (x : W 8) : Balanced242Plateau.ind (P x) * chr w x =
      Balanced242Plateau.ind (P x) - 2 * Balanced242Plateau.ind (P x && dot 8 w x) := by
    unfold chr; cases P x <;> cases dot 8 w x <;> decide
  rw [show (fun x => Balanced242Plateau.ind (P x) * chr w x) =
        fun x => Balanced242Plateau.ind (P x) - 2 * Balanced242Plateau.ind (P x && dot 8 w x) from funext hpt,
      total_sub, total_scale]

private theorem secCnt_eq_halfCnt (P : W 8 → Bool) (w : W 8) (hw : w ≠ zero 8) :
    secCnt P w true = (halfCnt w P : Int) ∧ secCnt P w false = (halfCntFalse w P : Int) := by
  have hT : secCnt P w true = total 8 (fun x => Balanced242Plateau.ind (P x && dot 8 w x)) := by
    unfold secCnt
    have hsec := Balanced242Hyperplane.sec_total 7 w hw true (fun x => Balanced242Plateau.ind (P x))
    change total 7 (fun a => Balanced242Plateau.ind (P (Balanced242Hyperplane.secPt 7 w true a))) = _
    rw [← hsec]; apply congrArg (total 8); funext x
    cases P x <;> cases dot 8 w x <;> decide
  have hF : secCnt P w false = total 8 (fun x => Balanced242Plateau.ind (P x && !dot 8 w x)) := by
    unfold secCnt
    have hsec := Balanced242Hyperplane.sec_total 7 w hw false (fun x => Balanced242Plateau.ind (P x))
    change total 7 (fun a => Balanced242Plateau.ind (P (Balanced242Hyperplane.secPt 7 w false a))) = _
    rw [← hsec]; apply congrArg (total 8); funext x
    cases P x <;> cases dot 8 w x <;> decide
  rw [halfCnt_eq_total, halfCntFalse_eq_total]
  exact ⟨hT, hF⟩

private theorem cnt_eq_suppList_len (P : W 8 → Bool) :
    cnt P = ((suppList P).length : Int) := by
  unfold cnt; rw [suppList_length_eq_total]; rfl

private theorem mod16_sq_cases (x : Int) (hmod : x % 16 = 8) :
    64 ≤ x * x ∧
    (x.natAbs = 8 ∨ x.natAbs = 24 ∨ x.natAbs = 40 ∨ 56 ≤ x.natAbs) ∧
    (x.natAbs = 8 → x * x - 64 = 0) ∧
    (x.natAbs = 24 → x * x - 64 = 512) ∧
    (x.natAbs = 40 → x * x - 64 = 1536) ∧
    (56 ≤ x.natAbs → 3072 ≤ x * x - 64) := by
  have hq : x = 16 * (x / 16) + 8 := by omega
  let k := x / 16
  have h16 : (16 * k) * (16 * k) = 256 * k * k := by
    calc (16 * k) * (16 * k) = 16 * (k * (16 * k)) := Int.mul_assoc 16 k (16 * k)
      _ = 16 * (16 * (k * k)) := by rw [Int.mul_left_comm k 16 k]
      _ = (16 * 16) * (k * k) := (Int.mul_assoc 16 16 (k * k)).symm
      _ = 256 * (k * k) := rfl
      _ = 256 * k * k := (Int.mul_assoc 256 k k).symm
  have hsq : x * x = 256 * k * k + 256 * k + 64 := by
    rw [hq]
    calc (16 * k + 8) * (16 * k + 8)
        = (16 * k) * (16 * k) + (16 * k) * 8 + (8 * (16 * k) + 8 * 8) := by
          rw [Int.add_mul, Int.mul_add, Int.mul_add]
      _ = 256 * k * k + 256 * k + 64 := by rw [h16]; omega
  have hkk : 0 ≤ k * k + k := by
    if hk : 0 ≤ k then
      have := Int.mul_nonneg hk hk; omega
    else
      have hk1 : 0 ≤ -(k + 1) := by omega
      have h1 : 0 ≤ (-k) * (-(k + 1)) := Int.mul_nonneg (by omega) hk1
      have h2 : (-k) * (-(k + 1)) = k * k + k := by
        rw [Int.neg_mul_neg, Int.mul_add, Int.mul_one]
      omega
  have h64 : 64 ≤ x * x := by
    have : 256 * k * k + 256 * k = 256 * (k * k + k) := by
      rw [Int.mul_add, Int.mul_assoc]
    omega
  have hcases : x.natAbs = 8 ∨ x.natAbs = 24 ∨ x.natAbs = 40 ∨ 56 ≤ x.natAbs := by
    if hk0 : k = 0 ∨ k = -1 then left; omega
    else if hk1 : k = 1 ∨ k = -2 then right; left; omega
    else if hk2 : k = 2 ∨ k = -3 then right; right; left; omega
    else right; right; right; omega
  refine ⟨h64, hcases, ?_, ?_, ?_, ?_⟩
  · intro h8
    have : x = 8 ∨ x = -8 := by omega
    rcases this with rfl | rfl <;> decide
  · intro h24
    have : x = 24 ∨ x = -24 := by omega
    rcases this with rfl | rfl <;> decide
  · intro h40
    have : x = 40 ∨ x = -40 := by omega
    rcases this with rfl | rfl <;> decide
  · intro h56
    if hp : 0 ≤ x then
      have h1 : 56 ≤ x := by omega
      have h2 : 56 * 56 ≤ x * x := Int.mul_le_mul h1 h1 (by decide) (by omega)
      omega
    else
      have h1 : 56 ≤ -x := by omega
      have h2 : 56 * 56 ≤ (-x) * (-x) := Int.mul_le_mul h1 h1 (by decide) (by omega)
      rw [Int.neg_mul_neg] at h2; omega

/-- Signed indicator `1_B - 1_C` for profile `(0, 31, 39)`. -/
def fBC (f g : Half) (x : W 8) : Int :=
  Balanced242Plateau.ind (clsB f g x) - Balanced242Plateau.ind (clsC f g x)

/-- Exact Walsh mod-16 congruence and Parseval excess `∑_w (W_BC(w)^2 - 64) = 1536`
    for `t = 96`, rank 8, profile `(0, 31, 39)`. -/
theorem t96_0_31_39_walsh_energy (f g : Half)
    (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)
    (ht : agreements f g % 2 = 0)
    (ha : cnt (clsA f g) = 0) (hb : cnt (clsB f g) = 31) (hc : cnt (clsC f g) = 39) :
    (∀ w : W 8, transform (fBC f g) w =
      -8 - 2 * ((halfCnt w (clsB f g) : Int) - (halfCnt w (clsC f g) : Int))) ∧
    (∀ w : W 8, transform (fBC f g) w % 16 = 8) ∧
    transform (fBC f g) (zero 8) = -8 ∧
    total 8 (fun w => transform (fBC f g) w * transform (fBC f g) w - 64) = 1536 := by
  have hlenA : (suppList (clsA f g)).length = 0 := by
    have := cnt_eq_suppList_len (clsA f g); omega
  have hlenB : (suppList (clsB f g)).length = 31 := by
    have := cnt_eq_suppList_len (clsB f g); omega
  have hlenC : (suppList (clsC f g)).length = 39 := by
    have := cnt_eq_suppList_len (clsC f g); omega
  have htr_eq (w : W 8) : transform (fBC f g) w =
      -8 - 2 * ((halfCnt w (clsB f g) : Int) - (halfCnt w (clsC f g) : Int)) := by
    have hsub : transform (fBC f g) w =
        transform (fun x => Balanced242Plateau.ind (clsB f g x)) w -
        transform (fun x => Balanced242Plateau.ind (clsC f g x)) w := by
      unfold transform fBC
      have hpt (x : W 8) : (Balanced242Plateau.ind (clsB f g x) - Balanced242Plateau.ind (clsC f g x)) * chr w x =
          Balanced242Plateau.ind (clsB f g x) * chr w x - Balanced242Plateau.ind (clsC f g x) * chr w x :=
        Int.sub_mul _ _ _
      rw [show (fun x => (Balanced242Plateau.ind (clsB f g x) - Balanced242Plateau.ind (clsC f g x)) * chr w x) =
            fun x => Balanced242Plateau.ind (clsB f g x) * chr w x - Balanced242Plateau.ind (clsC f g x) * chr w x
            from funext hpt, total_sub]
    rw [hsub, transform_ind_eq, transform_ind_eq, hlenB, hlenC]
    omega
  have htr0 : transform (fBC f g) (zero 8) = -8 := by
    rw [htr_eq (zero 8), halfCnt_zero, halfCnt_zero]; decide
  have hmod16 (w : W 8) : transform (fBC f g) w % 16 = 8 := by
    if hw : w = zero 8 then
      subst hw; rw [htr0]; decide
    else
      have hmass := hyperplane_mass f g res cap w hw true ht
      have hsecA := (secCnt_eq_halfCnt (clsA f g) w hw).1
      have hsecB := (secCnt_eq_halfCnt (clsB f g) w hw).1
      have hsecC := (secCnt_eq_halfCnt (clsC f g) w hw).1
      have hA0 : halfCnt w (clsA f g) = 0 := by
        have := Balanced242Krawtchouk.halfCnt_le w (clsA f g); omega
      rw [hsecA, hsecB, hsecC, hA0] at hmass
      have htr := htr_eq w
      omega
  have hpar := Balanced242Section0320.parseval (fBC f g)
  have hsq_pt (x : W 8) : fBC f g x * fBC f g x =
      Balanced242Plateau.ind (clsB f g x) + Balanced242Plateau.ind (clsC f g x) := by
    unfold fBC
    have hdisj := clsB_clsC_disj f g x
    cases hB : clsB f g x <;> cases hC : clsC f g x <;> simp_all [Balanced242Plateau.ind]
  have hsq_tot : total 8 (fun x => fBC f g x * fBC f g x) = 70 := by
    rw [show (fun x => fBC f g x * fBC f g x) =
          fun x => Balanced242Plateau.ind (clsB f g x) + Balanced242Plateau.ind (clsC f g x) from funext hsq_pt,
        total_add, ← suppList_length_eq_total, ← suppList_length_eq_total, hlenB, hlenC]
    decide
  rw [hsq_tot] at hpar
  have hm8 : many 8 = 256 := by decide
  rw [hm8] at hpar
  have hex : total 8 (fun w => transform (fBC f g) w * transform (fBC f g) w - 64) = 1536 := by
    rw [total_sub, total_const, hm8, hpar]; decide
  exact ⟨htr_eq, hmod16, htr0, hex⟩

/-- Parseval on `clsC` alone (`|C| = 39`): some nonzero hyperplane has `min(c, 39 - c) ≤ 16`. -/
theorem t96_0_31_39_small_C (C : W 8 → Bool) (hc : (suppList C).length = 39) :
    ∃ w : W 8, w ≠ zero 8 ∧ (halfCnt w C ≤ 16 ∨ halfCntFalse w C ≤ 16) := by
  let gC (x : W 8) : Int := Balanced242Plateau.ind (C x)
  have hpar := Balanced242Section0320.parseval gC
  have hsq_pt (x : W 8) : gC x * gC x = Balanced242Plateau.ind (C x) := by
    dsimp only [gC]; cases C x <;> decide
  have hsq_tot : total 8 (fun x => gC x * gC x) = 39 := by
    rw [show (fun x => gC x * gC x) = fun x => Balanced242Plateau.ind (C x) from funext hsq_pt,
        ← suppList_length_eq_total, hc]; rfl
  have hm8 : many 8 = 256 := by decide
  rw [hm8, hsq_tot] at hpar
  let F (w : W 8) : Int := if w = zero 8 then 0 else transform gC w * transform gC w
  have htr0 : transform gC (zero 8) = 39 := by
    dsimp only [gC]; rw [transform_ind_eq, hc, halfCnt_zero]; decide
  have hsplit := total_split_point (fun w => transform gC w * transform gC w) (zero 8)
  have hF_tot : total 8 F = 8463 := by
    dsimp only [F]
    rw [htr0] at hsplit; omega
  have hgt : many 8 * 25 < total 8 F := by rw [hm8, hF_tot]; decide
  rcases exists_gt_of_total_gt F 25 hgt with ⟨w, hwgt⟩
  have hw_nz : w ≠ zero 8 := by
    intro hz; subst hz; dsimp only [F] at hwgt; simp at hwgt
  dsimp only [F] at hwgt; simp only [hw_nz, if_false] at hwgt
  have htrw : transform gC w = 39 - 2 * (halfCnt w C : Int) := by
    dsimp only [gC]; rw [transform_ind_eq, hc]; rfl
  rw [htrw] at hwgt
  have hsum := halfCnt_add_false w C; rw [hc] at hsum
  refine ⟨w, hw_nz, ?_⟩
  have hc_bound : halfCnt w C ≤ 16 ∨ 23 ≤ halfCnt w C := by
    if h1 : halfCnt w C ≤ 16 then exact Or.inl h1
    else if h2 : 23 ≤ halfCnt w C then exact Or.inr h2
    else
      exfalso
      let d : Int := 39 - 2 * (halfCnt w C : Int)
      have hlo : -5 ≤ d := by dsimp only [d]; omega
      have hhi : d ≤ 5 := by dsimp only [d]; omega
      have hd_sq : d * d ≤ 25 := by
        if hd0 : 0 ≤ d then
          exact Int.mul_le_mul hhi hhi hd0 (by decide)
        else
          have h1' : -d ≤ 5 := by omega
          have h2' := Int.mul_le_mul h1' h1' (by omega) (by decide)
          rw [Int.neg_mul_neg] at h2'; exact h2'
      dsimp only [d] at hd_sq; omega
  rcases hc_bound with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (by omega)

/-- Complete unconditional spectral dichotomy for `t = 96`, rank 8, profile `(0, 31, 39)`
    (`t96/check_03139.py`):
    - Every Walsh coefficient satisfies `|W_BC(w)| ≤ 40`.
    - EITHER there is a unique `w ≠ 0` with `|W_BC(w)| = 40` (and all other `|W_BC(v)| = 8`),
      which automatically has a side with `c ≤ 16` and `|2(b - c) + 8| = 40` (single-40 branch);
    - OR `∀ w, |W_BC(w)| ≤ 24`, and there exists `w ≠ 0` with a side having `c ≤ 16` and
      `|2(b - c) + 8| ≤ 24` (three-24 branch). -/
theorem t96_0_31_39_dichotomy (f g : Half)
    (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)
    (ht : agreements f g % 2 = 0)
    (ha : cnt (clsA f g) = 0) (hb : cnt (clsB f g) = 31) (hc : cnt (clsC f g) = 39) :
    (∀ w : W 8, (transform (fBC f g) w).natAbs ≤ 40) ∧
    ((∃ w : W 8, w ≠ zero 8 ∧ (transform (fBC f g) w).natAbs = 40 ∧
        (∀ v : W 8, v ≠ w → (transform (fBC f g) v).natAbs = 8) ∧
        ∃ c : Bool, secCnt (clsC f g) w c ≤ 16 ∧
          (2 * (secCnt (clsB f g) w c - secCnt (clsC f g) w c) + 8).natAbs = 40) ∨
     ((∀ w : W 8, (transform (fBC f g) w).natAbs ≤ 24) ∧
        ∃ w : W 8, w ≠ zero 8 ∧ ∃ c : Bool, secCnt (clsC f g) w c ≤ 16 ∧
          (2 * (secCnt (clsB f g) w c - secCnt (clsC f g) w c) + 8).natAbs ≤ 24)) := by
  obtain ⟨htr_eq, hmod16, htr0, hex⟩ := t96_0_31_39_walsh_energy f g res cap ht ha hb hc
  have hlenB : (suppList (clsB f g)).length = 31 := by
    have := cnt_eq_suppList_len (clsB f g); omega
  have hlenC : (suppList (clsC f g)).length = 39 := by
    have := cnt_eq_suppList_len (clsC f g); omega
  let E (w : W 8) : Int := transform (fBC f g) w * transform (fBC f g) w - 64
  have hE_nn (w : W 8) : 0 ≤ E w := by
    have h := (mod16_sq_cases (transform (fBC f g) w) (hmod16 w)).1
    dsimp only [E]; omega
  have hle40 (w : W 8) : (transform (fBC f g) w).natAbs ≤ 40 := by
    have hm := mod16_sq_cases (transform (fBC f g) w) (hmod16 w)
    have hpt : E w ≤ 1536 := by
      have h1 := point_le_total' E hE_nn w
      dsimp only [E] at h1 ⊢; omega
    rcases hm.2.1 with h8 | h24 | h40 | h56
    · omega
    · omega
    · omega
    · exfalso; have := hm.2.2.2.2.2 h56; dsimp only [E] at hpt; omega
  have hside_eq (w : W 8) (hw : w ≠ zero 8) (c : Bool) :
      (2 * (secCnt (clsB f g) w c - secCnt (clsC f g) w c) + 8).natAbs =
        (transform (fBC f g) w).natAbs := by
    have hB := secCnt_eq_halfCnt (clsB f g) w hw
    have hC := secCnt_eq_halfCnt (clsC f g) w hw
    have hsumB := halfCnt_add_false w (clsB f g); rw [hlenB] at hsumB
    have hsumC := halfCnt_add_false w (clsC f g); rw [hlenC] at hsumC
    have htr := htr_eq w
    cases c
    · rw [hB.2, hC.2]; omega
    · rw [hB.1, hC.1]; omega
  refine ⟨hle40, ?_⟩
  let has40 : Bool := (worlds 8).any (fun w => decide ((transform (fBC f g) w).natAbs == 40))
  cases h40b : has40
  · right
    have hle24 (w : W 8) : (transform (fBC f g) w).natAbs ≤ 24 := by
      have hne40 : (transform (fBC f g) w).natAbs ≠ 40 := by
        intro heq
        have hany : (worlds 8).any (fun x => decide ((transform (fBC f g) x).natAbs == 40)) = true := by
          rw [List.any_eq_true]; exact ⟨w, all_worlds 8 w, by simp [heq]⟩
        dsimp only [has40] at h40b; rw [hany] at h40b; exact Bool.noConfusion h40b
      have hm := mod16_sq_cases (transform (fBC f g) w) (hmod16 w)
      have h40 := hle40 w
      rcases hm.2.1 with h8 | h24 | h40' | h56 <;> omega
    refine ⟨hle24, ?_⟩
    rcases t96_0_31_39_small_C (clsC f g) hlenC with ⟨w, hw, hc_small⟩
    have hC := secCnt_eq_halfCnt (clsC f g) w hw
    rcases hc_small with hT | hF
    · refine ⟨w, hw, true, ?_, ?_⟩
      · rw [hC.1]; omega
      · rw [hside_eq w hw true]; exact hle24 w
    · refine ⟨w, hw, false, ?_, ?_⟩
      · rw [hC.2]; omega
      · rw [hside_eq w hw false]; exact hle24 w
  · left
    dsimp only [has40] at h40b
    rw [List.any_eq_true] at h40b
    rcases h40b with ⟨w, _, hw40⟩
    simp only [decide_eq_true_eq, beq_iff_eq] at hw40
    have hw_nz : w ≠ zero 8 := by
      intro hz; subst hz; rw [htr0] at hw40; exact absurd hw40 (by decide)
    have hEw : E w = 1536 := (mod16_sq_cases _ (hmod16 w)).2.2.2.2.1 hw40
    have hrest_zero : total 8 (fun v => if v = w then 0 else E v) = 0 := by
      have hsp := total_split_point E w
      have hEt : total 8 E = 1536 := hex
      omega
    have hother (v : W 8) (hv : v ≠ w) : (transform (fBC f g) v).natAbs = 8 := by
      have hnn' : ∀ x, 0 ≤ (if x = w then (0 : Int) else E x) := by
        intro x
        split
        · decide
        · exact hE_nn x
      have hle0 := point_le_total' (fun x => if x = w then (0 : Int) else E x) hnn' v
      simp only [hv, if_false] at hle0
      have hEv0 : E v = 0 := by have := hE_nn v; omega
      have hm := mod16_sq_cases _ (hmod16 v)
      have h40 := hle40 v
      rcases hm.2.1 with h8 | h24 | h40' | h56
      · exact h8
      · exfalso; have := hm.2.2.2.1 h24; dsimp only [E] at hEv0; omega
      · exfalso; have := hm.2.2.2.2.1 h40'; dsimp only [E] at hEv0; omega
      · exfalso; omega
    have hB_le : halfCnt w (clsB f g) ≤ 31 := by
      have := Balanced242Krawtchouk.halfCnt_le w (clsB f g); omega
    have hC_sum := halfCnt_add_false w (clsC f g); rw [hlenC] at hC_sum
    have hC_sec := secCnt_eq_halfCnt (clsC f g) w hw_nz
    have htr := htr_eq w
    -- `| -8 - 2(b - c) | = 40` with `0 ≤ b ≤ 31` forces `c ≤ 15` (if `b-c = 16`) or `39-c ≤ 15` (if `b-c = -24`)!
    have hc_side : ∃ c : Bool, secCnt (clsC f g) w c ≤ 16 := by
      if hT : halfCnt w (clsC f g) ≤ 16 then
        exact ⟨true, by rw [hC_sec.1]; omega⟩
      else
        exact ⟨false, by rw [hC_sec.2]; omega⟩
    rcases hc_side with ⟨c, hc16⟩
    exact ⟨w, hw_nz, hw40, hother, c, hc16, by rw [hside_eq w hw_nz c]; exact hw40⟩

end Balanced242T96Arith

#print axioms Balanced242T96Arith.t96_0_31_39_walsh_energy
#print axioms Balanced242T96Arith.t96_0_31_39_small_C
#print axioms Balanced242T96Arith.t96_0_31_39_dichotomy
