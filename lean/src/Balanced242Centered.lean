/-
  Balanced242Centered.lean — Zero-Mathlib Lean 4 formalization of the centered-profile,
  barycenter/marker-center, residual-code, Griesmer, and sphere-packing machinery powering
  `t = 96` and `t = 98` (`t96/check_centered_profiles.py`, `rank8cp/center96.py`, `verify_center.py`):

    1. Shifted all-degree multivariate Krawtchouk theorem (`sum_triple_esym_shifted`,
       `kraw_triple_shifted_nonneg_and_mod`, `kraw_triple_shifted_deg1_eq`) for ALL
       dimensions `n`, ALL shifts `t : W n`, and ALL degrees `(i, j, l)` — odd and even.
    2. Barycenter / marker-center translation & puncturing invariants (`barycenter`,
       `translate`, `puncture`, `halfCnt_mod2_eq_dot_barycenter`, `barycenter_translate_odd`,
       `cut_sum_eq_half`) matching `rank8cp/center96.py` lines 15–46.
    3. Exact residual kernel coupling (`residual_kernel_counts`), the general binary
       **Griesmer bound** (`griesmer_bound`), and the **sphere-packing bound** for
       distance `≥ 3` (`sphere_packing_d3`), matching `t96/check_centered_profiles.py`.
    4. Verified computable Farkas engines:
       - `checkCenteredCert` / `centered_cert_refute` (origin-pinned & residual character sums)
       - `checkBarycenterCase` / `barycenter_case_refute` / `barycenter_profile_refute`
         (full shifted + unshifted + cut=128 barycenter case split).

  Zero Mathlib, zero `SectionEnum`, zero `sorry`, zero `native_decide`.
-/
import Balanced242Farkas

namespace Balanced242Centered

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Plateau
open Balanced242Krawtchouk (nz nz_total choose choose_zero choose_succ_succ choose_gt
  sumInt sumInt_append sumInt_map_scale sumInt_map_add sumInt_mul_sumInt sumInt_nonneg sumInt_zero
  kraw kraw_at_zero kraw_flip esym esym_zero xorList sublists esym_eq_kraw esym_eq_sublists
  suppList halfCnt halfCntFalse halfCnt_le halfCnt_zero halfCnt_add_false
  kraw_triple_nonneg_and_mod kraw_triple_deg2_eq)
open Balanced242Farkas (Triple KrawEntry chooseFast krawFast krawRowVal evalWeighted evalRhs farkas_refute)

/-! ## Part 1: Shifted All-Degree Multivariate Krawtchouk Theorem -/

private theorem total_sumInt {n : Nat} {α : Type} :
    ∀ (L : List α) (F : α → W n → Int),
      total n (fun v => sumInt (L.map (fun x => F x v))) =
        sumInt (L.map (fun x => total n (F x)))
  | [], _ => by simp [sumInt, total_zero]
  | a :: t, F => by
    simp only [List.map_cons, sumInt, total_add, total_sumInt t F]

private theorem sum_chr_eq {n : Nat} (u : W n) :
    total n (fun v => chr v u) = many n * (if u = zero n then 1 else 0) := by
  have h := identity_spectrum n u
  have heq : total n (fun v => chr v u) = total n (chr u) := by
    apply congrArg (total n); funext v; simp only [chr, dot_comm n v u]
  rw [heq]
  change total n (chr u) = _ at h
  rw [h]
  if hz : u = zero n then simp [hz] else simp [hz]

/-- Exact character-orthogonality formula for any shifted triple product of `esym` over `W n`. -/
theorem sum_triple_esym_shifted {n : Nat} (t : W n) (L1 L2 L3 : List (W n)) (i j l : Nat) :
    total n (fun v => chr v t * (esym v L1 i * esym v L2 j * esym v L3 l)) =
      many n * sumInt ((sublists i L1).map (fun S1 =>
        sumInt ((sublists j L2).map (fun S2 =>
          sumInt ((sublists l L3).map (fun S3 =>
            if add n t (add n (xorList S1) (add n (xorList S2) (xorList S3))) = zero n
            then (1 : Int) else 0)))))) := by
  have hexp (v : W n) :
      chr v t * (esym v L1 i * esym v L2 j * esym v L3 l) =
        sumInt ((sublists i L1).map (fun S1 =>
          sumInt ((sublists j L2).map (fun S2 =>
            sumInt ((sublists l L3).map (fun S3 =>
              chr v (add n t (add n (xorList S1) (add n (xorList S2) (xorList S3)))))))))) := by
    rw [esym_eq_sublists v L1 i, esym_eq_sublists v L2 j, esym_eq_sublists v L3 l,
        Int.mul_assoc (sumInt _),
        sumInt_mul_sumInt (sublists j L2) (sublists l L3),
        sumInt_mul_sumInt (sublists i L1) (sublists j L2),
        ← sumInt_map_scale (chr v t), List.map_map]
    congr 1; apply List.map_congr_left; intro S1 _
    dsimp only [Function.comp_def]
    rw [← sumInt_map_scale (chr v t), List.map_map]
    congr 1; apply List.map_congr_left; intro S2 _
    dsimp only [Function.comp_def]
    rw [← sumInt_map_scale (chr v (xorList S1)), ← sumInt_map_scale (chr v t), List.map_map, List.map_map]
    congr 1; apply List.map_congr_left; intro S3 _
    dsimp only [Function.comp_def]
    show chr v t * (chr v (xorList S1) * (chr v (xorList S2) * chr v (xorList S3))) =
      chr v (add n t (add n (xorList S1) (add n (xorList S2) (xorList S3))))
    rw [chr_add, chr_add, chr_add]
  rw [funext hexp, total_sumInt, ← sumInt_map_scale (many n), List.map_map]
  congr 1; apply List.map_congr_left; intro S1 _
  dsimp only [Function.comp_def]
  rw [total_sumInt, ← sumInt_map_scale (many n), List.map_map]
  congr 1; apply List.map_congr_left; intro S2 _
  dsimp only [Function.comp_def]
  rw [total_sumInt, ← sumInt_map_scale (many n), List.map_map]
  congr 1; apply List.map_congr_left; intro S3 _
  exact sum_chr_eq (add n t (add n (xorList S1) (add n (xorList S2) (xorList S3))))

/-- All-degree shifted multivariate Krawtchouk inequality and mod-`2^n` congruence. -/
theorem kraw_triple_shifted_nonneg_and_mod {n : Nat} (t : W n) (P Q R : W n → Bool) (i j l : Nat) :
    let a := (suppList P).length
    let b := (suppList Q).length
    let c := (suppList R).length
    let S := total n (fun v => nz v * (chr v t * (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l)))
    let dc := choose a i * choose b j * choose c l;
    -dc ≤ S ∧ (S + dc) % many n = 0 := by
  intro a b c S dc
  have hchr0 : chr (zero n) t = 1 := by simp [chr, dot_zero, sign]
  have hfull : total n (fun v => chr v t * (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l)) =
      S + dc := by
    have hnz := nz_total (fun v => chr v t * (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l))
    rw [hchr0, Int.one_mul, halfCnt_zero, halfCnt_zero, halfCnt_zero,
        kraw_at_zero, kraw_at_zero, kraw_at_zero] at hnz
    change S = total n _ - dc at hnz
    exact (Int.sub_add_cancel _ _).symm.trans (congrArg (· + dc) hnz.symm)
  have heq : total n (fun v => chr v t * (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l)) =
      total n (fun v => chr v t * (esym v (suppList P) i * esym v (suppList Q) j * esym v (suppList R) l)) := by
    apply congrArg (total n); funext v
    rw [esym_eq_kraw v (suppList P) i, esym_eq_kraw v (suppList Q) j, esym_eq_kraw v (suppList R) l]
    rfl
  rw [sum_triple_esym_shifted] at heq
  rw [hfull] at heq
  have hnn_inner : 0 ≤ sumInt ((sublists i (suppList P)).map (fun S1 =>
      sumInt ((sublists j (suppList Q)).map (fun S2 =>
        sumInt ((sublists l (suppList R)).map (fun S3 =>
          if add n t (add n (xorList S1) (add n (xorList S2) (xorList S3))) = zero n
          then (1 : Int) else 0)))))) := by
    apply sumInt_nonneg; intro x1 hx1
    rw [List.mem_map] at hx1; rcases hx1 with ⟨S1, _, rfl⟩
    apply sumInt_nonneg; intro x2 hx2
    rw [List.mem_map] at hx2; rcases hx2 with ⟨S2, _, rfl⟩
    apply sumInt_nonneg; intro x3 hx3
    rw [List.mem_map] at hx3; rcases hx3 with ⟨S3, _, rfl⟩
    split <;> decide
  have hmn : 0 ≤ many n := by have := many_pos n; omega
  have hprod : 0 ≤ S + dc := by rw [heq]; exact Int.mul_nonneg hmn hnn_inner
  have hmod : (S + dc) % many n = 0 := by rw [heq, Int.mul_emod_right]
  exact ⟨by omega, hmod⟩

private theorem sublists_zero {α : Type} (L : List α) : sublists 0 L = [[]] := by
  cases L <;> rfl

private theorem sublists_one_mem {α : Type} : ∀ {L : List α} {S : List α},
    S ∈ sublists 1 L → ∃ x, x ∈ L ∧ S = [x]
  | [], _, h => nomatch h
  | a :: t, S, h => by
    unfold sublists at h
    rw [List.mem_append] at h
    rcases h with htail | h1
    · rcases sublists_one_mem htail with ⟨x, hx, rfl⟩
      exact ⟨x, List.mem_cons_of_mem _ hx, rfl⟩
    · rw [List.mem_map] at h1
      rcases h1 with ⟨S', hS', rfl⟩
      rw [sublists_zero, List.mem_singleton] at hS'
      subst hS'; exact ⟨a, List.mem_cons_self _ _, rfl⟩

private theorem add_ne_zero_of_ne {n : Nat} {x y : W n} (hne : x ≠ y) : add n x y ≠ zero n := by
  intro hz
  apply hne
  have h1 : add n (add n x y) y = add n (zero n) y := congrArg (fun z => add n z y) hz
  rw [add_assoc', add_self, add_zero_right, add_zero_left] at h1
  exact h1

/-- Degree-1 shifted Krawtchouk exact equality: when `t ∉ P ∪ Q ∪ R`, NO 1-element subset
    has XOR equal to `t`, so `∑_{v ≠ 0} χ_v(t) K_i K_j K_l = -C(a, i) C(b, j) C(c, l)`. -/
theorem kraw_triple_shifted_deg1_eq {n : Nat} (t : W n) (P Q R : W n → Bool)
    (htP : P t = false) (htQ : Q t = false) (htR : R t = false)
    (i j l : Nat) (hdeg : i + j + l = 1) :
    let a := (suppList P).length
    let b := (suppList Q).length
    let c := (suppList R).length
    total n (fun v => nz v * (chr v t * (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l))) =
      -(choose a i * choose b j * choose c l) := by
  intro a b c
  have hchr0 : chr (zero n) t = 1 := by simp [chr, dot_zero, sign]
  have hfull : total n (fun v => chr v t * (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l)) =
      total n (fun v => nz v * (chr v t * (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l))) +
        choose a i * choose b j * choose c l := by
    have hnz := nz_total (fun v => chr v t * (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l))
    rw [hchr0, Int.one_mul, halfCnt_zero, halfCnt_zero, halfCnt_zero,
        kraw_at_zero, kraw_at_zero, kraw_at_zero] at hnz
    omega
  have heq : total n (fun v => chr v t * (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l)) =
      total n (fun v => chr v t * (esym v (suppList P) i * esym v (suppList Q) j * esym v (suppList R) l)) := by
    apply congrArg (total n); funext v
    rw [esym_eq_kraw v (suppList P) i, esym_eq_kraw v (suppList Q) j, esym_eq_kraw v (suppList R) l]
    rfl
  rw [sum_triple_esym_shifted] at heq
  have hzero : sumInt ((sublists i (suppList P)).map (fun S1 =>
      sumInt ((sublists j (suppList Q)).map (fun S2 =>
        sumInt ((sublists l (suppList R)).map (fun S3 =>
          if add n t (add n (xorList S1) (add n (xorList S2) (xorList S3))) = zero n
          then (1 : Int) else 0)))))) = 0 := by
    apply sumInt_zero; intro x1 hx1
    rw [List.mem_map] at hx1; rcases hx1 with ⟨S1, hS1, rfl⟩
    apply sumInt_zero; intro x2 hx2
    rw [List.mem_map] at hx2; rcases hx2 with ⟨S2, hS2, rfl⟩
    apply sumInt_zero; intro x3 hx3
    rw [List.mem_map] at hx3; rcases hx3 with ⟨S3, hS3, rfl⟩
    have hne : add n t (add n (xorList S1) (add n (xorList S2) (xorList S3))) ≠ zero n := by
      have hcases : (i = 1 ∧ j = 0 ∧ l = 0) ∨ (i = 0 ∧ j = 1 ∧ l = 0) ∨ (i = 0 ∧ j = 0 ∧ l = 1) := by omega
      rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · rcases sublists_one_mem hS1 with ⟨x, hx, rfl⟩
        rw [sublists_zero, List.mem_singleton] at hS2 hS3; subst hS2; subst hS3
        unfold suppList at hx; rw [List.mem_filter] at hx
        have htx : t ≠ x := fun h => by rw [← h, htP] at hx; exact Bool.noConfusion hx.2
        simpa [xorList, add_zero_right, add_zero_left] using add_ne_zero_of_ne htx
      · rcases sublists_one_mem hS2 with ⟨x, hx, rfl⟩
        rw [sublists_zero, List.mem_singleton] at hS1 hS3; subst hS1; subst hS3
        unfold suppList at hx; rw [List.mem_filter] at hx
        have htx : t ≠ x := fun h => by rw [← h, htQ] at hx; exact Bool.noConfusion hx.2
        simpa [xorList, add_zero_right, add_zero_left] using add_ne_zero_of_ne htx
      · rcases sublists_one_mem hS3 with ⟨x, hx, rfl⟩
        rw [sublists_zero, List.mem_singleton] at hS1 hS2; subst hS1; subst hS2
        unfold suppList at hx; rw [List.mem_filter] at hx
        have htx : t ≠ x := fun h => by rw [← h, htR] at hx; exact Bool.noConfusion hx.2
        simpa [xorList, add_zero_right, add_zero_left] using add_ne_zero_of_ne htx
    simp [hne]
  rw [hzero, Int.mul_zero] at heq
  omega

/-! ## Part 2: Barycenter, Translation, and Puncturing Invariants (`center96.py`) -/

/-- `F₂`-barycenter (XOR sum of all elements in `P`). -/
def barycenter {n : Nat} (P : W n → Bool) : W n := xorList (suppList P)

/-- Translate a predicate `P` by `s ∈ W n`: `translate P s y = P (y ⊕ s)`. -/
def translate {n : Nat} (P : W n → Bool) (s : W n) (y : W n) : Bool := P (add n y s)

/-- Remove a single point `s` from `P`. -/
def puncture {n : Nat} (P : W n → Bool) (s : W n) (y : W n) : Bool := P y && !decide (y = s)

private theorem dot_add_right {n : Nat} (w a b : W n) : dot n w (add n a b) = xor (dot n w a) (dot n w b) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rcases w with ⟨wb, wr⟩; rcases a with ⟨ab, ar⟩; rcases b with ⟨bb, br⟩
    simp only [dot, add, ih]
    cases wb <;> cases ab <;> cases bb <;> cases dot m wr ar <;> cases dot m wr br <;> rfl

private theorem dot_xorList {n : Nat} (w : W n) :
    ∀ (L : List (W n)),
      ((L.filter (fun a => dot n w a)).length % 2 = 1) ↔ dot n w (xorList L) = true
  | [] => by simp [xorList, dot_comm n w (zero n), dot_zero]
  | a :: t => by
    unfold xorList
    rw [dot_add_right]
    have ih := dot_xorList w t
    cases hda : dot n w a
    · simp only [List.filter_cons, hda, Bool.false_xor]
      exact ih
    · simp only [List.filter_cons, hda, if_true, List.length_cons, Bool.true_xor]
      cases hdt : dot n w (xorList t)
      · have hev : (t.filter (fun x => dot n w x)).length % 2 = 0 := by
          have : ¬ ((t.filter (fun x => dot n w x)).length % 2 = 1) := by intro h; rw [ih.mp h] at hdt; exact Bool.noConfusion hdt
          omega
        simp only [Bool.not_false, iff_true]; omega
      · have hodd : (t.filter (fun x => dot n w x)).length % 2 = 1 := ih.mpr hdt
        simp only [Bool.not_true, Bool.false_eq_true, iff_false]; omega

/-- Core barycenter parity law: for any `P` and `w`, `halfCnt w P % 2 = 1 ↔ dot n w (barycenter P) = true`. -/
theorem halfCnt_mod2_eq_dot_barycenter {n : Nat} (w : W n) (P : W n → Bool) :
    halfCnt w P % 2 = if dot n w (barycenter P) then 1 else 0 := by
  have h := dot_xorList w (suppList P)
  cases hd : dot n w (barycenter P)
  · simp only [Bool.false_eq_true, if_false]
    have hne : halfCnt w P % 2 ≠ 1 := fun h1 => by
      unfold barycenter at hd
      rw [h.mp h1] at hd; exact Bool.noConfusion hd
    omega
  · simp only [if_true]; exact h.mpr hd

private theorem suppList_length_eq_total_ind {n : Nat} (P : W n → Bool) :
    ((suppList P).length : Int) = total n (fun x => ind (P x)) := by
  have h := Balanced242Farkas.suppList_length_eq_total P
  exact h

private theorem halfCnt_eq_total_ind {n : Nat} (w : W n) (P : W n → Bool) :
    (halfCnt w P : Int) = total n (fun x => ind (P x && dot n w x)) := by
  unfold halfCnt suppList
  rw [List.filter_filter]
  have hfn : (fun a => dot n w a && P a) = (fun a => P a && dot n w a) :=
    funext (fun a => Bool.and_comm _ _)
  rw [hfn]
  exact suppList_length_eq_total_ind (fun x => P x && dot n w x)

private theorem halfCntFalse_eq_total_ind {n : Nat} (w : W n) (P : W n → Bool) :
    (halfCntFalse w P : Int) = total n (fun x => ind (P x && !dot n w x)) := by
  unfold halfCntFalse suppList
  rw [List.filter_filter]
  have hfn : (fun a => (!dot n w a) && P a) = (fun a => P a && !dot n w a) :=
    funext (fun a => Bool.and_comm _ _)
  rw [hfn]
  exact suppList_length_eq_total_ind (fun x => P x && !dot n w x)

/-- Translation preserves support size. -/
theorem suppList_translate_length {n : Nat} (P : W n → Bool) (s : W n) :
    (suppList (translate P s)).length = (suppList P).length := by
  have h1 := suppList_length_eq_total_ind (translate P s)
  have h2 := suppList_length_eq_total_ind P
  have hshift := sum_shift n s (fun x => ind (P x))
  have hcomm : (fun y => ind (translate P s y)) = fun y => ind (P (add n s y)) :=
    funext (fun y => by unfold translate; rw [add_comm])
  rw [hcomm, hshift] at h1; omega

/-- Translation preserves the unordered hyperplane split `{halfCnt, halfCntFalse}` at every `w`. -/
theorem halfCnt_translate {n : Nat} (w s : W n) (P : W n → Bool) :
    halfCnt w (translate P s) = if dot n w s then halfCntFalse w P else halfCnt w P := by
  have h1 := halfCnt_eq_total_ind w (translate P s)
  have hT := halfCnt_eq_total_ind w P
  have hF := halfCntFalse_eq_total_ind w P
  have hshift := sum_shift n s (fun x => ind (P x && dot n w (add n x s)))
  have hpt (y : W n) : ind (translate P s y && dot n w y) =
      ind (P (add n s y) && dot n w (add n (add n s y) s)) := by
    unfold translate
    rw [add_comm n s y, add_assoc', add_self, add_zero_right]
  rw [show (fun y => ind (translate P s y && dot n w y)) =
        fun y => ind (P (add n s y) && dot n w (add n (add n s y) s)) from funext hpt,
      hshift] at h1
  cases hs : dot n w s
  · simp only [Bool.false_eq_true, if_false]
    have heq (x : W n) : dot n w (add n x s) = dot n w x := by rw [dot_add_right, hs, Bool.xor_false]
    rw [show (fun x => ind (P x && dot n w (add n x s))) = fun x => ind (P x && dot n w x) from
      funext (fun x => by rw [heq x])] at h1
    omega
  · simp only [if_true]
    have heq (x : W n) : dot n w (add n x s) = !dot n w x := by rw [dot_add_right, hs, Bool.xor_true]
    rw [show (fun x => ind (P x && dot n w (add n x s))) = fun x => ind (P x && !dot n w x) from
      funext (fun x => by rw [heq x])] at h1
    omega

/-- If `|P|` is odd, translating `P` by its barycenter forces every half-count `halfCnt w P'` to be EVEN
    (justifying `if v4[ia] % 2: continue` in `rank8cp/center96.py`!). -/
theorem barycenter_translate_odd {n : Nat} (P : W n → Bool) (hodd : (suppList P).length % 2 = 1) (w : W n) :
    halfCnt w (translate P (barycenter P)) % 2 = 0 := by
  rw [halfCnt_translate]
  have hp := halfCnt_mod2_eq_dot_barycenter w P
  have hsum := halfCnt_add_false w P
  cases hd : dot n w (barycenter P)
  · rw [hd] at hp; simp only [Bool.false_eq_true, if_false] at hp ⊢; exact hp
  · rw [hd] at hp; simp only [if_true] at hp ⊢; omega

/-- Puncturing a point `s` decreases `|P|` by 1 iff `P s = true`. -/
theorem suppList_puncture_length {n : Nat} (P : W n → Bool) (s : W n) :
    (suppList (puncture P s)).length = (suppList P).length - (if P s then 1 else 0) := by
  have h1 := suppList_length_eq_total_ind (puncture P s)
  have h2 := suppList_length_eq_total_ind P
  have hpt (y : W n) : ind (puncture P s y) = ind (P y) - ind (P s) * hits s y := by
    unfold puncture hits
    if hy : s = y then subst hy; cases P s <;> simp [ind]
    else have hy' : y ≠ s := Ne.symm hy; simp [hy, hy']
  rw [funext hpt, total_sub, total_scale, diagonal, Int.mul_one] at h1
  cases hPs : P s
  · simp only [Bool.false_eq_true, if_false, Nat.sub_zero]
    rw [hPs] at h1; change ((suppList (puncture P s)).length : Int) = total n (fun y => ind (P y)) - 0 at h1
    omega
  · simp only [if_true]
    rw [hPs] at h1; change ((suppList (puncture P s)).length : Int) = total n (fun y => ind (P y)) - 1 at h1
    omega

/-- Puncturing `s` decreases `halfCnt w P` by 1 iff `P s = true ∧ dot n w s = true`. -/
theorem halfCnt_puncture {n : Nat} (w s : W n) (P : W n → Bool) :
    halfCnt w (puncture P s) = halfCnt w P - (if P s && dot n w s then 1 else 0) := by
  have h1 := halfCnt_eq_total_ind w (puncture P s)
  have h2 := halfCnt_eq_total_ind w P
  have hpt (y : W n) : ind (puncture P s y && dot n w y) =
      ind (P y && dot n w y) - ind (P s && dot n w s) * hits s y := by
    unfold puncture hits
    if hy : s = y then subst hy; cases P s <;> cases dot n w s <;> simp [ind]
    else have hy' : y ≠ s := Ne.symm hy; simp [hy, hy']
  rw [funext hpt, total_sub, total_scale, diagonal, Int.mul_one] at h1
  cases hPs : P s <;> cases hdw : dot n w s
  · rw [hPs, hdw] at h1; simp only [Bool.and_false, Bool.false_eq_true, if_false, Nat.sub_zero]
    change (halfCnt w (puncture P s) : Int) = total n (fun y => ind (P y && dot n w y)) - 0 at h1; omega
  · rw [hPs, hdw] at h1; simp only [Bool.false_and, Bool.false_eq_true, if_false, Nat.sub_zero]
    change (halfCnt w (puncture P s) : Int) = total n (fun y => ind (P y && dot n w y)) - 0 at h1; omega
  · rw [hPs, hdw] at h1; simp only [Bool.and_false, Bool.false_eq_true, if_false, Nat.sub_zero]
    change (halfCnt w (puncture P s) : Int) = total n (fun y => ind (P y && dot n w y)) - 0 at h1; omega
  · rw [hPs, hdw] at h1; simp only [Bool.and_true, if_true]
    change (halfCnt w (puncture P s) : Int) = total n (fun y => ind (P y && dot n w y)) - 1 at h1; omega

theorem puncture_self {n : Nat} (P : W n → Bool) (s : W n) : puncture P s s = false := by
  unfold puncture; simp

/-- For any nonzero marker `q ≠ 0` in `W n` (`n ≥ 1`), exactly `2^(n-1)` nonzero directions `w`
    satisfy `dot n w q = true` (`∑_{w ≠ 0} cut(w) = 128` for `n = 8` in `center96.py`!). -/
theorem cut_sum_eq_half {n : Nat} (q : W (n + 1)) (hq : q ≠ zero (n + 1)) :
    total (n + 1) (fun w => nz w * (if dot (n + 1) w q then (1 : Int) else 0)) = many n := by
  have hnz := nz_total (fun w => if dot (n + 1) w q then (1 : Int) else 0)
  rw [dot_zero] at hnz; simp only [Bool.false_eq_true, if_false, Int.sub_zero] at hnz
  rw [hnz]
  have hpt (w : W (n + 1)) : 2 * (if dot (n + 1) w q then (1 : Int) else 0) = 1 - chr w q := by
    unfold chr; cases dot (n + 1) w q <;> decide
  have htot := congrArg (total (n + 1)) (funext hpt)
  rw [total_scale, total_sub, total_const, Int.mul_one, sum_chr_eq q] at htot
  simp only [hq, if_false, Int.mul_zero, Int.sub_zero] at htot
  have hm : many (n + 1) = 2 * many n := by unfold many; rw [Int.pow_succ]; omega
  rw [hm] at htot; omega

/-! ## Part 3: Residual Kernel Coupling, Griesmer Bound, and Sphere-Packing Bound -/

/-- Exact residual kernel identity (`t96/check_centered_profiles.py` lines 110–119):
    restricting `P` to `ker(u) = {y : dot n u y = false}` satisfies
    `2 * halfCnt v P_ker + halfCnt u P = halfCnt v P + halfCnt (v ⊕ u) P`
    and `|halfCnt v P - halfCnt (v ⊕ u) P| ≤ halfCnt u P`. -/
theorem residual_kernel_counts {n : Nat} (P : W n → Bool) (u v : W n) :
    let Pker (y : W n) := P y && !dot n u y
    2 * halfCnt v Pker + halfCnt u P = halfCnt v P + halfCnt (add n v u) P ∧
    ((halfCnt v P : Int) - (halfCnt (add n v u) P : Int)).natAbs ≤ halfCnt u P := by
  intro Pker
  have hK := halfCnt_eq_total_ind v Pker
  have hU := halfCnt_eq_total_ind u P
  have hV := halfCnt_eq_total_ind v P
  have hVU := halfCnt_eq_total_ind (add n v u) P
  have hdot_add (y : W n) : dot n (add n v u) y = xor (dot n v y) (dot n u y) := by
    rw [dot_comm n (add n v u) y, dot_add_right, dot_comm n y v, dot_comm n y u]
  have hsum_pt (y : W n) :
      2 * ind (Pker y && dot n v y) + ind (P y && dot n u y) =
      ind (P y && dot n v y) + ind (P y && dot n (add n v u) y) := by
    dsimp only [Pker]; rw [hdot_add y]
    cases P y <;> cases dot n u y <;> cases dot n v y <;> decide
  have hsum_tot := congrArg (total n) (funext hsum_pt)
  rw [total_add, total_scale, total_add] at hsum_tot
  have h1 : 2 * halfCnt v Pker + halfCnt u P = halfCnt v P + halfCnt (add n v u) P := by omega
  have hdiff_le : total n (fun y => ind (P y && dot n v y) - ind (P y && dot n (add n v u) y)) ≤
      total n (fun y => ind (P y && dot n u y)) := by
    apply total_mono n; intro y; rw [hdot_add y]
    cases P y <;> cases dot n u y <;> cases dot n v y <;> decide
  have hdiff_ge : -total n (fun y => ind (P y && dot n u y)) ≤
      total n (fun y => ind (P y && dot n v y) - ind (P y && dot n (add n v u) y)) := by
    have hpt (y : W n) : -ind (P y && dot n u y) ≤
        ind (P y && dot n v y) - ind (P y && dot n (add n v u) y) := by
      rw [hdot_add y]
      cases P y <;> cases dot n u y <;> cases dot n v y <;> decide
    have hm := total_mono n _ _ hpt
    have hneg : total n (fun y => -ind (P y && dot n u y)) = -total n (fun y => ind (P y && dot n u y)) := by
      have h1 (y : W n) : -ind (P y && dot n u y) = (-1 : Int) * ind (P y && dot n u y) := by omega
      rw [funext h1, total_scale]; omega
    rw [hneg] at hm; exact hm
  rw [total_sub] at hdiff_le hdiff_ge
  exact ⟨h1, by omega⟩

/-- Codeword weight of `v ∈ W k` on a column multiset `cols : List (W k)`. -/
def codeWt {k : Nat} (v : W k) (cols : List (W k)) : Nat :=
  (cols.filter (fun x => dot k v x)).length

/-- Recursive Griesmer function `g(k, d) = ∑_{i=0}^{k-1} ⌈d / 2^i⌉`. -/
def griesmer : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, d => d + griesmer k ((d + 1) / 2)

private theorem codeWt_add_ge {k : Nat} (u v : W k) :
    ∀ (cols : List (W k)),
      2 * codeWt v (cols.filter (fun x => !dot k u x)) + codeWt u cols =
      codeWt v cols + codeWt (add k v u) cols
  | [] => rfl
  | x :: rest => by
    have ih := codeWt_add_ge u v rest
    have hd : dot k (add k v u) x = xor (dot k v x) (dot k u x) := by
      rw [dot_comm k (add k v u) x, dot_add_right, dot_comm k x v, dot_comm k x u]
    unfold codeWt at ih ⊢
    cases hu : dot k u x <;> cases hv : dot k v x <;>
      simp only [List.filter_cons, hu, hv, hd, Bool.not_false, Bool.not_true,
        Bool.xor_false, Bool.xor_true, Bool.false_xor, Bool.true_xor,
        Bool.false_eq_true, if_true, if_false, List.length_cons] <;> omega

private theorem codeWt_filter_len {k : Nat} (u : W k) :
    ∀ (cols : List (W k)),
      (cols.filter (fun x => !dot k u x)).length + codeWt u cols = cols.length
  | [] => rfl
  | x :: rest => by
    have ih := codeWt_filter_len u rest
    unfold codeWt at ih ⊢
    cases hu : dot k u x <;> simp [List.filter_cons, hu] <;> omega

private theorem griesmer_mono : ∀ (k d1 d2 : Nat), d1 ≤ d2 → griesmer k d1 ≤ griesmer k d2
  | 0, _, _, _ => Nat.le_refl 0
  | k + 1, d1, d2, h => by
    unfold griesmer
    have ih := griesmer_mono k ((d1 + 1) / 2) ((d2 + 1) / 2) (by omega)
    omega

/-- Clean `W (k+1)` quotient via a SINGLE non-zero bit of `u`: for any `u ≠ 0`, `embedCompl u`
    embeds `W k → W (k+1)` linearly with `∀ a ≠ 0, embed a ≠ 0 ∧ embed a ≠ u`! -/
private def embedCompl : ∀ {m : Nat}, W (m + 1) → W m → W (m + 1)
  | 0, _, () => zero 1
  | _ + 1, (true, _), a => (false, a)
  | _ + 1, (false, ur), (ab, ar) => (ab, embedCompl ur ar)

private theorem embedCompl_ne_zero :
    ∀ {m : Nat} (u : W (m + 1)), u ≠ zero (m + 1) → ∀ (a : W m),
      a ≠ zero m → embedCompl u a ≠ zero (m + 1)
  | 0, _, _, (), ha => False.elim (ha rfl)
  | _ + 1, (true, _), _, _, ha => fun h => ha (congrArg Prod.snd h)
  | m + 1, (false, ur), hu, (ab, ar), ha => by
    intro h
    have hab : ab = false := congrArg Prod.fst h
    have har : embedCompl ur ar = zero (m + 1) := congrArg Prod.snd h
    have hur : ur ≠ zero (m + 1) := fun hz => hu (by rw [hz]; rfl)
    have har_ne : ar ≠ zero m := fun hz => ha (by rw [hab, hz]; rfl)
    exact embedCompl_ne_zero ur hur ar har_ne har

private theorem embedCompl_ne_u :
    ∀ {m : Nat} (u : W (m + 1)), u ≠ zero (m + 1) → ∀ (a : W m),
      embedCompl u a ≠ u
  | 0, (ub, ()), hu, () => by
    cases ub
    · exact False.elim (hu rfl)
    · intro h; exact Bool.noConfusion (congrArg Prod.fst h)
  | _ + 1, (true, _), _, _ => fun h => Bool.noConfusion (congrArg Prod.fst h)
  | m + 1, (false, ur), hu, (_, ar) => by
    have hur : ur ≠ zero (m + 1) := fun hz => hu (by rw [hz]; rfl)
    intro h; exact embedCompl_ne_u ur hur ar (congrArg Prod.snd h)

private def projCompl : ∀ {m : Nat}, W (m + 1) → W (m + 1) → W m
  | 0, _, _ => ()
  | _ + 1, (true, _), (_, xr) => xr
  | _ + 1, (false, ur), (xb, xr) => (xb, projCompl ur xr)

private theorem dot_embedCompl :
    ∀ {m : Nat} (u : W (m + 1)) (a : W m) (x : W (m + 1)),
      dot m a (projCompl u x) = dot (m + 1) (embedCompl u a) x
  | 0, _, (), _ => rfl
  | m + 1, (true, _), a, (_, xr) => by simp [embedCompl, projCompl, dot]
  | m + 1, (false, ur), (ab, ar), (xb, xr) => by
    simp only [embedCompl, projCompl, dot, dot_embedCompl ur ar xr]

private theorem add_embedCompl_ne_zero {m : Nat} (u : W (m + 1)) (hu : u ≠ zero (m + 1)) (a : W m) :
    add (m + 1) (embedCompl u a) u ≠ zero (m + 1) :=
  add_ne_zero_of_ne (embedCompl_ne_u u hu a)

private def minNonzeroWt {k : Nat} (cols : List (W (k + 1))) : W (k + 1) :=
  let nzW := (worlds (k + 1)).filter (fun w => !decide (w = zero (k + 1)))
  let rec go (best : W (k + 1)) : List (W (k + 1)) → W (k + 1)
    | [] => best
    | w :: rest => go (if codeWt w cols < codeWt best cols then w else best) rest
  go (true, zero k) nzW

private theorem minNonzeroWt_spec {k : Nat} (cols : List (W (k + 1))) :
    minNonzeroWt cols ≠ zero (k + 1) ∧
    ∀ w : W (k + 1), w ≠ zero (k + 1) → codeWt (minNonzeroWt cols) cols ≤ codeWt w cols := by
  have hgo : ∀ (L : List (W (k + 1))) (best : W (k + 1)),
      best ≠ zero (k + 1) → (∀ w, w ∈ L → w ≠ zero (k + 1)) →
      minNonzeroWt.go cols best L ≠ zero (k + 1) ∧
      codeWt (minNonzeroWt.go cols best L) cols ≤ codeWt best cols ∧
      ∀ w, w ∈ L → codeWt (minNonzeroWt.go cols best L) cols ≤ codeWt w cols := by
    intro L
    induction L with
    | nil => intro best hb _; exact ⟨hb, Nat.le_refl _, fun _ h => nomatch h⟩
    | cons x rest ih =>
      intro best hb hL
      have hx_nz : x ≠ zero (k + 1) := hL x (List.mem_cons_self _ _)
      have hrest_nz : ∀ w, w ∈ rest → w ≠ zero (k + 1) := fun w hw => hL w (List.mem_cons_of_mem _ hw)
      let best' := if codeWt x cols < codeWt best cols then x else best
      have hb' : best' ≠ zero (k + 1) := by dsimp only [best']; split <;> assumption
      have hrec := ih best' hb' hrest_nz
      have hle_b : codeWt best' cols ≤ codeWt best cols := by dsimp only [best']; split <;> omega
      have hle_x : codeWt best' cols ≤ codeWt x cols := by dsimp only [best']; split <;> omega
      refine ⟨hrec.1, Nat.le_trans hrec.2.1 hle_b, ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | htl
      · exact Nat.le_trans hrec.2.1 hle_x
      · exact hrec.2.2 w htl
  have ht_nz : ((true, zero k) : W (k + 1)) ≠ zero (k + 1) := fun h => Bool.noConfusion (congrArg Prod.fst h)
  have hall_nz : ∀ w, w ∈ (worlds (k + 1)).filter (fun w => !decide (w = zero (k + 1))) → w ≠ zero (k + 1) := by
    intro w hw; rw [List.mem_filter] at hw
    intro hz; subst hz; simp at hw
  have hres := hgo _ (true, zero k) ht_nz hall_nz
  refine ⟨hres.1, fun w hw => hres.2.2 w ?_⟩
  rw [List.mem_filter]; exact ⟨all_worlds (k + 1) w, by simp [hw]⟩

/-- The **Griesmer bound** for binary linear codes (`griesmer k d ≤ n`), proved constructively
    for all dimensions `k` and minimum distances `d` via residual code puncturing. -/
theorem griesmer_bound : ∀ (k d : Nat) (cols : List (W k)),
    (∀ v : W k, v ≠ zero k → d ≤ codeWt v cols) → griesmer k d ≤ cols.length
  | 0, _, _, _ => Nat.zero_le _
  | k + 1, d, cols, hmin => by
    let u := minNonzeroWt cols
    have hu := minNonzeroWt_spec cols
    let d0 := codeWt u cols
    have hd_le_d0 : d ≤ d0 := hmin u hu.1
    let resCols : List (W k) := (cols.filter (fun x => !dot (k + 1) u x)).map (projCompl u)
    have hres_len : resCols.length + d0 = cols.length := by
      dsimp only [resCols, d0]; rw [List.length_map]; exact codeWt_filter_len u cols
    have hres_wt (a : W k) :
        codeWt a resCols = codeWt (embedCompl u a) (cols.filter (fun x => !dot (k + 1) u x)) := by
      dsimp only [resCols, codeWt]
      rw [List.filter_map, List.length_map]
      congr 1; apply List.filter_congr; intro x _
      exact dot_embedCompl u a x
    have hres_min (a : W k) (ha : a ≠ zero k) : (d0 + 1) / 2 ≤ codeWt a resCols := by
      rw [hres_wt a]
      have h1 := codeWt_add_ge u (embedCompl u a) cols
      have hw1 : d0 ≤ codeWt (embedCompl u a) cols := hu.2 _ (embedCompl_ne_zero u hu.1 a ha)
      have hw2 : d0 ≤ codeWt (add (k + 1) (embedCompl u a) u) cols := hu.2 _ (add_embedCompl_ne_zero u hu.1 a)
      omega
    have ih := griesmer_bound k ((d0 + 1) / 2) resCols hres_min
    have hmono := griesmer_mono (k + 1) d d0 hd_le_d0
    unfold griesmer at hmono ⊢
    omega

/-- **Sphere-packing (Hamming) bound for binary linear codes of distance `≥ 3`**
    (matching `t96/check_centered_profiles.py` line 188: `(1 << 6) * (1 + 9) > 1 << 9`):
    if every nonzero `v ∈ W k` has `codeWt v cols ≥ 3`, then `2^k * (1 + cols.length) ≤ 2^cols.length`. -/
private def evalCode {k : Nat} (v : W k) : List (W k) → List Bool
  | [] => []
  | x :: rest => dot k v x :: evalCode v rest

private def flipAt : Nat → List Bool → List Bool
  | _, [] => []
  | 0, b :: rest => (!b) :: rest
  | i + 1, b :: rest => b :: flipAt i rest

private def hamDist : List Bool → List Bool → Nat
  | [], [] => 0
  | a :: as, b :: bs => (if a == b then 0 else 1) + hamDist as bs
  | _, _ => 0

private theorem evalCode_length {k : Nat} (v : W k) : ∀ (L : List (W k)), (evalCode v L).length = L.length
  | [] => rfl
  | _ :: t => by simp [evalCode, evalCode_length v t]

private theorem flipAt_length : ∀ (i : Nat) (L : List Bool), (flipAt i L).length = L.length
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, _ :: _ => rfl
  | i + 1, _ :: t => by simp [flipAt, flipAt_length i t]

private theorem hamDist_evalCode {k : Nat} (u v : W k) :
    ∀ (cols : List (W k)), hamDist (evalCode u cols) (evalCode v cols) = codeWt (add k u v) cols
  | [] => rfl
  | x :: rest => by
    have ih := hamDist_evalCode u v rest
    have hd : dot k (add k u v) x = xor (dot k u x) (dot k v x) := by
      rw [dot_comm k (add k u v) x, dot_add_right, dot_comm k x u, dot_comm k x v]
    change (if (dot k u x == dot k v x) = true then 0 else 1) +
        hamDist (evalCode u rest) (evalCode v rest) =
      ((x :: rest).filter (fun y => dot k (add k u v) y)).length
    rw [List.filter_cons, hd, ih]
    change (if (dot k u x == dot k v x) = true then 0 else 1) +
        (rest.filter (fun y => dot k (add k u v) y)).length = _
    cases dot k u x <;> cases dot k v x <;> simp <;> omega

private theorem hamDist_symm : ∀ (A B : List Bool), hamDist A B = hamDist B A
  | [], [] => rfl
  | a :: as, b :: bs => by
    unfold hamDist; rw [hamDist_symm as bs]; cases a <;> cases b <;> rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

private theorem hamDist_tri : ∀ (A B C : List Bool),
    A.length = B.length → B.length = C.length → hamDist A C ≤ hamDist A B + hamDist B C
  | [], [], [], _, _ => Nat.le_refl 0
  | a :: as, b :: bs, c :: cs, h1, h2 => by
    have ih := hamDist_tri as bs cs (by simp at h1; exact h1) (by simp at h2; exact h2)
    unfold hamDist; cases a <;> cases b <;> cases c <;> simp <;> omega
  | [], _ :: _, _, h1, _ => nomatch h1
  | _ :: _, [], _, h1, _ => nomatch h1
  | _ :: _, _ :: _, [], _, h2 => nomatch h2

private theorem hamDist_flipAt_le : ∀ (i : Nat) (A : List Bool), hamDist A (flipAt i A) ≤ 1
  | 0, [] => Nat.zero_le 1
  | _ + 1, [] => Nat.zero_le 1
  | 0, a :: as => by
    have hself : ∀ (L : List Bool), hamDist L L = 0 := by
      intro L; induction L with | nil => rfl | cons x t ih => unfold hamDist; cases x <;> simp [ih]
    unfold flipAt hamDist; rw [hself]; cases a <;> decide
  | i + 1, a :: as => by
    unfold flipAt hamDist
    have ih := hamDist_flipAt_le i as
    cases a <;> simp [ih]

private theorem flipAt_ne_self : ∀ (i : Nat) (A : List Bool), i < A.length → flipAt i A ≠ A
  | _, [], hi => nomatch hi
  | 0, a :: _, _ => fun h => by cases a <;> simp [flipAt] at h
  | i + 1, _ :: as, hi => fun h => flipAt_ne_self i as (by simp at hi; omega) (by injection h)

private theorem flipAt_inj : ∀ (i j : Nat) (A : List Bool),
    i < A.length → j < A.length → flipAt i A = flipAt j A → i = j
  | _, _, [], hi, _, _ => nomatch hi
  | 0, 0, _ :: _, _, _, _ => rfl
  | 0, j + 1, a :: _, _, _, heq => by cases a <;> simp [flipAt] at heq
  | i + 1, 0, a :: _, _, _, heq => by cases a <;> simp [flipAt] at heq
  | i + 1, j + 1, _ :: as, hi, hj, heq => by
    congr 1; apply flipAt_inj i j as (by simp at hi; omega) (by simp at hj; omega)
    injection heq

private def allBools : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBools n).map (false :: ·) ++ (allBools n).map (true :: ·)

private theorem allBools_len : ∀ (n : Nat), (allBools n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    unfold allBools; rw [List.length_append, List.length_map, List.length_map, allBools_len n]
    rw [Nat.pow_succ]; omega

private theorem mem_allBools : ∀ (n : Nat) (L : List Bool), L.length = n → L ∈ allBools n
  | 0, [], _ => List.mem_cons_self _ _
  | 0, _ :: _, h => nomatch h
  | n + 1, [], h => nomatch h
  | n + 1, b :: t, h => by
    unfold allBools; rw [List.mem_append, List.mem_map, List.mem_map]
    have ht : t ∈ allBools n := mem_allBools n t (by simp at h; exact h)
    cases b
    · left; exact ⟨t, ht, rfl⟩
    · right; exact ⟨t, ht, rfl⟩

private theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ (A B : List α), A.Nodup → (∀ x, x ∈ A → x ∈ B) → A.length ≤ B.length
  | [], _, _, _ => Nat.zero_le _
  | a :: as, B, hnd, hsub => by
    have haB : a ∈ B := hsub a (List.mem_cons_self _ _)
    have hnd_a : a ∉ as ∧ as.Nodup := List.nodup_cons.mp hnd
    have hsub' : ∀ x, x ∈ as → x ∈ B.erase a := by
      intro x hx
      have hne : x ≠ a := fun h => hnd_a.1 (h ▸ hx)
      exact List.mem_erase_of_ne hne |>.mpr (hsub x (List.mem_cons_of_mem _ hx))
    have ih := nodup_length_le_of_subset as (B.erase a) hnd_a.2 hsub'
    have her : (B.erase a).length + 1 = B.length := by
      have hle := List.length_erase_of_mem haB
      have hpos : 0 < B.length := List.length_pos_of_mem haB
      omega
    simp only [List.length_cons]; omega

private theorem nodup_append_of {α : Type} : ∀ {A B : List α},
    A.Nodup → B.Nodup → (∀ x, x ∈ A → x ∈ B → False) → (A ++ B).Nodup
  | [], _, _, hB, _ => hB
  | a :: as, B, hA, hB, hdisj => by
    rw [List.nodup_cons] at hA
    rw [List.cons_append, List.nodup_cons]
    refine ⟨?_, nodup_append_of hA.2 hB (fun x hx => hdisj x (List.mem_cons_of_mem _ hx))⟩
    intro hmem; rw [List.mem_append] at hmem
    rcases hmem with h1 | h2
    · exact hA.1 h1
    · exact hdisj a (List.mem_cons_self _ _) h2

private theorem nodup_map_inj {α β : Type} (f : α → β) (hinj : ∀ a b, f a = f b → a = b) :
    ∀ {L : List α}, L.Nodup → (L.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: t, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_inj f hinj hnd.2⟩
    intro hmem; rw [List.mem_map] at hmem; rcases hmem with ⟨b, hb, hfb⟩
    exact hnd.1 ((hinj b a hfb) ▸ hb)

private theorem worlds_nodup_c : ∀ (n : Nat), (worlds n).Nodup
  | 0 => by decide
  | m + 1 => by
    have ih := worlds_nodup_c m
    show ((worlds m).map (fun x => (false, x)) ++ (worlds m).map (fun x => (true, x))).Nodup
    apply nodup_append_of
      (nodup_map_inj (fun x => (false, x)) (fun _ _ h => congrArg Prod.snd h) ih)
      (nodup_map_inj (fun x => (true, x)) (fun _ _ h => congrArg Prod.snd h) ih)
    intro x hx hy
    rw [List.mem_map] at hx hy
    rcases hx with ⟨_, _, rfl⟩; rcases hy with ⟨_, _, hxy⟩
    exact Bool.noConfusion (congrArg Prod.fst hxy)

private theorem worlds_len_pow2 : ∀ (n : Nat), (worlds n).length = 2 ^ n
  | 0 => rfl
  | m + 1 => by
    show ((worlds m).map _ ++ (worlds m).map _).length = 2 ^ (m + 1)
    rw [List.length_append, List.length_map, List.length_map, worlds_len_pow2 m, Nat.pow_succ]
    omega

theorem sphere_packing_d3 (k : Nat) (cols : List (W k))
    (hd3 : ∀ v : W k, v ≠ zero k → 3 ≤ codeWt v cols) :
    2 ^ k * (1 + cols.length) ≤ 2 ^ cols.length := by
  let ball (v : W k) : List (List Bool) :=
    evalCode v cols :: (List.range cols.length).map (fun i => flipAt i (evalCode v cols))
  let allBalls : List (List Bool) := (worlds k).flatMap ball
  have hball_len (v : W k) : (ball v).length = 1 + cols.length := by
    dsimp only [ball]; simp; omega
  have hball_mem_dist (v : W k) (x : List Bool) (hx : x ∈ ball v) :
      x.length = cols.length ∧ hamDist (evalCode v cols) x ≤ 1 := by
    dsimp only [ball] at hx
    rcases List.mem_cons.mp hx with rfl | ht
    · refine ⟨evalCode_length v cols, ?_⟩
      have hself : ∀ (L : List Bool), hamDist L L = 0 := by
        intro L; induction L with | nil => rfl | cons b t ih => unfold hamDist; cases b <;> simp [ih]
      rw [hself]; omega
    · rw [List.mem_map] at ht; rcases ht with ⟨i, _, rfl⟩
      exact ⟨(flipAt_length i _).trans (evalCode_length v cols), hamDist_flipAt_le i _⟩
  have hball_nodup (v : W k) : (ball v).Nodup := by
    dsimp only [ball]
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro hmem; rw [List.mem_map] at hmem; rcases hmem with ⟨i, hi, heq⟩
      rw [List.mem_range] at hi
      exact flipAt_ne_self i (evalCode v cols) (by rw [evalCode_length]; exact hi) heq
    · have hnd_r : (List.range cols.length).Nodup := List.nodup_range cols.length
      -- injective on `List.range cols.length`
      have hmap_nd : ∀ (L : List Nat), L.Nodup → (∀ i, i ∈ L → i < cols.length) →
          (L.map (fun i => flipAt i (evalCode v cols))).Nodup := by
        intro L; induction L with
        | nil => intros; exact List.nodup_nil
        | cons i t ih =>
          intro hnd hlt
          rw [List.nodup_cons] at hnd
          rw [List.map_cons, List.nodup_cons]
          refine ⟨?_, ih hnd.2 (fun j hj => hlt j (List.mem_cons_of_mem _ hj))⟩
          intro hmem; rw [List.mem_map] at hmem; rcases hmem with ⟨j, hj, heq⟩
          have hij := flipAt_inj j i (evalCode v cols)
            (by rw [evalCode_length]; exact hlt j (List.mem_cons_of_mem _ hj))
            (by rw [evalCode_length]; exact hlt i (List.mem_cons_self _ _)) heq
          subst hij; exact hnd.1 hj
      exact hmap_nd _ hnd_r (fun i hi => List.mem_range.mp hi)
  have hball_disj (u v : W k) (hne : u ≠ v) (x : List Bool) (hu : x ∈ ball u) (hv : x ∈ ball v) : False := by
    have du := hball_mem_dist u x hu
    have dv := hball_mem_dist v x hv
    have htri := hamDist_tri (evalCode u cols) x (evalCode v cols)
      (by rw [evalCode_length, du.1]) (by rw [du.1, evalCode_length])
    rw [hamDist_symm x (evalCode v cols), hamDist_evalCode u v cols] at htri
    have hge3 := hd3 (add k u v) (add_ne_zero_of_ne hne)
    omega
  have hall_nodup : allBalls.Nodup := by
    have hflat : ∀ (L : List (W k)), L.Nodup → (L.flatMap ball).Nodup := by
      intro L; induction L with
      | nil => intros; exact List.nodup_nil
      | cons u rest ih =>
        intro hnd; rw [List.nodup_cons] at hnd
        rw [List.flatMap_cons]
        apply nodup_append_of (hball_nodup u) (ih hnd.2)
        intro x hx hy
        rw [List.mem_flatMap] at hy; rcases hy with ⟨v, hv, hxv⟩
        exact hball_disj u v (fun h => hnd.1 (h ▸ hv)) x hx hxv
    exact hflat (worlds k) (worlds_nodup_c k)
  have hall_sub : ∀ x, x ∈ allBalls → x ∈ allBools cols.length := by
    intro x hx; rw [List.mem_flatMap] at hx; rcases hx with ⟨v, _, hxv⟩
    exact mem_allBools cols.length x (hball_mem_dist v x hxv).1
  have hall_len : allBalls.length = 2 ^ k * (1 + cols.length) := by
    have hlen_flat : ∀ (L : List (W k)), (L.flatMap ball).length = L.length * (1 + cols.length) := by
      intro L; induction L with
      | nil => simp
      | cons u rest ih =>
        rw [List.flatMap_cons, List.length_append, hball_len u, ih, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [hlen_flat, worlds_len_pow2]
  have hle := nodup_length_le_of_subset allBalls (allBools cols.length) hall_nodup hall_sub
  rw [hall_len, allBools_len] at hle
  exact hle

/-! ## Part 4: Computable Centered & Barycenter Farkas Soundness (`checkCenteredCert`, `barycenter_case_refute`) -/

def centeredEntryValid (e : KrawEntry) : Bool :=
  let deg := e.1 + e.2.1 + e.2.2.1
  decide (deg ≤ 2) || decide (0 ≤ e.2.2.2)

def centeredRowRhs (dim a b c : Nat) (e : KrawEntry) : Int :=
  if e.1 + e.2.1 + e.2.2.1 == 0 then ((2 ^ dim : Nat) : Int) - 1
  else -(chooseFast a e.1 * chooseFast b e.2.1 * chooseFast c e.2.2.1)

def evalCenteredCol (a b c : Nat) (cert : List KrawEntry) (col : Triple) : Int :=
  cert.foldl (fun acc e => acc + e.2.2.2 * krawRowVal a b c e col) 0

def evalCenteredRhs (dim a b c : Nat) (cert : List KrawEntry) : Int :=
  cert.foldl (fun acc e => acc + e.2.2.2 * centeredRowRhs dim a b c e) 0

/-- Computable kernel verifier for `t96/check_centered_profiles.py`'s `check_character_sum`
    (allows ALL degrees — odd and even — with `deg ≤ 2` as equalities, `deg ≥ 3` as inequalities). -/
def checkCenteredCert (dim a b c : Nat) (weights : List Triple) (cert : List KrawEntry) : Bool :=
  cert.all centeredEntryValid &&
  decide (0 < evalCenteredRhs dim a b c cert) &&
  weights.all (fun w => decide (evalCenteredCol a b c cert w ≤ 0))

private theorem foldl_add_eq' {α : Type} (g : α → Int) :
    ∀ (L : List α) (init : Int),
      L.foldl (fun acc x => acc + g x) init = init + sumInt (L.map g)
  | [], init => by simp [sumInt]
  | x :: t, init => by simp only [List.foldl_cons, List.map_cons, sumInt, foldl_add_eq' g t]; omega

private theorem kraw_k0' (s x : Nat) : kraw s x 0 = 1 := by
  unfold kraw; simp [List.range_succ, sumInt, Balanced242Krawtchouk.altSign, choose_zero]

private theorem many_eq_pow2 : ∀ (n : Nat), many n = ((2 ^ n : Nat) : Int)
  | 0 => rfl
  | m + 1 => by
    unfold many
    have ih := many_eq_pow2 m
    unfold many at ih
    rw [Int.pow_succ, ih, Nat.pow_succ, Int.ofNat_mul]
    omega

private theorem chooseFast_eq_choose (n : Nat) : ∀ k, chooseFast n k = choose n k := by
  intro k; induction k with
  | zero => exact (choose_zero n).symm
  | succ k ih =>
    unfold chooseFast
    have hmul : ∀ r s, ((s + 1 : Nat) : Int) * choose r (s + 1) = ((r : Int) - (s : Int)) * choose r s := by
      intro r; induction r with
      | zero => intro s; cases s with | zero => decide | succ s' => simp [choose]
      | succ r' ihr =>
        intro s; cases s with
        | zero =>
          have h1 : ∀ u, choose u 1 = (u : Int) := by
            intro u; induction u with | zero => rfl | succ u' ihu => rw [choose_succ_succ, choose_zero, ihu]; omega
          rw [choose_zero, h1]; omega
        | succ s' =>
          rw [choose_succ_succ r' (s' + 1), choose_succ_succ r' s', Int.mul_add, Int.mul_add, ihr (s' + 1)]
          have hc1 : (((r' + 1 : Nat) : Int) - ((s' + 1 : Nat) : Int)) = (r' : Int) - (s' : Int) := by omega
          rw [hc1, ← ihr s']
          have hs1 : ((r' : Int) - ((s' + 1 : Nat) : Int)) + ((s' + 2 : Nat) : Int) = (r' : Int) + 1 := by omega
          have hs2 : ((r' : Int) - (s' : Int)) + ((s' + 1 : Nat) : Int) = (r' : Int) + 1 := by omega
          calc ((r' : Int) - ((s' + 1 : Nat) : Int)) * choose r' (s' + 1) + ((s' + 2 : Nat) : Int) * choose r' (s' + 1)
              = (((r' : Int) - ((s' + 1 : Nat) : Int)) + ((s' + 2 : Nat) : Int)) * choose r' (s' + 1) := by rw [Int.add_mul]
            _ = (((r' : Int) - (s' : Int)) + ((s' + 1 : Nat) : Int)) * choose r' (s' + 1) := by rw [hs1, hs2]
            _ = ((r' : Int) - (s' : Int)) * choose r' (s' + 1) + ((s' + 1 : Nat) : Int) * choose r' (s' + 1) := by rw [Int.add_mul]
    rw [ih, Int.mul_comm (choose n k), ← hmul n k, Int.mul_ediv_cancel_left _ (by omega)]

private theorem krawFast_eq_kraw (s x k : Nat) : krawFast s x k = kraw s x k := by
  unfold krawFast kraw; congr 1; apply List.map_congr_left; intro r _
  rw [chooseFast_eq_choose, chooseFast_eq_choose]

/-- Soundness of `checkCenteredCert` on ANY dimension `dim` and ANY pairwise-disjoint
    `(P, Q, R)` avoiding `zero dim` (matching `t96/check_centered_profiles.py`!). -/
theorem centered_cert_refute {dim : Nat} (P Q R : W dim → Bool)
    (hPQ : ∀ x, (P x && Q x) = false) (hPR : ∀ x, (P x && R x) = false) (hQR : ∀ x, (Q x && R x) = false)
    (h0P : P (zero dim) = false) (h0Q : Q (zero dim) = false) (h0R : R (zero dim) = false)
    (a b c : Nat)
    (ha : (suppList P).length = a) (hb : (suppList Q).length = b) (hc : (suppList R).length = c)
    (weights : List Triple)
    (hmem : ∀ w : W dim, w ≠ zero dim → (halfCnt w P, halfCnt w Q, halfCnt w R) ∈ weights)
    (cert : List KrawEntry)
    (hcheck : checkCenteredCert dim a b c weights cert = true) : False := by
  unfold checkCenteredCert at hcheck
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hvalid, hrhs_pos⟩, hcols_le⟩ := hcheck
  let classify (w : W dim) : Triple := (halfCnt w P, halfCnt w Q, halfCnt w R)
  let rows : List ((Triple → Int) × Int × Int) :=
    cert.map (fun e => (krawRowVal a b c e, centeredRowRhs dim a b c e, e.2.2.2))
  have hsound : ∀ r, r ∈ rows →
      (0 ≤ r.2.2 ∧ r.2.1 ≤ total dim (fun v => nz v * r.1 (classify v))) ∨
      total dim (fun v => nz v * r.1 (classify v)) = r.2.1 := by
    intro r hr
    rw [List.mem_map] at hr; rcases hr with ⟨e, he, rfl⟩
    have hv := hvalid e he
    unfold centeredEntryValid at hv
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hv
    have hrow_eq (w : W dim) : krawRowVal a b c e (classify w) =
        kraw a (halfCnt w P) e.1 * kraw b (halfCnt w Q) e.2.1 * kraw c (halfCnt w R) e.2.2.1 := by
      unfold krawRowVal; dsimp only [classify]; simp only [krawFast_eq_kraw]
    have hsum_eq : total dim (fun w => nz w * krawRowVal a b c e (classify w)) =
        total dim (fun w => nz w * (kraw a (halfCnt w P) e.1 * kraw b (halfCnt w Q) e.2.1 * kraw c (halfCnt w R) e.2.2.1)) := by
      apply congrArg (total dim); funext w; rw [hrow_eq w]
    rw [hsum_eq]
    if hd0 : e.1 + e.2.1 + e.2.2.1 = 0 then
      right
      have he1 : e.1 = 0 := by omega
      have he2 : e.2.1 = 0 := by omega
      have he3 : e.2.2.1 = 0 := by omega
      unfold centeredRowRhs
      simp only [hd0, beq_self_eq_true, if_true, he1, he2, he3]
      have h1 (w : W dim) : nz w * (kraw a (halfCnt w P) 0 * kraw b (halfCnt w Q) 0 * kraw c (halfCnt w R) 0) = nz w * 1 := by
        rw [kraw_k0', kraw_k0', kraw_k0']; simp
      rw [funext h1, nz_total (fun _ => (1 : Int)), total_const, Int.mul_one, many_eq_pow2]
    else
      unfold centeredRowRhs
      have hbeq : (e.1 + e.2.1 + e.2.2.1 == 0) = false := beq_false_of_ne hd0
      rw [hbeq]; simp only [Bool.false_eq_true, if_false, chooseFast_eq_choose]
      if hd1 : e.1 + e.2.1 + e.2.2.1 = 1 then
        right
        have h1 := kraw_triple_shifted_deg1_eq (zero dim) P Q R h0P h0Q h0R e.1 e.2.1 e.2.2.1 hd1
        dsimp only at h1; rw [ha, hb, hc] at h1
        have hchr (w : W dim) : chr w (zero dim) = 1 := by simp [chr, dot_comm dim w (zero dim), dot_zero, sign]
        simpa only [hchr, Int.one_mul] using h1
      else if hd2 : e.1 + e.2.1 + e.2.2.1 = 2 then
        right
        have h2 := kraw_triple_deg2_eq P Q R hPQ hPR hQR e.1 e.2.1 e.2.2.1 hd2
        dsimp only at h2; rw [ha, hb, hc] at h2; exact h2
      else
        left
        have hwt : 0 ≤ e.2.2.2 := by
          rcases hv with hle2 | hwt
          · exfalso; omega
          · exact hwt
        have hnn := (kraw_triple_nonneg_and_mod P Q R e.1 e.2.1 e.2.2.1).1
        rw [ha, hb, hc] at hnn; exact ⟨hwt, hnn⟩
  have heval_col (col : Triple) :
      evalWeighted (rows.map (fun r => (r.1, r.2.2))) col = evalCenteredCol a b c cert col := by
    unfold evalCenteredCol; rw [foldl_add_eq', Int.zero_add]
    clear hsound hcols_le hrhs_pos hvalid
    induction cert with
    | nil => rfl
    | cons e t ih => simp only [rows, List.map_cons, evalWeighted, sumInt] at ih ⊢; rw [ih]
  have heval_rhs : evalRhs (rows.map (fun r => (r.2.1, r.2.2))) = evalCenteredRhs dim a b c cert := by
    unfold evalCenteredRhs; rw [foldl_add_eq', Int.zero_add]
    clear hsound hcols_le hrhs_pos hvalid heval_col
    induction cert with
    | nil => rfl
    | cons e t ih => simp only [rows, List.map_cons, evalRhs, sumInt] at ih ⊢; rw [ih]
  exact farkas_refute classify weights hmem rows hsound
    (fun col hcol => by rw [heval_col col]; exact hcols_le col hcol)
    (by rw [heval_rhs]; exact hrhs_pos)

/-- Shifted-Krawtchouk Farkas entry `(i, j, l, shifted, weight)` for `rank8cp/center96.py`:
    `shifted = false` is `K_i K_j K_l`, `shifted = true` is `(1 - 2*cut) * K_i K_j K_l = χ_w(q_b) K_i K_j K_l`. -/
abbrev BaryEntry := Nat × Nat × Nat × Bool × Int

/-- A centered-barycenter column `(w_cnt, cut)` (`w_cnt = (x', y', z')`, `cut : Bool`). -/
abbrev BaryCol := Triple × Bool

def baryRowVal (a b c : Nat) (e : BaryEntry) (col : BaryCol) : Int :=
  let base := krawFast a col.1.1 e.1 * krawFast b col.1.2.1 e.2.1 * krawFast c col.1.2.2 e.2.2.1
  if e.2.2.2.1 then (if col.2 then -base else base) else base

def baryRowRhs (dim a b c : Nat) (e : BaryEntry) : Int :=
  let deg := e.1 + e.2.1 + e.2.2.1
  if deg == 0 then
    if e.2.2.2.1 then -1 else ((2 ^ dim : Nat) : Int) - 1
  else -(chooseFast a e.1 * chooseFast b e.2.1 * chooseFast c e.2.2.1)

def baryEntryValid (e : BaryEntry) : Bool :=
  let deg := e.1 + e.2.1 + e.2.2.1
  let shifted := e.2.2.2.1
  if deg == 0 then true
  else if deg == 1 then true
  else if deg == 2 && !shifted then true
  else decide (0 ≤ e.2.2.2.2)

def evalBaryCol (a b c : Nat) (cert : List BaryEntry) (col : BaryCol) : Int :=
  cert.foldl (fun acc e => acc + e.2.2.2.2 * baryRowVal a b c e col) 0

def evalBaryRhs (dim a b c : Nat) (cert : List BaryEntry) : Int :=
  cert.foldl (fun acc e => acc + e.2.2.2.2 * baryRowRhs dim a b c e) 0

/-- Computable verifier for any single `(ca, cb)` case of `rank8cp/center96.py`
    (combining count=255, cut=128 via `deg=0, shifted=true` since `∑_{w≠0} (1 - 2*cut) = 255 - 2*128 = -1`,
    unshifted Krawtchouk eqs/ineqs, and shifted Krawtchouk eqs/ineqs!). -/
def checkBaryCert (dim a b c : Nat) (cols : List BaryCol) (cert : List BaryEntry) : Bool :=
  cert.all baryEntryValid &&
  decide (0 < evalBaryRhs dim a b c cert) &&
  cols.all (fun col => decide (evalBaryCol a b c cert col ≤ 0))

/-- Soundness of `checkBaryCert` against punctured pairwise-disjoint `(Q0, Q1, Q2)` avoiding `{0, q_b}`
    (both `q_b = 0` coinciding case and `q_b ≠ 0` non-coinciding case!). -/
theorem bary_cert_refute {m : Nat} (qb : W (m + 1)) (hqb : qb ≠ zero (m + 1))
    (Q0 Q1 Q2 : W (m + 1) → Bool)
    (h01 : ∀ x, (Q0 x && Q1 x) = false) (h02 : ∀ x, (Q0 x && Q2 x) = false) (h12 : ∀ x, (Q1 x && Q2 x) = false)
    (h0_0 : Q0 (zero (m + 1)) = false) (h0_1 : Q1 (zero (m + 1)) = false) (h0_2 : Q2 (zero (m + 1)) = false)
    (hq_0 : Q0 qb = false) (hq_1 : Q1 qb = false) (hq_2 : Q2 qb = false)
    (a b c : Nat)
    (ha : (suppList Q0).length = a) (hb : (suppList Q1).length = b) (hc : (suppList Q2).length = c)
    (cols : List BaryCol)
    (hmem : ∀ w : W (m + 1), w ≠ zero (m + 1) →
      ((halfCnt w Q0, halfCnt w Q1, halfCnt w Q2), dot (m + 1) w qb) ∈ cols)
    (cert : List BaryEntry)
    (hcheck : checkBaryCert (m + 1) a b c cols cert = true) : False := by
  unfold checkBaryCert at hcheck
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hvalid, hrhs_pos⟩, hcols_le⟩ := hcheck
  let classify (w : W (m + 1)) : BaryCol := ((halfCnt w Q0, halfCnt w Q1, halfCnt w Q2), dot (m + 1) w qb)
  let rows : List ((BaryCol → Int) × Int × Int) :=
    cert.map (fun e => (baryRowVal a b c e, baryRowRhs (m + 1) a b c e, e.2.2.2.2))
  have hsound : ∀ r, r ∈ rows →
      (0 ≤ r.2.2 ∧ r.2.1 ≤ total (m + 1) (fun v => nz v * r.1 (classify v))) ∨
      total (m + 1) (fun v => nz v * r.1 (classify v)) = r.2.1 := by
    intro r hr
    rw [List.mem_map] at hr; rcases hr with ⟨e, he, rfl⟩
    have hv := hvalid e he
    let t : W (m + 1) := if e.2.2.2.1 then qb else zero (m + 1)
    have hrow_eq (w : W (m + 1)) : baryRowVal a b c e (classify w) =
        chr w t * (kraw a (halfCnt w Q0) e.1 * kraw b (halfCnt w Q1) e.2.1 * kraw c (halfCnt w Q2) e.2.2.1) := by
      unfold baryRowVal; dsimp only [classify, t]
      simp only [krawFast_eq_kraw]
      cases e.2.2.2.1
      · simp [chr, dot_comm (m + 1) w (zero (m + 1)), dot_zero, sign]
      · simp only [if_true]; unfold chr; cases dot (m + 1) w qb <;> simp [sign]
    have hsum_eq : total (m + 1) (fun w => nz w * baryRowVal a b c e (classify w)) =
        total (m + 1) (fun w => nz w * (chr w t *
          (kraw a (halfCnt w Q0) e.1 * kraw b (halfCnt w Q1) e.2.1 * kraw c (halfCnt w Q2) e.2.2.1))) := by
      apply congrArg (total (m + 1)); funext w; rw [hrow_eq w]
    rw [hsum_eq]
    if hd0 : e.1 + e.2.1 + e.2.2.1 = 0 then
      right
      have he1 : e.1 = 0 := by omega
      have he2 : e.2.1 = 0 := by omega
      have he3 : e.2.2.1 = 0 := by omega
      unfold baryRowRhs
      simp only [hd0, beq_self_eq_true, if_true, he1, he2, he3]
      have h1 (w : W (m + 1)) : nz w * (chr w t * (kraw a (halfCnt w Q0) 0 * kraw b (halfCnt w Q1) 0 * kraw c (halfCnt w Q2) 0)) =
          nz w * chr w t := by rw [kraw_k0', kraw_k0', kraw_k0']; simp
      rw [funext h1, nz_total (fun w => chr w t)]
      have hchr0 : chr (zero (m + 1)) t = 1 := by simp [chr, dot_zero, sign]
      rw [hchr0, sum_chr_eq t]
      dsimp only [t]
      cases e.2.2.2.1
      · simp [many_eq_pow2]
      · simp [hqb]
    else
      unfold baryRowRhs; dsimp only
      have hbeq : (e.1 + e.2.1 + e.2.2.1 == 0) = false := beq_false_of_ne hd0
      rw [hbeq]; simp only [Bool.false_eq_true, if_false, chooseFast_eq_choose]
      if hd1 : e.1 + e.2.1 + e.2.2.1 = 1 then
        right
        have ht0 : Q0 t = false := by dsimp only [t]; cases e.2.2.2.1 <;> simp [h0_0, hq_0]
        have ht1 : Q1 t = false := by dsimp only [t]; cases e.2.2.2.1 <;> simp [h0_1, hq_1]
        have ht2 : Q2 t = false := by dsimp only [t]; cases e.2.2.2.1 <;> simp [h0_2, hq_2]
        have h1 := kraw_triple_shifted_deg1_eq t Q0 Q1 Q2 ht0 ht1 ht2 e.1 e.2.1 e.2.2.1 hd1
        dsimp only at h1; rw [ha, hb, hc] at h1; exact h1
      else if hd2 : e.1 + e.2.1 + e.2.2.1 = 2 ∧ e.2.2.2.1 = false then
        right
        have ht : t = zero (m + 1) := by dsimp only [t]; simp [hd2.2]
        rw [ht]
        have hchr (w : W (m + 1)) : chr w (zero (m + 1)) = 1 := by
          simp [chr, dot_comm (m + 1) w (zero (m + 1)), dot_zero, sign]
        simp only [hchr, Int.one_mul]
        have h2 := kraw_triple_deg2_eq Q0 Q1 Q2 h01 h02 h12 e.1 e.2.1 e.2.2.1 hd2.1
        dsimp only at h2; rw [ha, hb, hc] at h2; exact h2
      else
        left
        have hwt : 0 ≤ e.2.2.2.2 := by
          unfold baryEntryValid at hv; dsimp only at hv
          have hb1 : (e.1 + e.2.1 + e.2.2.1 == 1) = false := beq_false_of_ne hd1
          have hb2 : ((e.1 + e.2.1 + e.2.2.1 == 2) && !e.2.2.2.1) = false := by
            cases hs : e.2.2.2.1
            · simp only [Bool.not_false, Bool.and_true]
              apply beq_false_of_ne; intro he2; exact hd2 ⟨he2, hs⟩
            · simp
          rw [hbeq, hb1, hb2] at hv
          simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at hv; exact hv
        have hnn := (kraw_triple_shifted_nonneg_and_mod t Q0 Q1 Q2 e.1 e.2.1 e.2.2.1).1
        rw [ha, hb, hc] at hnn; exact ⟨hwt, hnn⟩
  have heval_col (col : BaryCol) :
      evalWeighted (rows.map (fun r => (r.1, r.2.2))) col = evalBaryCol a b c cert col := by
    unfold evalBaryCol; rw [foldl_add_eq', Int.zero_add]
    clear hsound hcols_le hrhs_pos hvalid
    induction cert with
    | nil => rfl
    | cons e t ih => simp only [rows, List.map_cons, evalWeighted, sumInt] at ih ⊢; rw [ih]
  have heval_rhs : evalRhs (rows.map (fun r => (r.2.1, r.2.2))) = evalBaryRhs (m + 1) a b c cert := by
    unfold evalBaryRhs; rw [foldl_add_eq', Int.zero_add]
    clear hsound hcols_le hrhs_pos hvalid heval_col
    induction cert with
    | nil => rfl
    | cons e t ih => simp only [rows, List.map_cons, evalRhs, sumInt] at ih ⊢; rw [ih]
  exact farkas_refute classify cols hmem rows hsound
    (fun col hcol => by rw [heval_col col]; exact hcols_le col hcol)
    (by rw [heval_rhs]; exact hrhs_pos)

/-! ## Part 5: Unconditional `[24, 8, ≥10]_2` Non-Existence & High-Level Origin-Pin / Residual / Barycenter Bridges -/

/-- Unconditional coding-theory impossibility powering `t = 96, (1, 54, 24)` (`t96/check_centered_profiles.py`
    lines 187–188): NO binary linear code of length `24`, dimension `8`, and minimum distance `≥ 10` exists!
    Proof: Griesmer `g(8, 11) = 25 > 24` forces a weight-10 word; its `[14, 7, ≥5]_2` residual meets
    Griesmer `g(7, 6) = 15 > 14`, forcing a weight-5 word; its `[9, 6, ≥3]_2` second residual violates
    sphere-packing `2^6 * (1 + 9) = 640 > 512 = 2^9`. -/
theorem no_binary_code_24_8_10 (cols : List (W 8)) (hlen : cols.length = 24)
    (hd10 : ∀ v : W 8, v ≠ zero 8 → 10 ≤ codeWt v cols) : False := by
  let u1 : W 8 := minNonzeroWt cols
  have hu1 : u1 ≠ zero 8 ∧ ∀ w : W 8, w ≠ zero 8 → codeWt u1 cols ≤ codeWt w cols :=
    minNonzeroWt_spec cols
  have h10_le : 10 ≤ codeWt u1 cols := hd10 u1 hu1.1
  have hlt11 : codeWt u1 cols < 11 :=
    match Nat.lt_or_ge (codeWt u1 cols) 11 with
    | Or.inl h => h
    | Or.inr hge11 => by
      exfalso
      have hall11 : ∀ v : W 8, v ≠ zero 8 → 11 ≤ codeWt v cols := by
        intro v hv; have := hu1.2 v hv; omega
      have hg := griesmer_bound 8 11 cols hall11
      have hval : griesmer 8 11 = 26 := by decide
      omega
  have hu1_wt : codeWt u1 cols = 10 := by omega
  let res1 : List (W 7) := (cols.filter (fun x => !dot 8 u1 x)).map (projCompl u1)
  have hres1_len : res1.length = 14 := by
    dsimp only [res1]; rw [List.length_map]
    have hfl : (cols.filter (fun x => !dot 8 u1 x)).length + codeWt u1 cols = cols.length :=
      codeWt_filter_len (k := 8) u1 cols
    omega
  have hres1_wt (a : W 7) :
      codeWt a res1 = codeWt (embedCompl u1 a) (cols.filter (fun x => !dot 8 u1 x)) := by
    dsimp only [res1, codeWt]
    rw [List.filter_map, List.length_map]
    congr 1; apply List.filter_congr; intro x _; exact dot_embedCompl u1 a x
  have hres1_d5 (a : W 7) (ha : a ≠ zero 7) : 5 ≤ codeWt a res1 := by
    rw [hres1_wt a]
    have hadd : 2 * codeWt (embedCompl u1 a) (cols.filter (fun x => !dot 8 u1 x)) + codeWt u1 cols =
        codeWt (embedCompl u1 a) cols + codeWt (add 8 (embedCompl u1 a) u1) cols :=
      codeWt_add_ge (k := 8) u1 (embedCompl u1 a) cols
    have hw1 := hd10 (embedCompl u1 a) (embedCompl_ne_zero u1 hu1.1 a ha)
    have hw2 := hd10 (add 8 (embedCompl u1 a) u1) (add_embedCompl_ne_zero u1 hu1.1 a)
    omega
  let u2 : W 7 := minNonzeroWt res1
  have hu2 : u2 ≠ zero 7 ∧ ∀ w : W 7, w ≠ zero 7 → codeWt u2 res1 ≤ codeWt w res1 :=
    minNonzeroWt_spec res1
  have h5_le : 5 ≤ codeWt u2 res1 := hres1_d5 u2 hu2.1
  have hlt6 : codeWt u2 res1 < 6 :=
    match Nat.lt_or_ge (codeWt u2 res1) 6 with
    | Or.inl h => h
    | Or.inr hge6 => by
      exfalso
      have hall6 : ∀ a : W 7, a ≠ zero 7 → 6 ≤ codeWt a res1 := by
        intro a ha; have := hu2.2 a ha; omega
      have hg := griesmer_bound 7 6 res1 hall6
      have hval : griesmer 7 6 = 15 := by decide
      omega
  have hu2_wt : codeWt u2 res1 = 5 := by omega
  let res2 : List (W 6) := (res1.filter (fun x => !dot 7 u2 x)).map (projCompl u2)
  have hres2_len : res2.length = 9 := by
    dsimp only [res2]; rw [List.length_map]
    have hfl : (res1.filter (fun x => !dot 7 u2 x)).length + codeWt u2 res1 = res1.length :=
      codeWt_filter_len (k := 7) u2 res1
    omega
  have hres2_wt (b : W 6) :
      codeWt b res2 = codeWt (embedCompl u2 b) (res1.filter (fun x => !dot 7 u2 x)) := by
    dsimp only [res2, codeWt]
    rw [List.filter_map, List.length_map]
    congr 1; apply List.filter_congr; intro x _; exact dot_embedCompl u2 b x
  have hres2_d3 (b : W 6) (hb : b ≠ zero 6) : 3 ≤ codeWt b res2 := by
    rw [hres2_wt b]
    have hadd : 2 * codeWt (embedCompl u2 b) (res1.filter (fun x => !dot 7 u2 x)) + codeWt u2 res1 =
        codeWt (embedCompl u2 b) res1 + codeWt (add 7 (embedCompl u2 b) u2) res1 :=
      codeWt_add_ge (k := 7) u2 (embedCompl u2 b) res1
    have hw1 := hres1_d5 (embedCompl u2 b) (embedCompl_ne_zero u2 hu2.1 b hb)
    have hw2 := hres1_d5 (add 7 (embedCompl u2 b) u2) (add_embedCompl_ne_zero u2 hu2.1 b)
    omega
  have hsp := sphere_packing_d3 6 res2 hres2_d3
  rw [hres2_len] at hsp
  exact absurd hsp (by decide)

/-- Deduplicated helper for list-based weight sets. -/
def dedupTriples : List Triple → List Triple
  | [] => []
  | x :: t => let r := dedupTriples t; if x ∈ r then r else x :: r

private theorem mem_dedupTriples {x : Triple} : ∀ {L : List Triple}, x ∈ dedupTriples L ↔ x ∈ L
  | [] => Iff.rfl
  | a :: t => by
    unfold dedupTriples
    dsimp only
    split
    · rename_i hmem
      rw [mem_dedupTriples, List.mem_cons]
      constructor
      · intro hx; exact Or.inr hx
      · intro hx
        rcases hx with rfl | hx
        · exact (mem_dedupTriples.mp hmem)
        · exact hx
    · rw [List.mem_cons, List.mem_cons, mem_dedupTriples]

/-- Origin-pinned weight set (`t96/check_centered_profiles.py` lines 97–107):
    orient every surviving split away from an `A`-point chosen as the origin. -/
def centeredWeights (a b c : Nat) (splits : List Triple) : List Triple :=
  dedupTriples (splits.flatMap (fun s =>
    let inv := (a - s.1, b - s.2.1, c - s.2.2)
    (if 0 < s.1 then [inv] else []) ++ (if 0 < inv.1 then [s] else [])))

private theorem halfCnt_pos_of_mem {n : Nat} (w x0 : W n) (P : W n → Bool)
    (hP : P x0 = true) (hd : dot n w x0 = true) : 0 < halfCnt w P := by
  have hmem : x0 ∈ (suppList P).filter (fun x => dot n w x) := by
    rw [List.mem_filter]; refine ⟨?_, hd⟩
    unfold suppList; rw [List.mem_filter]; exact ⟨all_worlds n x0, hP⟩
  exact List.length_pos_of_mem hmem

private theorem halfCntFalse_pos_of_mem {n : Nat} (w x0 : W n) (P : W n → Bool)
    (hP : P x0 = true) (hd : dot n w x0 = false) : 0 < halfCntFalse w P := by
  have hmem : x0 ∈ (suppList P).filter (fun x => !dot n w x) := by
    rw [List.mem_filter]; refine ⟨?_, by simp [hd]⟩
    unfold suppList; rw [List.mem_filter]; exact ⟨all_worlds n x0, hP⟩
  exact List.length_pos_of_mem hmem

/-- High-level origin-pinning theorem: given ANY pairwise-disjoint `(A, B, C)` on `W dim`
    with `|A| = a ≥ 1`, `|B| = b`, `|C| = c` whose nonzero hyperplane splits all lie in `splits`
    (up to complement), a verified `checkCenteredCert` on `(a - 1, b, c)` and `centeredWeights`
    refutes `(A, B, C)`. -/
theorem origin_pin_refute {dim : Nat} (A B C : W dim → Bool)
    (hAB : ∀ x, (A x && B x) = false) (hAC : ∀ x, (A x && C x) = false) (hBC : ∀ x, (B x && C x) = false)
    (a b c : Nat) (ha_pos : 0 < a)
    (ha : (suppList A).length = a) (hb : (suppList B).length = b) (hc : (suppList C).length = c)
    (splits : List Triple)
    (hsplits : ∀ w : W dim, w ≠ zero dim →
      (halfCnt w A, halfCnt w B, halfCnt w C) ∈ splits ∨
      (halfCntFalse w A, halfCntFalse w B, halfCntFalse w C) ∈ splits)
    (cert : List KrawEntry)
    (hcheck : checkCenteredCert dim (a - 1) b c (centeredWeights a b c splits) cert = true) : False := by
  have hne : suppList A ≠ [] := by
    intro hnil; rw [hnil] at ha; simp at ha; omega
  cases hL : suppList A with
  | nil => exact hne hL
  | cons x0 rest =>
    have hx0A : A x0 = true := by
      have hm : x0 ∈ suppList A := by rw [hL]; exact List.mem_cons_self _ _
      unfold suppList at hm; rw [List.mem_filter] at hm; exact hm.2
    let P : W dim → Bool := puncture (translate A x0) (zero dim)
    let Q : W dim → Bool := translate B x0
    let R : W dim → Bool := translate C x0
    have hAx0_tr : translate A x0 (zero dim) = true := by
      unfold translate; rw [add_zero_left]; exact hx0A
    have h0P : P (zero dim) = false := puncture_self _ _
    have h0Q : Q (zero dim) = false := by
      unfold Q translate; rw [add_zero_left]
      have h := hAB x0; rw [hx0A, Bool.true_and] at h; exact h
    have h0R : R (zero dim) = false := by
      unfold R translate; rw [add_zero_left]
      have h := hAC x0; rw [hx0A, Bool.true_and] at h; exact h
    have hPQ : ∀ x, (P x && Q x) = false := by
      intro x; unfold P Q puncture translate
      have h := hAB (add dim x x0)
      cases hA : A (add dim x x0) <;> cases hB : B (add dim x x0) <;> simp_all
    have hPR : ∀ x, (P x && R x) = false := by
      intro x; unfold P R puncture translate
      have h := hAC (add dim x x0)
      cases hA : A (add dim x x0) <;> cases hC : C (add dim x x0) <;> simp_all
    have hQR : ∀ x, (Q x && R x) = false := by
      intro x; unfold Q R translate; exact hBC (add dim x x0)
    have hlenP : (suppList P).length = a - 1 := by
      dsimp only [P]; rw [suppList_puncture_length, suppList_translate_length, hAx0_tr, ha]; simp
    have hlenQ : (suppList Q).length = b := by
      dsimp only [Q]; rw [suppList_translate_length, hb]
    have hlenR : (suppList R).length = c := by
      dsimp only [R]; rw [suppList_translate_length, hc]
    have hmem : ∀ w : W dim, w ≠ zero dim →
        (halfCnt w P, halfCnt w Q, halfCnt w R) ∈ centeredWeights a b c splits := by
      intro w hw
      have hpP : halfCnt w P = halfCnt w (translate A x0) := by
        dsimp only [P]; rw [halfCnt_puncture, dot_comm dim w (zero dim), dot_zero]; simp
      rw [hpP]
      dsimp only [Q, R]
      rw [halfCnt_translate, halfCnt_translate, halfCnt_translate]
      have hsumA := halfCnt_add_false w A; rw [ha] at hsumA
      have hsumB := halfCnt_add_false w B; rw [hb] at hsumB
      have hsumC := halfCnt_add_false w C; rw [hc] at hsumC
      have hinv1 : (a - halfCnt w A, b - halfCnt w B, c - halfCnt w C) =
          (halfCntFalse w A, halfCntFalse w B, halfCntFalse w C) := by
        rw [show a - halfCnt w A = halfCntFalse w A by omega,
            show b - halfCnt w B = halfCntFalse w B by omega,
            show c - halfCnt w C = halfCntFalse w C by omega]
      have hinv2 : (a - halfCntFalse w A, b - halfCntFalse w B, c - halfCntFalse w C) =
          (halfCnt w A, halfCnt w B, halfCnt w C) := by
        rw [show a - halfCntFalse w A = halfCnt w A by omega,
            show b - halfCntFalse w B = halfCnt w B by omega,
            show c - halfCntFalse w C = halfCnt w C by omega]
      unfold centeredWeights; rw [mem_dedupTriples, List.mem_flatMap]
      cases hdw : dot dim w x0
      · simp only [Bool.false_eq_true, if_false]
        have hposF : 0 < halfCntFalse w A := halfCntFalse_pos_of_mem w x0 A hx0A hdw
        rcases hsplits w hw with hT | hF
        · refine ⟨(halfCnt w A, halfCnt w B, halfCnt w C), hT, ?_⟩
          rw [List.mem_append]; right
          have hpos' : 0 < a - halfCnt w A := by omega
          simp [hpos']
        · refine ⟨(halfCntFalse w A, halfCntFalse w B, halfCntFalse w C), hF, ?_⟩
          rw [List.mem_append]; left
          simp [hposF, hinv2]
      · simp only [if_true]
        have hposT : 0 < halfCnt w A := halfCnt_pos_of_mem w x0 A hx0A hdw
        rcases hsplits w hw with hT | hF
        · refine ⟨(halfCnt w A, halfCnt w B, halfCnt w C), hT, ?_⟩
          rw [List.mem_append]; left
          simp [hposT, hinv1]
        · refine ⟨(halfCntFalse w A, halfCntFalse w B, halfCntFalse w C), hF, ?_⟩
          rw [List.mem_append]; right
          have hpos' : 0 < a - halfCntFalse w A := by omega
          simp [hpos']
    exact centered_cert_refute P Q R hPQ hPR hQR h0P h0Q h0R (a - 1) b c hlenP hlenQ hlenR
      (centeredWeights a b c splits) hmem cert hcheck

/-- Residual weight set (`t96/check_centered_profiles.py` lines 110–119):
    all candidate `(x', y', z')` on `ker(u)` compatible with `weights` and `anchor`. -/
def residualWeights (a b c : Nat) (weights : List Triple) (anchor : Triple) : List Triple :=
  let remA := a - anchor.1
  let remB := b - anchor.2.1
  let remC := c - anchor.2.2
  dedupTriples (weights.flatMap (fun l =>
    weights.flatMap (fun r =>
      let n1 := l.1 + r.1
      let n2 := l.2.1 + r.2.1
      let n3 := l.2.2 + r.2.2
      if anchor.1 ≤ n1 && anchor.2.1 ≤ n2 && anchor.2.2 ≤ n3 &&
         (n1 - anchor.1) % 2 == 0 && (n2 - anchor.2.1) % 2 == 0 && (n3 - anchor.2.2) % 2 == 0 &&
         (n1 - anchor.1) / 2 ≤ remA && (n2 - anchor.2.1) / 2 ≤ remB && (n3 - anchor.2.2) / 2 ≤ remC &&
         ((l.1 : Int) - (r.1 : Int)).natAbs ≤ anchor.1 &&
         ((l.2.1 : Int) - (r.2.1 : Int)).natAbs ≤ anchor.2.1 &&
         ((l.2.2 : Int) - (r.2.2 : Int)).natAbs ≤ anchor.2.2
      then [((n1 - anchor.1) / 2, (n2 - anchor.2.1) / 2, (n3 - anchor.2.2) / 2)]
      else [])))

private theorem secPt_zero_false :
    ∀ (m : Nat) (u : W (m + 1)), u ≠ zero (m + 1) →
      Balanced242Hyperplane.secPt m u false (zero m) = zero (m + 1)
  | 0, (ub, ()), hu => by
    cases ub
    · exact absurd rfl hu
    · simp [Balanced242Hyperplane.secPt, dot, zero]
  | m + 1, (true, ur), _ => by
    rw [Balanced242Hyperplane.secPt_true, dot_comm (m + 1) ur (zero (m + 1)), dot_zero]
    rfl
  | m + 1, (false, ur), hu => by
    have hur : ur ≠ zero (m + 1) := fun h => hu (by rw [h]; rfl)
    show Balanced242Hyperplane.secPt (m + 1) (false, ur) false (false, zero m) = (false, zero (m + 1))
    rw [Balanced242Hyperplane.secPt_false, secPt_zero_false m ur hur]

private theorem dot_embedCompl_secPt :
    ∀ (m : Nat) (u : W (m + 1)), u ≠ zero (m + 1) → ∀ (v a : W m),
      dot (m + 1) (embedCompl u v) (Balanced242Hyperplane.secPt m u false a) = dot m v a
  | 0, _, _, (), () => by simp [embedCompl, dot, zero]
  | m + 1, (true, ur), _, v, a => by
    rw [Balanced242Hyperplane.secPt_true]
    simp [embedCompl, dot]
  | m + 1, (false, ur), hu, (vb, vr), (ab, ar) => by
    have hur : ur ≠ zero (m + 1) := fun h => hu (by rw [h]; rfl)
    rw [Balanced242Hyperplane.secPt_false]
    show (vb && ab ^^ dot (m + 1) (embedCompl ur vr) (Balanced242Hyperplane.secPt m ur false ar)) =
      (vb && ab ^^ dot m vr ar)
    rw [dot_embedCompl_secPt m ur hur vr ar]

private theorem sec_suppList_len {m : Nat} (u : W (m + 1)) (hu : u ≠ zero (m + 1)) (P : W (m + 1) → Bool) :
    (suppList (fun a => P (Balanced242Hyperplane.secPt m u false a))).length = halfCntFalse u P := by
  have h1 := suppList_length_eq_total_ind (fun a => P (Balanced242Hyperplane.secPt m u false a))
  have h2 := halfCntFalse_eq_total_ind u P
  have hsec := Balanced242Hyperplane.sec_total m u hu false (fun x => ind (P x))
  have hpt (x : W (m + 1)) : (if dot (m + 1) u x = false then ind (P x) else 0) =
      ind (P x && !dot (m + 1) u x) := by
    cases P x <;> cases dot (m + 1) u x <;> decide
  rw [funext hpt] at hsec
  omega

private theorem sec_halfCnt_eq {m : Nat} (u : W (m + 1)) (hu : u ≠ zero (m + 1))
    (P : W (m + 1) → Bool) (v : W m) :
    halfCnt v (fun a => P (Balanced242Hyperplane.secPt m u false a)) =
      halfCnt (embedCompl u v) (fun x => P x && !dot (m + 1) u x) := by
  have h1 := halfCnt_eq_total_ind v (fun a => P (Balanced242Hyperplane.secPt m u false a))
  have h2 := halfCnt_eq_total_ind (embedCompl u v) (fun x => P x && !dot (m + 1) u x)
  have hsec := Balanced242Hyperplane.sec_total m u hu false
    (fun x => ind (P x && dot (m + 1) (embedCompl u v) x))
  have hpt1 (x : W (m + 1)) :
      (if dot (m + 1) u x = false then ind (P x && dot (m + 1) (embedCompl u v) x) else 0) =
      ind ((P x && !dot (m + 1) u x) && dot (m + 1) (embedCompl u v) x) := by
    cases P x <;> cases dot (m + 1) u x <;> cases dot (m + 1) (embedCompl u v) x <;> decide
  have hpt2 (a : W m) :
      ind (P (Balanced242Hyperplane.secPt m u false a) &&
        dot (m + 1) (embedCompl u v) (Balanced242Hyperplane.secPt m u false a)) =
      ind (P (Balanced242Hyperplane.secPt m u false a) && dot m v a) := by
    rw [dot_embedCompl_secPt m u hu v a]
  rw [funext hpt1, funext hpt2] at hsec
  omega

/-- Residual-kernel refutation: for any pairwise-disjoint `(P, Q, R)` avoiding `0` on `W (m+1)`
    with weight set `weights`, if a `dim = m` `checkCenteredCert` succeeds on `residualWeights` for
    `anchor`, then NO nonzero `u ∈ W (m+1)` can realize `anchor`! -/
theorem residual_cert_refute {m : Nat} (P Q R : W (m + 1) → Bool)
    (hPQ : ∀ x, (P x && Q x) = false) (hPR : ∀ x, (P x && R x) = false) (hQR : ∀ x, (Q x && R x) = false)
    (h0P : P (zero (m + 1)) = false) (h0Q : Q (zero (m + 1)) = false) (h0R : R (zero (m + 1)) = false)
    (a b c : Nat)
    (ha : (suppList P).length = a) (hb : (suppList Q).length = b) (hc : (suppList R).length = c)
    (weights : List Triple)
    (hmem : ∀ w : W (m + 1), w ≠ zero (m + 1) → (halfCnt w P, halfCnt w Q, halfCnt w R) ∈ weights)
    (u : W (m + 1)) (hu : u ≠ zero (m + 1))
    (anchor : Triple) (hanc : (halfCnt u P, halfCnt u Q, halfCnt u R) = anchor)
    (cert : List KrawEntry)
    (hcheck : checkCenteredCert m (a - anchor.1) (b - anchor.2.1) (c - anchor.2.2)
      (residualWeights a b c weights anchor) cert = true) : False := by
  let P' (x : W m) := P (Balanced242Hyperplane.secPt m u false x)
  let Q' (x : W m) := Q (Balanced242Hyperplane.secPt m u false x)
  let R' (x : W m) := R (Balanced242Hyperplane.secPt m u false x)
  have hP'Q' : ∀ x, (P' x && Q' x) = false := fun x => hPQ _
  have hP'R' : ∀ x, (P' x && R' x) = false := fun x => hPR _
  have hQ'R' : ∀ x, (Q' x && R' x) = false := fun x => hQR _
  have h0P' : P' (zero m) = false := by dsimp only [P']; rw [secPt_zero_false m u hu]; exact h0P
  have h0Q' : Q' (zero m) = false := by dsimp only [Q']; rw [secPt_zero_false m u hu]; exact h0Q
  have h0R' : R' (zero m) = false := by dsimp only [R']; rw [secPt_zero_false m u hu]; exact h0R
  have ha1 : halfCnt u P = anchor.1 := congrArg Prod.fst hanc
  have hb1 : halfCnt u Q = anchor.2.1 := congrArg (fun t => t.2.1) hanc
  have hc1 : halfCnt u R = anchor.2.2 := congrArg (fun t => t.2.2) hanc
  have hlenP' : (suppList P').length = a - anchor.1 := by
    rw [sec_suppList_len u hu P]; have := halfCnt_add_false u P; omega
  have hlenQ' : (suppList Q').length = b - anchor.2.1 := by
    rw [sec_suppList_len u hu Q]; have := halfCnt_add_false u Q; omega
  have hlenR' : (suppList R').length = c - anchor.2.2 := by
    rw [sec_suppList_len u hu R]; have := halfCnt_add_false u R; omega
  have hmem' : ∀ v : W m, v ≠ zero m →
      (halfCnt v P', halfCnt v Q', halfCnt v R') ∈ residualWeights a b c weights anchor := by
    intro v hv
    let v1 := embedCompl u v
    let v2 := add (m + 1) v1 u
    have hv1 : v1 ≠ zero (m + 1) := embedCompl_ne_zero u hu v hv
    have hv2 : v2 ≠ zero (m + 1) := add_embedCompl_ne_zero u hu v
    have hl := hmem v1 hv1
    have hr := hmem v2 hv2
    have hP_res := residual_kernel_counts P u v1
    have hQ_res := residual_kernel_counts Q u v1
    have hR_res := residual_kernel_counts R u v1
    dsimp only at hP_res hQ_res hR_res
    have hP1 : 2 * halfCnt v P' + anchor.1 = halfCnt v1 P + halfCnt v2 P := by
      rw [sec_halfCnt_eq u hu P v, ← ha1]; exact hP_res.1
    have hQ1 : 2 * halfCnt v Q' + anchor.2.1 = halfCnt v1 Q + halfCnt v2 Q := by
      rw [sec_halfCnt_eq u hu Q v, ← hb1]; exact hQ_res.1
    have hR1 : 2 * halfCnt v R' + anchor.2.2 = halfCnt v1 R + halfCnt v2 R := by
      rw [sec_halfCnt_eq u hu R v, ← hc1]; exact hR_res.1
    have hP_le : halfCnt v P' ≤ a - anchor.1 := by rw [← hlenP']; exact halfCnt_le v P'
    have hQ_le : halfCnt v Q' ≤ b - anchor.2.1 := by rw [← hlenQ']; exact halfCnt_le v Q'
    have hR_le : halfCnt v R' ≤ c - anchor.2.2 := by rw [← hlenR']; exact halfCnt_le v R'
    unfold residualWeights; rw [mem_dedupTriples, List.mem_flatMap]
    refine ⟨(halfCnt v1 P, halfCnt v1 Q, halfCnt v1 R), hl, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨(halfCnt v2 P, halfCnt v2 Q, halfCnt v2 R), hr, ?_⟩
    have hcnd :
        anchor.1 ≤ halfCnt v1 P + halfCnt v2 P ∧
        anchor.2.1 ≤ halfCnt v1 Q + halfCnt v2 Q ∧
        anchor.2.2 ≤ halfCnt v1 R + halfCnt v2 R ∧
        (halfCnt v1 P + halfCnt v2 P - anchor.1) % 2 = 0 ∧
        (halfCnt v1 Q + halfCnt v2 Q - anchor.2.1) % 2 = 0 ∧
        (halfCnt v1 R + halfCnt v2 R - anchor.2.2) % 2 = 0 ∧
        (halfCnt v1 P + halfCnt v2 P - anchor.1) / 2 ≤ a - anchor.1 ∧
        (halfCnt v1 Q + halfCnt v2 Q - anchor.2.1) / 2 ≤ b - anchor.2.1 ∧
        (halfCnt v1 R + halfCnt v2 R - anchor.2.2) / 2 ≤ c - anchor.2.2 ∧
        ((halfCnt v1 P : Int) - (halfCnt v2 P : Int)).natAbs ≤ anchor.1 ∧
        ((halfCnt v1 Q : Int) - (halfCnt v2 Q : Int)).natAbs ≤ anchor.2.1 ∧
        ((halfCnt v1 R : Int) - (halfCnt v2 R : Int)).natAbs ≤ anchor.2.2 := by
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
              by omega, by omega, by omega, by rw [← ha1]; exact hP_res.2,
              by rw [← hb1]; exact hQ_res.2, by rw [← hc1]; exact hR_res.2⟩
    have heq_t :
        ((halfCnt v1 P + halfCnt v2 P - anchor.1) / 2,
         (halfCnt v1 Q + halfCnt v2 Q - anchor.2.1) / 2,
         (halfCnt v1 R + halfCnt v2 R - anchor.2.2) / 2) =
        (halfCnt v P', halfCnt v Q', halfCnt v R') := by
      rw [show (halfCnt v1 P + halfCnt v2 P - anchor.1) / 2 = halfCnt v P' by omega,
          show (halfCnt v1 Q + halfCnt v2 Q - anchor.2.1) / 2 = halfCnt v Q' by omega,
          show (halfCnt v1 R + halfCnt v2 R - anchor.2.2) / 2 = halfCnt v R' by omega]
    dsimp only
    simp [hcnd, heq_t]
  exact centered_cert_refute P' Q' R' hP'Q' hP'R' hQ'R' h0P' h0Q' h0R'
    (a - anchor.1) (b - anchor.2.1) (c - anchor.2.2) hlenP' hlenQ' hlenR'
    (residualWeights a b c weights anchor) hmem' cert hcheck

/-- Full `(1, b, 24)` origin-pinning + residual-kernel + `[24, 8, ≥10]_2` refutation theorem
    (matching `t96/check_centered_profiles.py` lines 179–190 for `(1, 54, 24)`!). -/
theorem origin_pin_residual_24_refute (A B C : W 8 → Bool)
    (hAB : ∀ x, (A x && B x) = false) (hAC : ∀ x, (A x && C x) = false) (hBC : ∀ x, (B x && C x) = false)
    (b : Nat)
    (ha : (suppList A).length = 1) (hb : (suppList B).length = b) (hc : (suppList C).length = 24)
    (splits : List Triple)
    (hsplits : ∀ w : W 8, w ≠ zero 8 →
      (halfCnt w A, halfCnt w B, halfCnt w C) ∈ splits ∨
      (halfCntFalse w A, halfCntFalse w B, halfCntFalse w C) ∈ splits)
    (resCerts : List (Triple × List KrawEntry))
    (hcover : ∀ w, w ∈ centeredWeights 1 b 24 splits → w.2.2 < 10 →
      ∃ cert, (w, cert) ∈ resCerts ∧
        checkCenteredCert 7 (0 - w.1) (b - w.2.1) (24 - w.2.2)
          (residualWeights 0 b 24 (centeredWeights 1 b 24 splits) w) cert = true) : False := by
  have hne : suppList A ≠ [] := by intro hnil; rw [hnil] at ha; simp at ha
  cases hL : suppList A with
  | nil => exact hne hL
  | cons x0 rest =>
    have hx0A : A x0 = true := by
      have hm : x0 ∈ suppList A := by rw [hL]; exact List.mem_cons_self _ _
      unfold suppList at hm; rw [List.mem_filter] at hm; exact hm.2
    let P : W 8 → Bool := puncture (translate A x0) (zero 8)
    let Q : W 8 → Bool := translate B x0
    let R : W 8 → Bool := translate C x0
    have hAx0_tr : translate A x0 (zero 8) = true := by
      unfold translate; rw [add_zero_left]; exact hx0A
    have h0P : P (zero 8) = false := puncture_self _ _
    have h0Q : Q (zero 8) = false := by
      unfold Q translate; rw [add_zero_left]
      have h := hAB x0; rw [hx0A, Bool.true_and] at h; exact h
    have h0R : R (zero 8) = false := by
      unfold R translate; rw [add_zero_left]
      have h := hAC x0; rw [hx0A, Bool.true_and] at h; exact h
    have hPQ : ∀ x, (P x && Q x) = false := by
      intro x; unfold P Q puncture translate
      have h := hAB (add 8 x x0)
      cases hA : A (add 8 x x0) <;> cases hB : B (add 8 x x0) <;> simp_all
    have hPR : ∀ x, (P x && R x) = false := by
      intro x; unfold P R puncture translate
      have h := hAC (add 8 x x0)
      cases hA : A (add 8 x x0) <;> cases hC : C (add 8 x x0) <;> simp_all
    have hQR : ∀ x, (Q x && R x) = false := fun x => hBC (add 8 x x0)
    have hlenP : (suppList P).length = 0 := by
      dsimp only [P]; rw [suppList_puncture_length, suppList_translate_length, hAx0_tr, ha]; simp
    have hlenQ : (suppList Q).length = b := by dsimp only [Q]; rw [suppList_translate_length, hb]
    have hlenR : (suppList R).length = 24 := by dsimp only [R]; rw [suppList_translate_length, hc]
    have hmem : ∀ w : W 8, w ≠ zero 8 →
        (halfCnt w P, halfCnt w Q, halfCnt w R) ∈ centeredWeights 1 b 24 splits := by
      intro w hw
      have hpP : halfCnt w P = halfCnt w (translate A x0) := by
        dsimp only [P]; rw [halfCnt_puncture, dot_comm 8 w (zero 8), dot_zero]; simp
      rw [hpP]; dsimp only [Q, R]
      rw [halfCnt_translate, halfCnt_translate, halfCnt_translate]
      have hsumA := halfCnt_add_false w A; rw [ha] at hsumA
      have hsumB := halfCnt_add_false w B; rw [hb] at hsumB
      have hsumC := halfCnt_add_false w C; rw [hc] at hsumC
      have hinv1 : (1 - halfCnt w A, b - halfCnt w B, 24 - halfCnt w C) =
          (halfCntFalse w A, halfCntFalse w B, halfCntFalse w C) := by
        rw [show 1 - halfCnt w A = halfCntFalse w A by omega,
            show b - halfCnt w B = halfCntFalse w B by omega,
            show 24 - halfCnt w C = halfCntFalse w C by omega]
      have hinv2 : (1 - halfCntFalse w A, b - halfCntFalse w B, 24 - halfCntFalse w C) =
          (halfCnt w A, halfCnt w B, halfCnt w C) := by
        rw [show 1 - halfCntFalse w A = halfCnt w A by omega,
            show b - halfCntFalse w B = halfCnt w B by omega,
            show 24 - halfCntFalse w C = halfCnt w C by omega]
      unfold centeredWeights; rw [mem_dedupTriples, List.mem_flatMap]
      cases hdw : dot 8 w x0
      · simp only [Bool.false_eq_true, if_false]
        have hposF : 0 < halfCntFalse w A := halfCntFalse_pos_of_mem w x0 A hx0A hdw
        rcases hsplits w hw with hT | hF
        · refine ⟨(halfCnt w A, halfCnt w B, halfCnt w C), hT, ?_⟩
          rw [List.mem_append]; right; simp [show 0 < 1 - halfCnt w A by omega]
        · refine ⟨(halfCntFalse w A, halfCntFalse w B, halfCntFalse w C), hF, ?_⟩
          rw [List.mem_append]; left; simp [hposF, hinv2]
      · simp only [if_true]
        have hposT : 0 < halfCnt w A := halfCnt_pos_of_mem w x0 A hx0A hdw
        rcases hsplits w hw with hT | hF
        · refine ⟨(halfCnt w A, halfCnt w B, halfCnt w C), hT, ?_⟩
          rw [List.mem_append]; left; simp [hposT, hinv1]
        · refine ⟨(halfCntFalse w A, halfCntFalse w B, halfCntFalse w C), hF, ?_⟩
          rw [List.mem_append]; right; simp [show 0 < 1 - halfCntFalse w A by omega]
    have hd10 : ∀ u : W 8, u ≠ zero 8 → 10 ≤ codeWt u (suppList R) := by
      intro u hu
      match Nat.lt_or_ge (codeWt u (suppList R)) 10 with
      | Or.inr hge => exact hge
      | Or.inl hlt =>
        exfalso
        have hlt10 : halfCnt u R < 10 := hlt
        have hu_mem := hmem u hu
        rcases hcover (halfCnt u P, halfCnt u Q, halfCnt u R) hu_mem hlt10 with ⟨cert, _, hck⟩
        exact residual_cert_refute P Q R hPQ hPR hQR h0P h0Q h0R 0 b 24 hlenP hlenQ hlenR
          (centeredWeights 1 b 24 splits) hmem u hu _ rfl cert hck
    exact no_binary_code_24_8_10 (suppList R) hlenR hd10

end Balanced242Centered

#print axioms Balanced242Centered.sum_triple_esym_shifted
#print axioms Balanced242Centered.kraw_triple_shifted_nonneg_and_mod
#print axioms Balanced242Centered.kraw_triple_shifted_deg1_eq
#print axioms Balanced242Centered.halfCnt_mod2_eq_dot_barycenter
#print axioms Balanced242Centered.barycenter_translate_odd
#print axioms Balanced242Centered.cut_sum_eq_half
#print axioms Balanced242Centered.residual_kernel_counts
#print axioms Balanced242Centered.griesmer_bound
#print axioms Balanced242Centered.sphere_packing_d3
#print axioms Balanced242Centered.no_binary_code_24_8_10
#print axioms Balanced242Centered.centered_cert_refute
#print axioms Balanced242Centered.bary_cert_refute
#print axioms Balanced242Centered.origin_pin_refute
#print axioms Balanced242Centered.residual_cert_refute
#print axioms Balanced242Centered.origin_pin_residual_24_refute
