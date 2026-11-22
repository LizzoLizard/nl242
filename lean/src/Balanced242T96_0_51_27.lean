/-
  Balanced242T96_0_51_27.lean — Kernel-verified Lean 4 exclusion of `(96, 0, 51, 27, 8)`
  (the second and final `b + c = 78` profile at `t = 96`, pairing with
  `Balanced242T96Centered.excl_96_1_54_24`).

  Uses ZERO `out96` flag kills and ZERO anchor peeling — ONLY:
    * `Balanced242T96Quartic.rank8_a0_far_yz_div4` (unconditional `y % 2 = 0`, `z % 2 = 0`,
      `(y + z) % 4 = 0` after translating by `P = barycenter (clsC f g)`),
    * `Balanced242Farkas.SectionEnumE` (`excl6MaskT96`, empty `eBounds`),
    * `Balanced242Centered.centered_cert_refute` on 3 tiny integer Farkas certificates
      (6, 5, and 5 nonzero terms respectively for `P ∈ B`, `P ∈ C`, `P ∈ D`).

  Zero Mathlib, zero `sorry`, zero `native_decide`, zero custom axioms.
-/
import Balanced242T96Quartic
import Balanced242T96Data

namespace Balanced242T96_0_51_27

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Reduction Balanced242Plateau Balanced242Rank
open Balanced242Global Balanced242Rank8 Balanced242T96Quartic Balanced242T96Data
open Balanced242Krawtchouk (suppList halfCnt halfCntFalse halfCnt_add_false)
open Balanced242Farkas (Triple KrawEntry SectionEnumE genSplits canonPair costR6
  mem_genSplits section_costR6_le sec_suppList_eq_halfCnt suppList_length_eq_total)
open Balanced242Centered (barycenter translate puncture halfCnt_translate halfCnt_puncture
  puncture_self suppList_translate_length suppList_puncture_length
  checkCenteredCert centered_cert_refute)

/-- All `genSplits` far-side candidates `(0, y, z)` passing the unconditional mod-4 parity law
    `y % 2 = 0 ∧ z % 2 = 0 ∧ (y + z) % 4 = 0`. -/
def farWeights_0_51_27 : List Triple :=
  ((genSplits excl6MaskT96 [] 96 0 51 27).flatMap fun p =>
    [p, (0 - p.1, 51 - p.2.1, 27 - p.2.2)]).filter fun q =>
    q.2.1 % 2 == 0 && q.2.2 % 2 == 0 && (q.2.1 + q.2.2) % 4 == 0

/-- 6-term Farkas certificate for `P ∈ B` (`(0, 50, 27)`). -/
def cert_0_51_27_B : List KrawEntry :=
  [(0, 0, 0, 992439), (0, 0, 1, -8621), (0, 0, 2, 94828),
   (0, 1, 0, 100575), (0, 1, 1, 100575), (0, 0, 4, 2874)]

/-- 5-term degree-≤2 Farkas certificate for `P ∈ C` (`(0, 51, 26)`). -/
def cert_0_51_27_C : List KrawEntry :=
  [(0, 0, 0, 20), (0, 0, 1, -1), (0, 0, 2, 2), (0, 1, 0, 6), (0, 1, 1, 3)]

/-- 5-term degree-≤2 Farkas certificate for `P ∈ D` (`(0, 51, 27)`). -/
def cert_0_51_27_D : List KrawEntry :=
  [(0, 0, 0, 999998), (0, 0, 1, -130435), (0, 0, 2, 86957),
   (0, 1, 0, 130435), (0, 1, 1, 130435)]

theorem cert_B_ok : checkCenteredCert 8 0 50 27 farWeights_0_51_27 cert_0_51_27_B = true := by
  decide +kernel

theorem cert_C_ok : checkCenteredCert 8 0 51 26 farWeights_0_51_27 cert_0_51_27_C = true := by
  decide +kernel

theorem cert_D_ok : checkCenteredCert 8 0 51 27 farWeights_0_51_27 cert_0_51_27_D = true := by
  decide +kernel

private theorem clsA_B_disj (f g : Half) (x : W 8) : (clsA f g x && clsB f g x) = false := by
  unfold clsA clsB
  cases h : ((hi f g x).natAbs == 4)
  · rfl
  · have h4 : (hi f g x).natAbs = 4 := beq_iff_eq.mp h; rw [h4]; decide

private theorem clsA_C_disj (f g : Half) (x : W 8) : (clsA f g x && clsC f g x) = false := by
  unfold clsA clsC
  cases h : ((hi f g x).natAbs == 4)
  · rfl
  · have h4 : (hi f g x).natAbs = 4 := beq_iff_eq.mp h; rw [h4]; decide

private theorem clsB_C_disj (f g : Half) (x : W 8) : (clsB f g x && clsC f g x) = false := by
  unfold clsB clsC
  cases h : ((hi f g x).natAbs == 20)
  · rfl
  · have h20 : (hi f g x).natAbs = 20 := beq_iff_eq.mp h; rw [h20]; decide

private theorem all_true_of_total' : ∀ {n : Nat} (p : W n → Bool),
    total n (fun x => Balanced242Plateau.ind (p x)) = many n → ∀ x, p x = true
  | 0, p, h, () => by
    change Balanced242Plateau.ind (p ()) = 1 at h
    cases hp : p () <;> rw [hp] at h <;> simp [Balanced242Plateau.ind] at h ⊢
  | m + 1, p, h, (b, x) => by
    have hle (c : Bool) : total m (fun y => Balanced242Plateau.ind (p (c, y))) ≤ many m := by
      have hm := total_mono m (fun y => Balanced242Plateau.ind (p (c, y))) (fun _ => 1)
        (fun y => by dsimp only; cases p (c, y) <;> decide)
      rw [total_const, Int.mul_one] at hm; exact hm
    have hm1 : many (m + 1) = 2 * many m := by unfold many; rw [Int.pow_succ]; omega
    change total m (fun y => Balanced242Plateau.ind (p (false, y))) +
      total m (fun y => Balanced242Plateau.ind (p (true, y))) = many (m + 1) at h
    have h0 := hle false; have h1 := hle true
    cases b
    · have hf : total m (fun y => Balanced242Plateau.ind (p (false, y))) = many m := by omega
      exact all_true_of_total' (fun y => p (false, y)) hf x
    · have ht : total m (fun y => Balanced242Plateau.ind (p (true, y))) = many m := by omega
      exact all_true_of_total' (fun y => p (true, y)) ht x

/-- **Kernel-verified exclusion of `(96, 0, 51, 27, 8)`** (zero `out96` kills, zero anchor peeling). -/
theorem excl_96_0_51_27 (f g : Half)
    (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)
    (ht : agreements f g = 96)
    (hpa : pa f g = 0) (hpb : pb f g = 51) (hpc : pc f g = 27)
    (hrr : rr (β8 f g) = 1)
    (hsec : SectionEnumE excl6MaskT96 []) : False := by
  have hgood_all : ∀ x : W 8, good (β8 f g) x = true := by
    have hrg := rr_good (β8 f g) (cube8 f g res)
    rw [hrr, Int.one_mul] at hrg
    exact all_true_of_total' (good (β8 f g)) hrg
  have hplat16 : ∀ x : W 8,
      transform (Balanced242RankCond.q8 f g) x = 16 ∨
      transform (Balanced242RankCond.q8 f g) x = -16 := by
    intro x
    have hsq := spec_good (β8 f g) (cube8 f g res) x
    rw [hrr, hgood_all x] at hsq
    change transform (Balanced242RankCond.q8 f g) x * transform (Balanced242RankCond.q8 f g) x =
      many 8 * (1 * 1) at hsq
    have hm : many 8 * (1 * 1) = (16 : Int) * 16 := by decide
    rw [hm] at hsq
    exact sq_cases _ 16 hsq
  have hlenA : (suppList (clsA f g)).length = 0 := by
    have h1 := suppList_length_eq_total (clsA f g)
    have h2 : (pa f g : Int) = cnt (clsA f g) := Int.toNat_of_nonneg (cnt_nonneg _)
    unfold Balanced242Plateau.ind at h1; unfold cnt Balanced242Reduction.ind at h2; omega
  have hlenB : (suppList (clsB f g)).length = 51 := by
    have h1 := suppList_length_eq_total (clsB f g)
    have h2 : (pb f g : Int) = cnt (clsB f g) := Int.toNat_of_nonneg (cnt_nonneg _)
    unfold Balanced242Plateau.ind at h1; unfold cnt Balanced242Reduction.ind at h2; omega
  have hlenC : (suppList (clsC f g)).length = 27 := by
    have h1 := suppList_length_eq_total (clsC f g)
    have h2 : (pc f g : Int) = cnt (clsC f g) := Int.toNat_of_nonneg (cnt_nonneg _)
    unfold Balanced242Plateau.ind at h1; unfold cnt Balanced242Reduction.ind at h2; omega
  -- Every direction `w ≠ 0` lands in `genSplits excl6MaskT96 [] 96 0 51 27`!
  have hgen : ∀ w : W 8, w ≠ zero 8 →
      (halfCnt w (clsA f g), halfCnt w (clsB f g), halfCnt w (clsC f g)) ∈
        genSplits excl6MaskT96 [] 96 0 51 27 ∨
      (halfCntFalse w (clsA f g), halfCntFalse w (clsB f g), halfCntFalse w (clsC f g)) ∈
        genSplits excl6MaskT96 [] 96 0 51 27 := by
    intro w hw
    have hleA : halfCnt w (clsA f g) ≤ 0 := hlenA ▸ Balanced242Krawtchouk.halfCnt_le w (clsA f g)
    have hleB : halfCnt w (clsB f g) ≤ 51 := hlenB ▸ Balanced242Krawtchouk.halfCnt_le w (clsB f g)
    have hleC : halfCnt w (clsC f g) ≤ 27 := hlenC ▸ Balanced242Krawtchouk.halfCnt_le w (clsC f g)
    have hsumA := halfCnt_add_false w (clsA f g); rw [hlenA] at hsumA
    have hsumB := halfCnt_add_false w (clsB f g); rw [hlenB] at hsumB
    have hsumC := halfCnt_add_false w (clsC f g); rw [hlenC] at hsumC
    have hcF := (section_costR6_le excl6MaskT96 [] hsec f g res cap hrr w hw false 13).2
    have hcT := (section_costR6_le excl6MaskT96 [] hsec f g res cap hrr w hw true 13).2
    have sA := sec_suppList_eq_halfCnt w hw (clsA f g)
    have sB := sec_suppList_eq_halfCnt w hw (clsB f g)
    have sC := sec_suppList_eq_halfCnt w hw (clsC f g)
    have fA : halfCntFalse w (clsA f g) = 0 - halfCnt w (clsA f g) := by omega
    have fB : halfCntFalse w (clsB f g) = 51 - halfCnt w (clsB f g) := by omega
    have fC : halfCntFalse w (clsC f g) = 27 - halfCnt w (clsC f g) := by omega
    rw [sA.1, sB.1, sC.1, fA, fB, fC] at hcF
    rw [sA.2, sB.2, sC.2] at hcT
    have hsum_exc := rank8_secExc_sum f g res hplat16 w hw
    have hnp := rank8_Nplus_formula f g res cap hplat16
    have hpaI : cnt (clsA f g) = 0 := by
      have h := Int.toNat_of_nonneg (cnt_nonneg (clsA f g)); unfold pa at hpa; omega
    have hpcI : cnt (clsC f g) = 27 := by
      have h := Int.toNat_of_nonneg (cnt_nonneg (clsC f g)); unfold pc at hpc; omega
    rw [ht, hpaI, hpcI] at hnp
    have hcost_le : costR6 excl6MaskT96 [] 13 (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) +
        costR6 excl6MaskT96 [] 13 (0 - halfCnt w (clsA f g)) (51 - halfCnt w (clsB f g)) (27 - halfCnt w (clsC f g)) ≤
        13 := by omega
    have hcm := mem_genSplits (excl6Mask := excl6MaskT96) (eBounds := []) (t := 96)
      (a := 0) (b := 51) (c := 27) hleA hleB hleC hcost_le
    unfold canonPair at hcm; dsimp only at hcm
    split at hcm
    · left; exact hcm
    · right; rwa [← fA, ← fB, ← fC] at hcm
  -- Translate by `P = barycenter (clsC f g)` and apply `rank8_a0_far_yz_div4`!
  let P : W 8 := barycenter (clsC f g)
  let A' : W 8 → Bool := translate (clsA f g) P
  let B' : W 8 → Bool := translate (clsB f g) P
  let C' : W 8 → Bool := translate (clsC f g) P
  have hA'empty : ∀ x, A' x = false := by
    intro x
    cases h : A' x
    · rfl
    · exfalso
      have hm : x ∈ suppList A' := by unfold suppList; rw [List.mem_filter]; exact ⟨all_worlds 8 x, h⟩
      have hpos : 0 < (suppList A').length := List.length_pos_of_mem hm
      rw [suppList_translate_length, hlenA] at hpos; omega
  have hlenA' : (suppList A').length = 0 := by rw [suppList_translate_length, hlenA]
  have hlenB' : (suppList B').length = 51 := by rw [suppList_translate_length, hlenB]
  have hlenC' : (suppList C').length = 27 := by rw [suppList_translate_length, hlenC]
  have h0A' : A' (zero 8) = false := hA'empty (zero 8)
  have hfar : ∀ w : W 8, w ≠ zero 8 → (halfCnt w A', halfCnt w B', halfCnt w C') ∈ farWeights_0_51_27 := by
    intro w hw
    obtain ⟨hy2, hz2, hyz4⟩ := rank8_a0_far_yz_div4 f g res cap hrr hpa w hw
    unfold farWeights_0_51_27
    rw [List.mem_filter, List.mem_flatMap]
    refine ⟨?_, ?_⟩
    · have hsumA := halfCnt_add_false w (clsA f g); rw [hlenA] at hsumA
      have hsumB := halfCnt_add_false w (clsB f g); rw [hlenB] at hsumB
      have hsumC := halfCnt_add_false w (clsC f g); rw [hlenC] at hsumC
      have htrA := halfCnt_translate w P (clsA f g)
      have htrB := halfCnt_translate w P (clsB f g)
      have htrC := halfCnt_translate w P (clsC f g)
      change halfCnt w A' = _ at htrA
      change halfCnt w B' = _ at htrB
      change halfCnt w C' = _ at htrC
      rcases hgen w hw with hT | hF
      · refine ⟨(halfCnt w (clsA f g), halfCnt w (clsB f g), halfCnt w (clsC f g)), hT, ?_⟩
        cases hdw : dot 8 w P
        · rw [hdw] at htrA htrB htrC; simp only [Bool.false_eq_true, if_false] at htrA htrB htrC
          rw [htrA, htrB, htrC]; exact List.mem_cons_self _ _
        · rw [hdw] at htrA htrB htrC; simp only [if_true] at htrA htrB htrC
          rw [htrA, htrB, htrC]
          have e1 : 0 - halfCnt w (clsA f g) = halfCntFalse w (clsA f g) := by omega
          have e2 : 51 - halfCnt w (clsB f g) = halfCntFalse w (clsB f g) := by omega
          have e3 : 27 - halfCnt w (clsC f g) = halfCntFalse w (clsC f g) := by omega
          simp [e1, e2, e3]
      · refine ⟨(halfCntFalse w (clsA f g), halfCntFalse w (clsB f g), halfCntFalse w (clsC f g)), hF, ?_⟩
        cases hdw : dot 8 w P
        · rw [hdw] at htrA htrB htrC; simp only [Bool.false_eq_true, if_false] at htrA htrB htrC
          rw [htrA, htrB, htrC]
          have e1 : 0 - halfCntFalse w (clsA f g) = halfCnt w (clsA f g) := by omega
          have e2 : 51 - halfCntFalse w (clsB f g) = halfCnt w (clsB f g) := by omega
          have e3 : 27 - halfCntFalse w (clsC f g) = halfCnt w (clsC f g) := by omega
          simp [e1, e2, e3]
        · rw [hdw] at htrA htrB htrC; simp only [if_true] at htrA htrB htrC
          rw [htrA, htrB, htrC]; exact List.mem_cons_self _ _
    · simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨hy2, hz2⟩, hyz4⟩
  -- Case split on `B' (zero 8)` and `C' (zero 8)` (the 3 possible types of `P`: B, C, or D)!
  cases h0B : B' (zero 8)
  · cases h0C : C' (zero 8)
    · -- Case D: `P ∉ A ∪ B ∪ C`, size `(0, 51, 27)`!
      exact centered_cert_refute A' B' C'
        (fun x => clsA_B_disj f g (add 8 x P))
        (fun x => clsA_C_disj f g (add 8 x P))
        (fun x => clsB_C_disj f g (add 8 x P))
        h0A' h0B h0C 0 51 27 hlenA' hlenB' hlenC'
        farWeights_0_51_27 hfar cert_0_51_27_D cert_D_ok
    · -- Case C: `P ∈ C`, puncture `zero 8` from `C'`, size `(0, 51, 26)`!
      let C'' := puncture C' (zero 8)
      have hlenC'' : (suppList C'').length = 26 := by
        dsimp only [C'']; rw [suppList_puncture_length, hlenC', h0C]; rfl
      have hfarC'' : ∀ w : W 8, w ≠ zero 8 → (halfCnt w A', halfCnt w B', halfCnt w C'') ∈ farWeights_0_51_27 := by
        intro w hw
        have hp : halfCnt w C'' = halfCnt w C' := by
          dsimp only [C'']; rw [halfCnt_puncture, dot_comm 8 w (zero 8), dot_zero]; simp
        rw [hp]; exact hfar w hw
      exact centered_cert_refute A' B' C''
        (fun x => clsA_B_disj f g (add 8 x P))
        (fun x => by dsimp only [C'', puncture]; rw [hA'empty x]; rfl)
        (fun x => by
          dsimp only [C'', puncture]
          have h := clsB_C_disj f g (add 8 x P)
          change (B' x && C' x) = false at h
          cases hB : B' x <;> cases hC : C' x <;> simp_all)
        h0A' h0B (puncture_self C' (zero 8)) 0 51 26 hlenA' hlenB' hlenC''
        farWeights_0_51_27 hfarC'' cert_0_51_27_C cert_C_ok
  · -- Case B: `P ∈ B`, puncture `zero 8` from `B'`, size `(0, 50, 27)`!
    have h0C : C' (zero 8) = false := by
      have h := clsB_C_disj f g (add 8 (zero 8) P)
      change (B' (zero 8) && C' (zero 8)) = false at h
      rw [h0B, Bool.true_and] at h; exact h
    let B'' := puncture B' (zero 8)
    have hlenB'' : (suppList B'').length = 50 := by
      dsimp only [B'']; rw [suppList_puncture_length, hlenB', h0B]; rfl
    have hfarB'' : ∀ w : W 8, w ≠ zero 8 → (halfCnt w A', halfCnt w B'', halfCnt w C') ∈ farWeights_0_51_27 := by
      intro w hw
      have hp : halfCnt w B'' = halfCnt w B' := by
        dsimp only [B'']; rw [halfCnt_puncture, dot_comm 8 w (zero 8), dot_zero]; simp
      rw [hp]; exact hfar w hw
    exact centered_cert_refute A' B'' C'
      (fun x => by dsimp only [B'', puncture]; rw [hA'empty x]; rfl)
      (fun x => clsA_C_disj f g (add 8 x P))
      (fun x => by
        dsimp only [B'', puncture]
        have h := clsB_C_disj f g (add 8 x P)
        change (B' x && C' x) = false at h
        cases hB : B' x <;> cases hC : C' x <;> simp_all)
      h0A' (puncture_self B' (zero 8)) h0C 0 50 27 hlenA' hlenB'' hlenC'
      farWeights_0_51_27 hfarB'' cert_0_51_27_B cert_B_ok

end Balanced242T96_0_51_27

#print axioms Balanced242T96_0_51_27.cert_B_ok
#print axioms Balanced242T96_0_51_27.cert_C_ok
#print axioms Balanced242T96_0_51_27.cert_D_ok
#print axioms Balanced242T96_0_51_27.excl_96_0_51_27
