/-
  Balanced242T96Centered.lean — Kernel-verified Lean 4 exclusions for the two `t = 96`
  centered profiles `(96, 2, 47, 27, 8)` and `(96, 1, 54, 24, 8)` from
  `t96/check_centered_profiles.py` and `t96/centered_certificates.json`:

    1. `excl_96_2_47_27`: peels all 10 layer-0 anchor-pair certificates (kernel-verified in
       `Balanced242T96_2_47_27_L0`), excludes the single flag leaf `(0, 26, 10)`, and closes
       the surviving 50 splits (68 centered weights) via `Balanced242Centered.origin_pin_refute`
       with the exact 10-term origin-pinned Krawtchouk Farkas certificate.
    2. `excl_96_1_54_24`: peels all 20 layer-0 anchor-pair certificates (kernel-verified in
       `Balanced242T96_1_54_24_L0`), excludes the 3 flag leaves `(0, 44, 4), (0, 38, 6), (0, 40, 8)`,
       refutes both short-codeword residuals `(0, 46, 6)` and `(0, 48, 8)` via 7D centered
       Krawtchouk Farkas certificates, and closes the remaining `d ≥ 10` case unconditionally
       via `Balanced242Centered.no_binary_code_24_8_10` (Griesmer + sphere packing!).

  Zero Mathlib, zero `sorry`, zero `native_decide`, zero custom axioms.
-/
import Balanced242Centered
import Balanced242FastCond
import Balanced242T96Data
import Balanced242T96_2_47_27_L0
import Balanced242T96_1_54_24_L0

namespace Balanced242T96Centered

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Reduction Balanced242Plateau Balanced242Rank
open Balanced242Global Balanced242Rank8
open Balanced242Krawtchouk (suppList halfCnt halfCntFalse halfCnt_le halfCnt_add_false)
open Balanced242Farkas (Triple KrawEntry SectionEnumE genSplits buildAllowedMask peelSplits
  canonPair tripleLe costR6 mem_genSplits section_costR6_le sec_suppList_eq_halfCnt
  suppList_length_eq_total cond_cert_refute inAllowedMask checkLayerWithMask halfBitIdx)
open Balanced242FastCond (checkLayerFast2 checkLayerWithMask_of_fast2)
open Balanced242Centered (checkCenteredCert centeredWeights residualWeights
  origin_pin_refute origin_pin_residual_24_refute)
open Balanced242T96Data

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

private theorem testBit_eq_nat' (a i : Nat) : Balanced242Pair.testBit a i = a.testBit i := by
  unfold Balanced242Pair.testBit Nat.testBit
  rw [Nat.and_comm 1, Nat.and_one_is_mod]
  have h : (a >>> i) % 2 = 0 ∨ (a >>> i) % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> decide

private theorem testBit_or' (a b i : Nat) :
    Balanced242Pair.testBit (a ||| b) i = (Balanced242Pair.testBit a i || Balanced242Pair.testBit b i) := by
  rw [testBit_eq_nat', testBit_eq_nat', testBit_eq_nat', Nat.testBit_or]

private theorem testBit_one_shift_self' (i : Nat) : Balanced242Pair.testBit (1 <<< i) i = true := by
  unfold Balanced242Pair.testBit
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow, Nat.div_self (Nat.two_pow_pos i)]
  rfl

private theorem testBit_foldl_mono' (a b c : Nat) :
    ∀ (L : List Triple) (init : Nat) (idx : Nat),
      Balanced242Pair.testBit init idx = true →
      Balanced242Pair.testBit (L.foldl (fun acc p =>
        let q : Triple := (a - p.1, b - p.2.1, c - p.2.2)
        acc ||| (1 <<< halfBitIdx p) ||| (1 <<< halfBitIdx q)) init) idx = true
  | [], _, _, h => h
  | p :: t, init, idx, h => by
    apply testBit_foldl_mono' a b c t
    rw [testBit_or', testBit_or', h]; rfl

private theorem testBit_buildAllowedMask' (a b c : Nat) (anchors : List Triple)
    (p : Triple) (hp : p ∈ anchors) :
    Balanced242Pair.testBit (buildAllowedMask a b c anchors) (halfBitIdx p) = true ∧
    Balanced242Pair.testBit (buildAllowedMask a b c anchors) (halfBitIdx (a - p.1, b - p.2.1, c - p.2.2)) = true := by
  unfold buildAllowedMask
  have haux : ∀ (L : List Triple) (init : Nat), p ∈ L →
      Balanced242Pair.testBit (L.foldl (fun acc x =>
        let q : Triple := (a - x.1, b - x.2.1, c - x.2.2)
        acc ||| (1 <<< halfBitIdx x) ||| (1 <<< halfBitIdx q)) init) (halfBitIdx p) = true ∧
      Balanced242Pair.testBit (L.foldl (fun acc x =>
        let q : Triple := (a - x.1, b - x.2.1, c - x.2.2)
        acc ||| (1 <<< halfBitIdx x) ||| (1 <<< halfBitIdx q)) init) (halfBitIdx (a - p.1, b - p.2.1, c - p.2.2)) = true := by
    intro L; induction L with
    | nil => intro _ h; nomatch h
    | cons x t ih =>
      intro init hmem
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | ht
      · constructor
        · apply testBit_foldl_mono'; rw [testBit_or', testBit_or', testBit_one_shift_self']; simp
        · apply testBit_foldl_mono'; rw [testBit_or', testBit_one_shift_self']; simp
      · exact ih _ ht
  exact haux anchors 0 hp

/-- Generic layer-0 peeling + leaf exclusion bridge for any `t = 96` rank-8 profile:
    reduces `(f, g : Half)` to the surviving split list ready for `origin_pin_refute` or
    `origin_pin_residual_24_refute`. -/
private theorem rank8_peel_to_surviving
    (excl6Mask : Nat) (eBounds : List (Nat × Nat × Nat × Nat))
    (henum : SectionEnumE excl6Mask eBounds)
    (a b c : Nat) (ha64 : a < 64) (hb64 : b < 64) (hc64 : c < 64)
    (splits : List Triple) (mask : Nat)
    (layer0 : List (Triple × List (Nat × Int)))
    (leaves surviving : List Triple)
    (hgen : genSplits excl6Mask eBounds 96 a b c = splits)
    (hmask : buildAllowedMask a b c splits = mask)
    (hlay : checkLayerFast2 a b c mask layer0 = true)
    (hsurv : (peelSplits splits layer0).filter (fun p => !leaves.contains p) = surviving)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 96) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = a)
    (hb : (suppList (clsB f g)).length = b)
    (hc : (suppList (clsC f g)).length = c)
    (hno_leaves : ∀ w : W 8, w ≠ zero 8 →
      canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ∉ leaves) :
    ∀ w : W 8, w ≠ zero 8 →
      (halfCnt w (clsA f g), halfCnt w (clsB f g), halfCnt w (clsC f g)) ∈ surviving ∨
      (halfCntFalse w (clsA f g), halfCntFalse w (clsB f g), halfCntFalse w (clsC f g)) ∈ surviving := by
  have hcube8 : Cube (β8 f g) := Balanced242Global.cube8 f g res
  have h8 : ∀ u, transform (Balanced242RankCond.q8 f g) u = 16 ∨
      transform (Balanced242RankCond.q8 f g) u = -16 := by
    intro u
    have hrg := rr_good (β8 f g) hcube8
    rw [hrr, Int.one_mul] at hrg
    have hgu : good (β8 f g) u = true := all_true_of_total' (good (β8 f g)) hrg u
    have hsg := spec_good (β8 f g) hcube8 u
    rw [hgu, hrr] at hsg
    have hm : many 8 = 256 := by decide
    rw [hm] at hsg
    have hsq : transform (Balanced242RankCond.q8 f g) u * transform (Balanced242RankCond.q8 f g) u = 256 := by
      simpa [Balanced242RankCond.q8, Balanced242Plateau.ind] using hsg
    exact sq_cases _ 16 hsq
  have hmem0 : ∀ w : W 8, w ≠ zero 8 →
      canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ∈ splits := by
    intro w hw
    rw [← hgen]
    have hleA : halfCnt w (clsA f g) ≤ a := ha ▸ halfCnt_le w (clsA f g)
    have hleB : halfCnt w (clsB f g) ≤ b := hb ▸ halfCnt_le w (clsB f g)
    have hleC : halfCnt w (clsC f g) ≤ c := hc ▸ halfCnt_le w (clsC f g)
    let budget := (3 * 96 - 208) / 2 - a - c
    have hcF := (section_costR6_le excl6Mask eBounds henum f g res hicap hrr w hw false budget).2
    have hcT := (section_costR6_le excl6Mask eBounds henum f g res hicap hrr w hw true budget).2
    have sA := sec_suppList_eq_halfCnt w hw (clsA f g)
    have sB := sec_suppList_eq_halfCnt w hw (clsB f g)
    have sC := sec_suppList_eq_halfCnt w hw (clsC f g)
    have fA : halfCntFalse w (clsA f g) = a - halfCnt w (clsA f g) := by
      have := halfCnt_add_false w (clsA f g); omega
    have fB : halfCntFalse w (clsB f g) = b - halfCnt w (clsB f g) := by
      have := halfCnt_add_false w (clsB f g); omega
    have fC : halfCntFalse w (clsC f g) = c - halfCnt w (clsC f g) := by
      have := halfCnt_add_false w (clsC f g); omega
    rw [sA.1, sB.1, sC.1, fA, fB, fC] at hcF
    rw [sA.2, sB.2, sC.2] at hcT
    have hsum_exc := rank8_secExc_sum f g res h8 w hw
    have hnp := rank8_Nplus_formula f g res hicap h8
    have hpa : Balanced242Reduction.cnt (clsA f g) = (a : Int) := by
      unfold Balanced242Reduction.cnt; rw [← ha, suppList_length_eq_total]; rfl
    have hpc : Balanced242Reduction.cnt (clsC f g) = (c : Int) := by
      unfold Balanced242Reduction.cnt; rw [← hc, suppList_length_eq_total]; rfl
    rw [ht, hpa, hpc] at hnp
    have hcost_le : costR6 excl6Mask eBounds budget (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) +
        costR6 excl6Mask eBounds budget (a - halfCnt w (clsA f g)) (b - halfCnt w (clsB f g)) (c - halfCnt w (clsC f g)) ≤
        budget := by
      dsimp only [budget] at hcF hcT ⊢; omega
    exact mem_genSplits hleA hleB hleC hcost_le
  have hlay_orig : checkLayerWithMask a b c mask layer0 = true :=
    checkLayerWithMask_of_fast2 a b c mask layer0 hlay
  have hmem_peel : ∀ w : W 8, w ≠ zero 8 →
      canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ∈
        peelSplits splits layer0 := by
    intro w hw
    unfold peelSplits
    rw [List.mem_filter]
    refine ⟨hmem0 w hw, ?_⟩
    cases hct : (layer0.map Prod.fst).contains
        (canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)))
    · rfl
    · exfalso
      have hmem_k : canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ∈
          layer0.map Prod.fst := List.contains_iff_mem.mp hct
      rw [List.mem_map] at hmem_k
      rcases hmem_k with ⟨⟨lo, ws⟩, hpair_mem, hlo_eq⟩
      dsimp only at hlo_eq
      unfold checkLayerWithMask at hlay_orig
      rw [List.all_eq_true] at hlay_orig
      have hws_ok := hlay_orig (lo, ws) hpair_mem
      have hallow : ∀ u : W 8, u ≠ zero 8 →
          inAllowedMask mask (halfCntFalse u (clsA f g), halfCntFalse u (clsB f g), halfCntFalse u (clsC f g)) = true ∧
          inAllowedMask mask (halfCnt u (clsA f g), halfCnt u (clsB f g), halfCnt u (clsC f g)) = true := by
        intro u hu
        rw [← hmask]
        have hmu := hmem0 u hu
        have hbits := testBit_buildAllowedMask' a b c splits _ hmu
        have huA : halfCnt u (clsA f g) ≤ a := ha ▸ halfCnt_le u (clsA f g)
        have huB : halfCnt u (clsB f g) ≤ b := hb ▸ halfCnt_le u (clsB f g)
        have huC : halfCnt u (clsC f g) ≤ c := hc ▸ halfCnt_le u (clsC f g)
        have hfA : halfCntFalse u (clsA f g) = a - halfCnt u (clsA f g) := by
          have := halfCnt_add_false u (clsA f g); omega
        have hfB : halfCntFalse u (clsB f g) = b - halfCnt u (clsB f g) := by
          have := halfCnt_add_false u (clsB f g); omega
        have hfC : halfCntFalse u (clsC f g) = c - halfCnt u (clsC f g) := by
          have := halfCnt_add_false u (clsC f g); omega
        have hltF : halfCntFalse u (clsA f g) < 64 ∧ halfCntFalse u (clsB f g) < 64 ∧ halfCntFalse u (clsC f g) < 64 := by omega
        have hltT : halfCnt u (clsA f g) < 64 ∧ halfCnt u (clsB f g) < 64 ∧ halfCnt u (clsC f g) < 64 := by omega
        unfold canonPair at hbits
        cases hfl : tripleLe (halfCnt u (clsA f g), halfCnt u (clsB f g), halfCnt u (clsC f g))
            (a - halfCnt u (clsA f g), b - halfCnt u (clsB f g), c - halfCnt u (clsC f g))
        · simp only [hfl, Bool.false_eq_true, if_false,
            Nat.sub_sub_self huA, Nat.sub_sub_self huB, Nat.sub_sub_self huC] at hbits
          rw [← hfA, ← hfB, ← hfC] at hbits
          exact ⟨by unfold inAllowedMask; simp [hltF.1, hltF.2.1, hltF.2.2, hbits.1],
                 by unfold inAllowedMask; simp [hltT.1, hltT.2.1, hltT.2.2, hbits.2]⟩
        · simp only [hfl, if_true] at hbits
          rw [← hfA, ← hfB, ← hfC] at hbits
          exact ⟨by unfold inAllowedMask; simp [hltF.1, hltF.2.1, hltF.2.2, hbits.2],
                 by unfold inAllowedMask; simp [hltT.1, hltT.2.1, hltT.2.2, hbits.1]⟩
      exact cond_cert_refute f g res hicap hrr a b c ha hb hc mask hallow w hw lo hlo_eq.symm ws hws_ok
  intro w hw
  have hmem_surv : canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ∈ surviving := by
    rw [← hsurv, List.mem_filter]
    refine ⟨hmem_peel w hw, ?_⟩
    cases hct : leaves.contains
        (canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)))
    · rfl
    · exfalso; exact hno_leaves w hw (List.contains_iff_mem.mp hct)
  have fA : a - halfCnt w (clsA f g) = halfCntFalse w (clsA f g) := by
    have := halfCnt_add_false w (clsA f g); omega
  have fB : b - halfCnt w (clsB f g) = halfCntFalse w (clsB f g) := by
    have := halfCnt_add_false w (clsB f g); omega
  have fC : c - halfCnt w (clsC f g) = halfCntFalse w (clsC f g) := by
    have := halfCnt_add_false w (clsC f g); omega
  unfold canonPair at hmem_surv
  rw [fA, fB, fC] at hmem_surv
  cases hfl : tripleLe (halfCnt w (clsA f g), halfCnt w (clsB f g), halfCnt w (clsC f g))
      (halfCntFalse w (clsA f g), halfCntFalse w (clsB f g), halfCntFalse w (clsC f g))
  · simp only [hfl, Bool.false_eq_true, if_false] at hmem_surv
    exact Or.inr hmem_surv
  · simp only [hfl, if_true] at hmem_surv
    exact Or.inl hmem_surv

/-! ### Kernel checks for `(96, 2, 47, 27, 8)` -/

private theorem gen_96_2_47_27 :
    genSplits excl6MaskT96 eBoundsT96 96 2 47 27 = splits_96_2_47_27 := by
  decide +kernel

private theorem mask_eq_96_2_47_27 :
    buildAllowedMask 2 47 27 splits_96_2_47_27 = mask_96_2_47_27 := by
  decide +kernel

private theorem surv_eq_96_2_47_27 :
    (peelSplits splits_96_2_47_27 layer0_96_2_47_27).filter
      (fun p => !leaves_96_2_47_27.contains p) = surviving_96_2_47_27 := by
  decide +kernel

private theorem dual_ok_96_2_47_27 :
    checkCenteredCert 8 1 47 27 (centeredWeights 2 47 27 surviving_96_2_47_27) dual_96_2_47_27 = true := by
  decide +kernel

/-- **Kernel-verified exclusion of `(96, 2, 47, 27, 8)`** (`t96/check_centered_profiles.py`):
    modulo `SectionEnumE excl6MaskT96 eBoundsT96` (the 242 excluded rank-6 sections + 6 capped
    `t96_sweep1` bounds) and non-occurrence of the single flag leaf `(0, 26, 10)`, no balanced
    9-variable NL242 rank-8 function with `t = 96` and profile `(2, 47, 27)` can exist. -/
theorem excl_96_2_47_27 (henum : SectionEnumE excl6MaskT96 eBoundsT96)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 96) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 2)
    (hb : (suppList (clsB f g)).length = 47)
    (hc : (suppList (clsC f g)).length = 27)
    (hno_leaf : ∀ w : W 8, w ≠ zero 8 →
      canonPair 2 47 27 (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ≠ (0, 26, 10)) :
    False := by
  have hno_leaves : ∀ w : W 8, w ≠ zero 8 →
      canonPair 2 47 27 (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ∉ leaves_96_2_47_27 := by
    intro w hw hmem
    unfold leaves_96_2_47_27 at hmem
    rw [List.mem_singleton] at hmem
    exact hno_leaf w hw hmem
  have hsurv := rank8_peel_to_surviving excl6MaskT96 eBoundsT96 henum
    2 47 27 (by decide) (by decide) (by decide)
    splits_96_2_47_27 mask_96_2_47_27 layer0_96_2_47_27 leaves_96_2_47_27 surviving_96_2_47_27
    gen_96_2_47_27 mask_eq_96_2_47_27 Balanced242T96_2_47_27_L0.layer0_ok surv_eq_96_2_47_27
    f g res hicap ht hrr ha hb hc hno_leaves
  exact origin_pin_refute (clsA f g) (clsB f g) (clsC f g)
    (clsA_B_disj f g) (clsA_C_disj f g) (clsB_C_disj f g)
    2 47 27 (by decide) ha hb hc surviving_96_2_47_27 hsurv dual_96_2_47_27 dual_ok_96_2_47_27

/-! ### Kernel checks for `(96, 1, 54, 24, 8)` -/

private theorem gen_96_1_54_24 :
    genSplits excl6MaskT96 eBoundsT96 96 1 54 24 = splits_96_1_54_24 := by
  decide +kernel

private theorem mask_eq_96_1_54_24 :
    buildAllowedMask 1 54 24 splits_96_1_54_24 = mask_96_1_54_24 := by
  decide +kernel

private theorem surv_eq_96_1_54_24 :
    (peelSplits splits_96_1_54_24 layer0_96_1_54_24).filter
      (fun p => !leaves_96_1_54_24.contains p) = surviving_96_1_54_24 := by
  decide +kernel

private def checkAllShortResiduals : Bool :=
  let wts := centeredWeights 1 54 24 surviving_96_1_54_24
  wts.all fun w =>
    if w.2.2 < 10 then
      resCerts_96_1_54_24.any fun (anc, cert) =>
        decide (anc = w) &&
        checkCenteredCert 7 (0 - w.1) (54 - w.2.1) (24 - w.2.2)
          (residualWeights 0 54 24 wts w) cert
    else true

private theorem residuals_ok_96_1_54_24 : checkAllShortResiduals = true := by
  decide +kernel

/-- **Kernel-verified exclusion of `(96, 1, 54, 24, 8)`** (`t96/check_centered_profiles.py`):
    modulo `SectionEnumE excl6MaskT96 eBoundsT96` and non-occurrence of the 3 flag leaves
    `(0, 44, 4), (0, 38, 6), (0, 40, 8)`, all 20 layer-0 anchor-pair certs + both 7D residual
    Krawtchouk Farkas certs `(0, 46, 6)` and `(0, 48, 8)` + the unconditional coding-theory
    impossibility `no_binary_code_24_8_10` (Griesmer + sphere packing) refute `(1, 54, 24)`. -/
theorem excl_96_1_54_24 (henum : SectionEnumE excl6MaskT96 eBoundsT96)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 96) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 1)
    (hb : (suppList (clsB f g)).length = 54)
    (hc : (suppList (clsC f g)).length = 24)
    (hno_leaves : ∀ w : W 8, w ≠ zero 8 →
      canonPair 1 54 24 (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ∉
        [(0, 44, 4), (0, 38, 6), (0, 40, 8)]) :
    False := by
  have hno_leaves' : ∀ w : W 8, w ≠ zero 8 →
      canonPair 1 54 24 (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ∉ leaves_96_1_54_24 := by
    intro w hw hmem
    have heq_l : leaves_96_1_54_24 = [(0, 38, 6), (0, 40, 8), (0, 44, 4)] := rfl
    rw [heq_l] at hmem
    apply hno_leaves w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
    rcases hmem with h1 | h2 | h3
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
    · exact Or.inl h3
  have hsurv := rank8_peel_to_surviving excl6MaskT96 eBoundsT96 henum
    1 54 24 (by decide) (by decide) (by decide)
    splits_96_1_54_24 mask_96_1_54_24 layer0_96_1_54_24 leaves_96_1_54_24 surviving_96_1_54_24
    gen_96_1_54_24 mask_eq_96_1_54_24 Balanced242T96_1_54_24_L0.layer0_ok surv_eq_96_1_54_24
    f g res hicap ht hrr ha hb hc hno_leaves'
  have hcover : ∀ w, w ∈ centeredWeights 1 54 24 surviving_96_1_54_24 → w.2.2 < 10 →
      ∃ cert, (w, cert) ∈ resCerts_96_1_54_24 ∧
        checkCenteredCert 7 (0 - w.1) (54 - w.2.1) (24 - w.2.2)
          (residualWeights 0 54 24 (centeredWeights 1 54 24 surviving_96_1_54_24) w) cert = true := by
    intro w hw hlt
    have hck := residuals_ok_96_1_54_24
    unfold checkAllShortResiduals at hck
    rw [List.all_eq_true] at hck
    have hw_ok := hck w hw
    simp only [hlt, if_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hw_ok
    rcases hw_ok with ⟨⟨anc, cert⟩, hmem_rc, hanc_eq, hcert_ok⟩
    dsimp only at hanc_eq hcert_ok
    subst hanc_eq
    exact ⟨cert, hmem_rc, hcert_ok⟩
  exact origin_pin_residual_24_refute (clsA f g) (clsB f g) (clsC f g)
    (clsA_B_disj f g) (clsA_C_disj f g) (clsB_C_disj f g)
    54 ha hb hc surviving_96_1_54_24 hsurv resCerts_96_1_54_24 hcover

end Balanced242T96Centered

#print axioms Balanced242T96Centered.excl_96_2_47_27
#print axioms Balanced242T96Centered.excl_96_1_54_24
