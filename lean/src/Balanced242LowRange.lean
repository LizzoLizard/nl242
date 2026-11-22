/-
  Exclusion of the entire lower agreement range `t ≤ 84` from `SectionEnum`, combined with
  `Balanced242Complete.no_242_86_to_92` and `Balanced242Endpoint.agreement_and_peak_range` to
  obtain the coordinate-free window theorem for balanced 9-variable Boolean functions of
  nonlinearity 242:

    * `agreements f g ∈ [94, 118]` (even),
    * `axisAgreements F ∈ [188, 236]` (multiple of 4),
    * `autocorr F (supportXor F) ∈ [-136, -40]` (multiple of 8).

  Everything uses only `SectionEnum` and `[propext, Quot.sound]`.
-/
import Balanced242Complete
import Balanced242No244

namespace Balanced242LowRange
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Blocks Balanced242Support Balanced242Endpoint
open Balanced242Global Balanced242Complete Balanced242No244
open Balanced242Reduction (ind cnt low nz clsA clsB clsC hi_values profile_mass
  low_spec transform_ind_zero nz_total parseval2)
open Balanced242SectionFacts (secD secH secCnt secD_bound secH_spec secH_odd
  low_eq_secCnt cnt_split secD_sq_even ind_nonneg')
open Balanced242Coord (axisAgreements autocorr autocorr_eq_axisAgreements
  supportXor_ne_zero_of_peak28 to_adapted)

private theorem sq_le_sq (x B : Int) (h1 : -B ≤ x) (h2 : x ≤ B) : x * x ≤ B * B := by
  have hnn : 0 ≤ (B - x) * (B + x) := Int.mul_nonneg (by omega) (by omega)
  have hmul : (B - x) * (B + x) = B * B - x * x := by
    rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm x B]; omega
  omega

private theorem secCnt_nonneg (P : W 8 → Bool) (w : W 8) (c : Bool) : 0 ≤ secCnt P w c := by
  unfold secCnt
  rw [← total_zero 7]
  exact total_mono 7 _ _ (fun a => ind_nonneg' P _)

/-- Every hyperplane section of an adapted balanced-242 high block has mass at least 88. -/
theorem sec_mass_ge_88 (enum : SectionEnum) (f g : Half)
    (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)
    (hev : agreements f g % 2 = 0) (w : W 8) (hw : w ≠ zero 8) (c : Bool) :
    88 ≤ 6 * secCnt (clsA f g) w c + 3 * secCnt (clsB f g) w c + 5 * secCnt (clsC f g) w c := by
  have hA0 := secCnt_nonneg (clsA f g) w c
  have hB0 := secCnt_nonneg (clsB f g) w c
  have hC0 := secCnt_nonneg (clsC f g) w c
  let X : Nat := (secCnt (clsA f g) w c).toNat
  let Y : Nat := (secCnt (clsB f g) w c).toNat
  let Z : Nat := (secCnt (clsC f g) w c).toNat
  have hX : (X : Int) = total 7 (fun a => if (secH f g w c a).natAbs = 1 then (1 : Int) else 0) := by
    have heq : (X : Int) = secCnt (clsA f g) w c := by dsimp only [X]; omega
    rw [heq]; unfold secCnt
    apply congrArg (total 7); funext a
    unfold ind clsA secH
    rcases hi_values f g res cap (Balanced242Hyperplane.secPt 7 w c a) with h | h | h | h | h | h | h | h <;>
      rw [h] <;> decide
  have hY : (Y : Int) = total 7 (fun a => if (secH f g w c a).natAbs = 5 then (1 : Int) else 0) := by
    have heq : (Y : Int) = secCnt (clsB f g) w c := by dsimp only [Y]; omega
    rw [heq]; unfold secCnt
    apply congrArg (total 7); funext a
    unfold ind clsB secH
    rcases hi_values f g res cap (Balanced242Hyperplane.secPt 7 w c a) with h | h | h | h | h | h | h | h <;>
      rw [h] <;> decide
  have hZ : (Z : Int) = total 7 (fun a => if (secH f g w c a).natAbs = 3 then (1 : Int) else 0) := by
    have heq : (Z : Int) = secCnt (clsC f g) w c := by dsimp only [Z]; omega
    rw [heq]; unfold secCnt
    apply congrArg (total 7); funext a
    unfold ind clsC secH
    rcases hi_values f g res cap (Balanced242Hyperplane.secPt 7 w c a) with h | h | h | h | h | h | h | h <;>
      rw [h] <;> decide
  have hcapH (a : W 7) : secH f g w c a % 2 = 1 ∧ (secH f g w c a).natAbs ≤ 7 := by
    refine ⟨secH_odd f g res w c a, ?_⟩
    unfold secH
    rcases hi_values f g res cap (Balanced242Hyperplane.secPt 7 w c a) with h | h | h | h | h | h | h | h <;>
      rw [h] <;> decide
  have h88 := (enum (secD f g w c) (secH f g w c) (secD_bound f g w c)
    (secH_spec f g res w hw c) hcapH (secD_sq_even f g w hw c hev) X Y Z hX hY hZ).1
  omega

/-- Parseval on the mass weight excludes `t ≤ 84`, leaving `86 ≤ agreements f g`. -/
theorem agreements_ge_86 (enum : SectionEnum) (f g : Half)
    (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)
    (hev : agreements f g % 2 = 0) :
    86 ≤ agreements f g := by
  let T : Int := 6 * cnt (clsA f g) + 3 * cnt (clsB f g) + 5 * cnt (clsC f g)
  have hT : T = 8 * agreements f g - 480 := profile_mass f g res cap
  -- First, any nonzero direction forces T ≥ 176, i.e. agreements ≥ 82
  let w0 : W 8 := (true, zero 7)
  have hw0 : w0 ≠ zero 8 := fun h => Bool.noConfusion (congrArg Prod.fst h)
  have h176 : 176 ≤ T := by
    have m0 := sec_mass_ge_88 enum f g res cap hev w0 hw0 false
    have m1 := sec_mass_ge_88 enum f g res cap hev w0 hw0 true
    have sA := cnt_split w0 hw0 (clsA f g)
    have sB := cnt_split w0 hw0 (clsB f g)
    have sC := cnt_split w0 hw0 (clsC f g)
    dsimp only [T]; omega
  -- Second, Parseval on the mass weight `Wwt = 6*1_A + 3*1_B + 5*1_C`
  let Wwt : W 8 → Int := fun a =>
    6 * ind (clsA f g) a + 3 * ind (clsB f g) a + 5 * ind (clsC f g) a
  have hWtr (w : W 8) : transform Wwt w =
      6 * transform (ind (clsA f g)) w + 3 * transform (ind (clsB f g)) w +
      5 * transform (ind (clsC f g)) w := by
    unfold transform
    simp only [Wwt, Int.add_mul, Int.mul_assoc, total_add, total_scale]
  have hW0 : transform Wwt (zero 8) = T := by
    rw [hWtr, transform_ind_zero, transform_ind_zero, transform_ind_zero]
  have hWdiff (w : W 8) (hw : w ≠ zero 8) :
      -(T - 176) ≤ transform Wwt w ∧ transform Wwt w ≤ T - 176 := by
    have m0 := sec_mass_ge_88 enum f g res cap hev w hw false
    have m1 := sec_mass_ge_88 enum f g res cap hev w hw true
    have lA := low_spec (clsA f g) w; have lB := low_spec (clsB f g) w; have lC := low_spec (clsC f g) w
    have eA := low_eq_secCnt w hw (clsA f g); have eB := low_eq_secCnt w hw (clsB f g); have eC := low_eq_secCnt w hw (clsC f g)
    have sA := cnt_split w hw (clsA f g); have sB := cnt_split w hw (clsB f g); have sC := cnt_split w hw (clsC f g)
    rw [hWtr]; dsimp only [T]; exact ⟨by omega, by omega⟩
  have hupper : total 8 (fun w => nz w * (transform Wwt w * transform Wwt w)) ≤
      255 * ((T - 176) * (T - 176)) := by
    have pt (w : W 8) : nz w * (transform Wwt w * transform Wwt w) ≤
        nz w * ((T - 176) * (T - 176)) := by
      if hw : w = zero 8 then
        subst hw; simp [nz]
      else
        simp only [nz, if_neg hw, Int.one_mul]
        exact sq_le_sq _ _ (hWdiff w hw).1 (hWdiff w hw).2
    have hsum := total_mono 8 _ _ pt
    have hconst : total 8 (fun w => nz w * ((T - 176) * (T - 176))) =
        255 * ((T - 176) * (T - 176)) := by
      rw [nz_total, total_const]
      have hm256 : many 8 = 256 := by decide
      rw [hm256]
      have h255 : (256 : Int) * ((T - 176) * (T - 176)) - (T - 176) * (T - 176) =
          (256 - 1) * ((T - 176) * (T - 176)) := by
        rw [Int.sub_mul 256 1, Int.one_mul]
      exact h255
    rw [hconst] at hsum; exact hsum
  have hpar : total 8 (fun w => nz w * (transform Wwt w * transform Wwt w)) =
      256 * total 8 (fun a => Wwt a * Wwt a) - T * T := by
    rw [nz_total, parseval2, hW0]
    have hm256 : many 8 = 256 := by decide
    rw [hm256]
  have h3T : 3 * T ≤ total 8 (fun a => Wwt a * Wwt a) := by
    have hsumW : total 8 Wwt = T := by
      simp only [Wwt, total_add, total_scale]; rfl
    rw [← hsumW, ← total_scale]
    apply total_mono 8; intro a
    dsimp only [Wwt, ind, clsA, clsB, clsC]
    rcases hi_values f g res cap a with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hineq : 256 * (3 * T) - T * T ≤ 255 * ((T - 176) * (T - 176)) := by omega
  have hge82 : 82 ≤ agreements f g := by omega
  if h86 : 86 ≤ agreements f g then
    exact h86
  else if h82 : agreements f g = 82 then
    exfalso; rw [h82] at hT; have hT176 : T = 176 := hT.trans (by decide)
    rw [hT176] at hineq; omega
  else if h84 : agreements f g = 84 then
    exfalso; rw [h84] at hT; have hT192 : T = 192 := hT.trans (by decide)
    rw [hT192] at hineq; omega
  else
    exfalso; omega

/-- Constructive parity of `agreements f g` for any balanced halves `(f, g)`. -/
theorem agreements_even (f g : Half) (bal : total 9 (fun x => sign (halves f g x)) = 0) :
    agreements f g % 2 = 0 := by
  have split0 : total 8 (fun x => sign (f x) + sign (g x)) = 0 := by rw [total_add]; exact bal
  have signs (b c : Bool) : sign b + sign c = 2 * (sameBit false b c - sameBit true b c) := by
    cases b <;> cases c <;> decide
  simp only [signs, total_scale, total_sub] at split0
  change 2 * (countPair f g false - countPair f g true) = 0 at split0
  have heqv : countPair f g false = countPair f g true := by
    have h0 : countPair f g false - countPair f g true = 0 :=
      Int.eq_of_mul_eq_mul_left (by decide) (split0.trans (Int.mul_zero 2).symm)
    have h1 := congrArg (· + countPair f g true) h0
    simpa [Int.sub_add_cancel] using h1
  unfold agreements
  rw [heqv]
  have h2 : countPair f g true + countPair f g true = 2 * countPair f g true := by
    have := Int.add_mul (1 : Int) 1 (countPair f g true)
    simpa [Int.one_mul] using this.symm
  rw [h2]
  exact Int.mul_emod_right 2 _

/-- Constructive lower-bound theorem (`[propext, Quot.sound]`): every adapted balanced-242 pair
satisfies `94 ≤ agreements f g` and `agreements f g % 2 = 0`, assuming only `SectionEnum`. -/
theorem agreements_ge_94 (enum : SectionEnum) (f g : Half)
    (axis : supportXor (halves f g) = (true, zero 8))
    (bal : total 9 (fun x => sign (halves f g x)) = 0)
    (cap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28) :
    94 ≤ agreements f g ∧ agreements f g % 2 = 0 := by
  have hev : agreements f g % 2 = 0 := agreements_even f g bal
  have hge86 := agreements_ge_86 enum f g (fun a => (adapted_blocks f g axis bal a).2)
    (fun a => (cap a).2) hev
  have ⟨h86, h88, h90, h92⟩ := no_242_86_to_92 enum f g axis bal cap
  refine ⟨?_, hev⟩
  if h94 : 94 ≤ agreements f g then exact h94
  else if e86 : agreements f g = 86 then exact absurd e86 h86
  else if e88 : agreements f g = 88 then exact absurd e88 h88
  else if e90 : agreements f g = 90 then exact absurd e90 h90
  else if e92 : agreements f g = 92 then exact absurd e92 h92
  else exfalso; omega

/-- Coordinate-free constructive lower bound (`[propext, Quot.sound]`): any balanced 9-variable
Boolean function of nonlinearity ≥ 242 (`∀ a, |W_F(a)| ≤ 28`, no peak assumption needed)
satisfies `188 ≤ axisAgreements F` and `4 ∣ axisAgreements F`, assuming only `SectionEnum`. -/
theorem axisAgreements_ge_188 (enum : SectionEnum) (F : W 9 → Bool)
    (bal : total 9 (fun x => sign (F x)) = 0)
    (cap : ∀ a, (booleanSpec F a).natAbs ≤ 28) :
    188 ≤ axisAgreements F ∧ axisAgreements F % 4 = 0 := by
  have hs := supportXor_ne_zero_of_cap28 F bal cap
  obtain ⟨f, g, haxis, hbal, hlo, hhi, h2t⟩ := to_adapted F bal hs
  have hcap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28 := fun a => by
    obtain ⟨b1, hb1⟩ := hlo a
    obtain ⟨b2, hb2⟩ := hhi a
    exact ⟨hb1 ▸ cap b1, hb2 ▸ cap b2⟩
  have ⟨hlo94, hev⟩ := agreements_ge_94 enum f g haxis hbal hcap
  let k := agreements f g / 2
  have hdiv : agreements f g = 2 * k := by
    have h := Int.ediv_add_emod (agreements f g) 2
    rw [hev, Int.add_zero] at h; exact h.symm
  have h4 : axisAgreements F = 4 * k := by
    calc axisAgreements F = 2 * agreements f g := h2t.symm
      _ = 2 * (2 * k) := by rw [hdiv]
      _ = 4 * k := by rw [← Int.mul_assoc]; rfl
  refine ⟨?_, ?_⟩
  · rw [← h2t]; exact Int.mul_le_mul_of_nonneg_left hlo94 (by decide)
  · rw [h4]; exact Int.mul_emod_right 4 k

/-- Coordinate-free constructive autocorrelation lower bound (`[propext, Quot.sound]`):
any balanced 9-variable Boolean function with `|W_F| ≤ 28` satisfies `-136 ≤ Δ_F(supportXor F)`
and `8 ∣ Δ_F(supportXor F)`. -/
theorem autocorr_ge_m136 (enum : SectionEnum) (F : W 9 → Bool)
    (bal : total 9 (fun x => sign (F x)) = 0)
    (cap : ∀ a, (booleanSpec F a).natAbs ≤ 28) :
    -136 ≤ autocorr F (supportXor F) ∧ autocorr F (supportXor F) % 8 = 0 := by
  have hrel := autocorr_eq_axisAgreements F
  have ⟨h1, h2⟩ := axisAgreements_ge_188 enum F bal cap
  let k := axisAgreements F / 4
  have hdiv : axisAgreements F = 4 * k := by
    have h := Int.ediv_add_emod (axisAgreements F) 4
    rw [h2, Int.add_zero] at h; exact h.symm
  have h8 : autocorr F (supportXor F) = 8 * (k - 64) := by
    calc autocorr F (supportXor F) = 2 * axisAgreements F - 512 := hrel
      _ = 2 * (4 * k) - 512 := by rw [hdiv]
      _ = 8 * k - 8 * 64 := by rw [← Int.mul_assoc]; rfl
      _ = 8 * (k - 64) := (Int.mul_sub 8 k 64).symm
  refine ⟨?_, ?_⟩
  · rw [hrel]
    have h2' := Int.mul_le_mul_of_nonneg_left h1 (by decide : (0 : Int) ≤ 2)
    exact Int.sub_le_sub_right h2' 512
  · rw [h8]; exact Int.mul_emod_right 8 (k - 64)

/-- Adapted-coordinate full window theorem: every adapted balanced-242 pair has even agreement
count in `[94, 118]`, assuming only `SectionEnum`. -/
theorem agreements_window_94_to_118 (enum : SectionEnum) (f g : Half)
    (axis : supportXor (halves f g) = (true, zero 8))
    (bal : total 9 (fun x => sign (halves f g x)) = 0)
    (cap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28) :
    94 ≤ agreements f g ∧ agreements f g ≤ 118 ∧ agreements f g % 2 = 0 := by
  have ⟨hge94, hev⟩ := agreements_ge_94 enum f g axis bal cap
  have ⟨_, hle118, _⟩ := agreement_and_peak_range f g axis bal cap
  exact ⟨hge94, hle118, hev⟩

/-- Coordinate-free full window theorem: any balanced 9-variable Boolean function of nonlinearity
≥ 242 (`∀ a, |W_F(a)| ≤ 28`) satisfies `188 ≤ axisAgreements F ≤ 236` and
`4 ∣ axisAgreements F`, assuming only `SectionEnum`. -/
theorem axisAgreements_window_242 (enum : SectionEnum) (F : W 9 → Bool)
    (bal : total 9 (fun x => sign (F x)) = 0)
    (cap : ∀ a, (booleanSpec F a).natAbs ≤ 28) :
    188 ≤ axisAgreements F ∧ axisAgreements F ≤ 236 ∧ axisAgreements F % 4 = 0 := by
  have hs := supportXor_ne_zero_of_cap28 F bal cap
  obtain ⟨f, g, haxis, hbal, hlo, hhi, h2t⟩ := to_adapted F bal hs
  have hcap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28 := fun a => by
    obtain ⟨b1, hb1⟩ := hlo a
    obtain ⟨b2, hb2⟩ := hhi a
    exact ⟨hb1 ▸ cap b1, hb2 ▸ cap b2⟩
  have ⟨hlo94, hhi118, hev⟩ := agreements_window_94_to_118 enum f g haxis hbal hcap
  omega

/-- Coordinate-free autocorrelation window: any balanced 9-variable Boolean function with
`|W_F| ≤ 28` satisfies `-136 ≤ Δ_F(supportXor F) ≤ -40` and `8 ∣ Δ_F(supportXor F)`. -/
theorem autocorr_window_242 (enum : SectionEnum) (F : W 9 → Bool)
    (bal : total 9 (fun x => sign (F x)) = 0)
    (cap : ∀ a, (booleanSpec F a).natAbs ≤ 28) :
    -136 ≤ autocorr F (supportXor F) ∧ autocorr F (supportXor F) ≤ -40 ∧
    autocorr F (supportXor F) % 8 = 0 := by
  have hrel := autocorr_eq_axisAgreements F
  have ⟨h1, h2, h3⟩ := axisAgreements_window_242 enum F bal cap
  omega

end Balanced242LowRange

#print axioms Balanced242LowRange.sec_mass_ge_88
#print axioms Balanced242LowRange.agreements_ge_86
#print axioms Balanced242LowRange.agreements_ge_94
#print axioms Balanced242LowRange.axisAgreements_ge_188
#print axioms Balanced242LowRange.autocorr_ge_m136
#print axioms Balanced242LowRange.agreements_window_94_to_118
#print axioms Balanced242LowRange.axisAgreements_window_242
#print axioms Balanced242LowRange.autocorr_window_242
