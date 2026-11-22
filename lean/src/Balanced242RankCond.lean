/-
  The global rank condition r ∈ ranks t k, derived from the halves.

    * Phase identity: sum_x U(x) q^(x) = 32 (2t - 232 - k), with k = #(|hi| in {4, 12}).
    * q^ takes values 0, +-M on the support (M = 256 / 2^(r/2)), so M divides the sum and
      the quotient is at most min(2^r, 256 - t) in absolute value.
    * Low residue count Z = #{a : lo(a) = 0 mod 16}: by the coupled phase identity
      2Z - 256 = q(0) q^(supportXor g), so Z is 128 or 128 +- M/2 (128 only if r < 8);
      Z > 0 from the balanced DC, and the low energy budget holds.
  The one extra hypothesis is Z ≠ 64 (the residue-flat case, excluded in AGREEMENT_RANGE.md
  by the switching argument and the covering-radius theorem).
-/
import Balanced242Global
import Balanced242HighSections

namespace Balanced242RankCond
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Global
open Balanced242Reduction (cnt clsA clsB clsC hi_values pa pc profile_mass)
open Balanced242SectionFacts (U hi_U point_le_total)
open Balanced242Plateau (phase_bt)
open Balanced242Rank (good rr spec_good)
open Balanced242Pair (ranks rankOK)

local notation "phase" => Balanced242Section0320.phase
local notation "bind" => Balanced242Plateau.ind
local notation "rind" => Balanced242Reduction.ind

def q8 (f g : Half) (a : W 8) : Int := sign (β8 f g a)
def Zc (f g : Half) : Int := total 8 (fun a => if lo f g a % 16 = 0 then 1 else 0)

/-- Packaging of `rankOK` from its ingredients. -/
theorem rankOK_of (t k r Z : Nat) (K : Int)
    (hz : Z ∈ [128 - (256 >>> (r / 2)) / 2, 128 + (256 >>> (r / 2)) / 2] ++
      (if r < 8 then [128] else []))
    (hZ0 : 0 < Z) (hZ64 : Z ≠ 64) (hbud : 1024 * t + 320 * Z + 256 ≤ 147456)
    (hamp : 0 < 256 >>> (r / 2))
    (hq : (32 : Int) * ((2 : Int) * (t : Int) - (232 : Int) - (k : Int)) =
      ((256 >>> (r / 2) : Nat) : Int) * K)
    (hK : K.natAbs ≤ min (2 ^ r) (256 - t)) : rankOK t k r = true := by
  have any : ([128 - (256 >>> (r / 2)) / 2, 128 + (256 >>> (r / 2)) / 2] ++
      (if r < 8 then [128] else [])).any (fun z0 => decide (0 < z0) && z0 != 64 &&
        decide (1024 * t + 320 * z0 + 256 ≤ 147456)) = true := by
    rw [List.any_eq_true]
    refine ⟨Z, hz, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    exact ⟨⟨hZ0, hZ64⟩, hbud⟩
  have hmod : ((32 : Int) * ((2 : Int) * (t : Int) - (232 : Int) - (k : Int))) %
      ((256 >>> (r / 2) : Nat) : Int) = 0 := by
    rw [hq]; exact Int.mul_emod_right _ _
  have hdiv : ((32 : Int) * ((2 : Int) * (t : Int) - (232 : Int) - (k : Int))) /
      ((256 >>> (r / 2) : Nat) : Int) = K := by
    rw [hq, Int.mul_ediv_cancel_left _ (by omega)]
  show (_ && _ && _) = true
  rw [any, hmod, hdiv, decide_eq_true hK]
  rfl

section
variable (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)

include res cap in
theorem q8_point (a : W 8) :
    q8 f g a * H8 f g a = -7 + 8 * rind (clsA f g) a + 12 * rind (clsB f g) a +
      4 * rind (clsC f g) a := by
  unfold q8 β8
  rw [← phase_bt _ (odd8 f g res a)]
  unfold H8 Balanced242Reduction.ind clsA clsB clsC
  rcases hi_values f g res cap a with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

include res cap in
theorem phase_identity :
    total 8 (fun x => U f g x * transform (q8 f g) x) =
      32 * (2 * agreements f g - 232 - (cnt (clsA f g) + cnt (clsC f g))) := by
  rw [← Balanced242Section0320.duality]
  have e (a : W 8) : q8 f g a * transform (U f g) a = 2 * (q8 f g a * H8 f g a) := by
    rw [spec8 f g res a, Int.mul_left_comm]
  simp only [e, q8_point f g res cap, total_scale, total_add, total_const]
  have pm := profile_mass f g res cap
  unfold cnt at pm ⊢
  have : many 8 = 256 := by decide
  rw [this]
  omega

theorem sign_vals (b : Bool) : sign b = 1 ∨ sign b = -1 := by cases b <;> decide

include res in
theorem phase_div (M : Int) (hM : 0 < M) (hMM : M * M = many 8 * rr (β8 f g)) :
    ∃ K : Int, total 8 (fun x => U f g x * transform (q8 f g) x) = M * K ∧
      K.natAbs ≤ cntGood f g ∧ K.natAbs ≤ 256 - agreements f g := by
  let σ : W 8 → Int := fun x =>
    if transform (q8 f g) x = M then 1 else if transform (q8 f g) x = -M then -1 else 0
  let k : W 8 → Int := fun x => U f g x * σ x
  have vals (x : W 8) : (good (β8 f g) x = true →
      transform (q8 f g) x = M ∨ transform (q8 f g) x = -M) ∧
      (good (β8 f g) x = false → transform (q8 f g) x = 0) :=
    Balanced242Rank.spec_values (β8 f g) (cube8 f g res) M hMM x
  have pt (x : W 8) : U f g x * transform (q8 f g) x = M * k x := by
    have hu := Balanced242SectionFacts.U_bound f g x
    have hU : U f g x = -1 ∨ U f g x = 0 ∨ U f g x = 1 := by omega
    have hq : transform (q8 f g) x = 0 ∨ transform (q8 f g) x = M ∨ transform (q8 f g) x = -M := by
      cases hg : good (β8 f g) x
      · exact Or.inl ((vals x).2 hg)
      · rcases (vals x).1 hg with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    show _ = M * (U f g x * σ x)
    simp only [σ]
    rcases hq with h | h | h <;> rw [h]
    · rw [if_neg (by omega), if_neg (by omega)]; simp
    · rw [if_pos rfl]; rcases hU with u | u | u <;> rw [u] <;> omega
    · rw [if_neg (by omega), if_pos rfl]; rcases hU with u | u | u <;> rw [u] <;> omega
  have bnd1 (x : W 8) : k x ≤ bind (good (β8 f g) x) ∧ -k x ≤ bind (good (β8 f g) x) := by
    have hu := Balanced242SectionFacts.U_bound f g x
    show U f g x * σ x ≤ _ ∧ -(U f g x * σ x) ≤ _
    simp only [σ]
    cases hg : good (β8 f g) x
    · rw [(vals x).2 hg, if_neg (by omega), if_neg (by omega)]
      simp [Balanced242Plateau.ind]
    · simp only [Balanced242Plateau.ind, if_true]
      have hU : U f g x = -1 ∨ U f g x = 0 ∨ U f g x = 1 := by omega
      rcases (vals x).1 hg with h | h <;> rw [h]
      · rw [if_pos rfl]; rcases hU with u | u | u <;> rw [u] <;> decide
      · rw [if_neg (by omega), if_pos rfl]; rcases hU with u | u | u <;> rw [u] <;> decide
  have bnd2 (x : W 8) : k x ≤ 1 - (sameBit false (f x) (g x) + sameBit true (f x) (g x)) ∧
      -k x ≤ 1 - (sameBit false (f x) (g x) + sameBit true (f x) (g x)) := by
    show U f g x * σ x ≤ _ ∧ -(U f g x * σ x) ≤ _
    have hs : σ x = -1 ∨ σ x = 0 ∨ σ x = 1 := by
      simp only [σ]; split
      · exact Or.inr (Or.inr rfl)
      · split
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
    unfold U sameBit
    cases f x <;> cases g x <;> rcases hs with s | s | s <;> rw [s] <;> decide
  refine ⟨total 8 k, ?_, ?_, ?_⟩
  · rw [← total_scale]; apply congrArg (total 8); funext x; exact pt x
  · have a1 := total_mono 8 _ _ (fun x => (bnd1 x).1)
    have a2 := total_mono 8 (fun x => -k x) _ (fun x => (bnd1 x).2)
    have neg : total 8 (fun x => -k x) = -total 8 k := by
      have := total_scale 8 (-1) k
      simp only [Int.neg_mul, Int.one_mul] at this; exact this
    rw [neg] at a2
    change total 8 k ≤ cntGood f g at a1
    change -total 8 k ≤ cntGood f g at a2
    omega
  · have a1 := total_mono 8 _ _ (fun x => (bnd2 x).1)
    have a2 := total_mono 8 (fun x => -k x) _ (fun x => (bnd2 x).2)
    have neg : total 8 (fun x => -k x) = -total 8 k := by
      have := total_scale 8 (-1) k
      simp only [Int.neg_mul, Int.one_mul] at this; exact this
    rw [neg] at a2
    simp only [total_sub, total_add, total_const] at a1 a2
    unfold agreements countPair
    have : many 8 = 256 := by decide
    rw [this] at a1 a2
    omega

include res in
theorem Z_identity (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0) :
    2 * Zc f g - 256 = q8 f g (zero 8) * transform (q8 f g) (supportXor g) := by
  have pt (a : W 8) : 2 * (if lo f g a % 16 = 0 then 1 else 0) - 1 =
      q8 f g (zero 8) * (q8 f g a * chr (supportXor g) a) := by
    have hc := Balanced242HighSections.coupled_phase f g a
    rw [dc] at hc
    have r1 := res a; have r0 := res (zero 8); have l1 := lores a
    unfold q8 β8 Balanced242Plateau.bt H8 chr
    rw [dot_comm 8 (supportXor g) a]
    cases hd : dot 8 a (supportXor g) <;> simp only [hd, if_true, Bool.false_eq_true, if_false] at hc <;>
    by_cases h1 : hi f g a / 4 / 2 % 2 = 1 <;> by_cases h0 : hi f g (zero 8) / 4 / 2 % 2 = 1 <;>
      by_cases hl : lo f g a % 16 = 0 <;>
      simp only [h1, h0, hl, decide_true, decide_false, sign, if_true, if_false,
        Bool.false_eq_true] <;> omega
  have e := congrArg (total 8) (funext pt)
  simp only [total_sub, total_scale, total_const] at e
  unfold Zc
  have : many 8 = 256 := by decide
  rw [this] at e
  unfold transform
  omega

theorem Z_pos (dc : lo f g (zero 8) = 0) : 1 ≤ Zc f g := by
  have := point_le_total 8 (fun a => if lo f g a % 16 = 0 then (1 : Int) else 0)
    (fun a => by show 0 ≤ (if lo f g a % 16 = 0 then (1 : Int) else 0); split <;> decide) (zero 8)
  simp only [dc] at this
  exact this

end


section
variable (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)

theorem all_good (h : cntGood f g = 256) (y : W 8) : good (β8 f g) y = true := by
  cases hp : good (β8 f g) y
  · exfalso
    have pt := point_le_total 8 (fun v => 1 - bind (good (β8 f g) v))
      (fun v => by
        show 0 ≤ 1 - bind (good (β8 f g) v)
        unfold Balanced242Plateau.ind; split <;> decide) y
    simp only [hp, Balanced242Plateau.ind, Bool.false_eq_true, if_false] at pt
    rw [total_sub, total_const] at pt
    change 1 - 0 ≤ many 8 * 1 - cntGood f g at pt
    rw [h] at pt
    have : many 8 = 256 := by decide
    omega
  · rfl

theorem pow_eq (r : Nat) (c : Nat) (hc : c ≤ 256) (h : (2 : Int) ^ r = (c : Int)) : r < 9 ∧ 2 ^ r = c := by
  have h' : 2 ^ r = c := by exact_mod_cast h
  refine ⟨?_, h'⟩
  false_or_by_contra
  have : 2 ^ 9 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem log_of (r : Nat) (hr : r < 9) :
    (2 ^ r = 256 → r = 8) ∧ (2 ^ r = 64 → r = 6) ∧ (2 ^ r = 16 → r = 4) ∧
    (2 ^ r = 4 → r = 2) ∧ (2 ^ r = 1 → r = 0) := by
  revert r; decide

include res cap in
/-- The global rank condition. The covering-radius input `Zc f g ≠ 64` is only needed above
t = 103: below that the witness 128 always passes the budget at rank 2. -/
theorem rank_cond (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (t : Nat) (hZ64 : Zc f g ≠ 64 ∨ t ≤ 103)
    (ht : agreements f g = t) :
    ∀ r : Nat, cntGood f g = 2 ^ r → r ∈ ranks t (pa f g + pc f g) := by
  intro r hr
  have bud : 1024 * agreements f g + 320 * Zc f g + 256 ≤ 147456 :=
    low_support_budget f g dc lores locap
  have zp := Z_pos f g dc
  have zid := Z_identity f g res dc lores
  have pid := phase_identity f g res cap
  have cA := Balanced242Reduction.cnt_nonneg (clsA f g)
  have cC := Balanced242Reduction.cnt_nonneg (clsC f g)
  have hq0 : q8 f g (zero 8) = 1 ∨ q8 f g (zero 8) = -1 := sign_vals _
  -- generic finisher for one rank value, given a witness Z for the support test
  have finish : ∀ (r0 : Nat) (M : Nat) (rr0 c0 : Int), r = r0 →
      (r0 = 0 ∨ r0 = 2 ∨ r0 = 4 ∨ r0 = 6 ∨ r0 = 8) →
      256 >>> (r0 / 2) = M → rr (β8 f g) = rr0 → cntGood f g = c0 → (M : Int) * M = 256 * rr0 →
      c0 = 2 ^ r0 → 0 < M → ∀ Z : Nat,
      Z ∈ [128 - M / 2, 128 + M / 2] ++ (if r0 < 8 then [128] else []) → 0 < Z → Z ≠ 64 →
      1024 * (t : Int) + 320 * (Z : Int) + 256 ≤ 147456 →
      r ∈ ranks t (pa f g + pc f g) := by
    intro r0 M rr0 c0 hr0 hr0v hM hrr hc0 hMM hc2 hMpos Z hZm hZ0 hZn hZb
    subst hr0
    obtain ⟨K, hK, hK1, hK2⟩ := phase_div f g res (M : Int) (by omega)
      (by rw [hrr, show many 8 = 256 from rfl]; exact hMM)
    unfold ranks
    rw [List.mem_filter]
    refine ⟨by rcases hr0v with h | h | h | h | h <;> subst h <;> decide, ?_⟩
    apply rankOK_of t (pa f g + pc f g) r Z K
    · rw [hM]; exact hZm
    · exact hZ0
    · exact hZn
    · omega
    · rw [hM]; exact hMpos
    · rw [hM]
      unfold pa pc
      rw [pid] at hK; rw [ht] at hK
      have e1 : (((cnt (clsA f g)).toNat + (cnt (clsC f g)).toNat : Nat) : Int) =
          cnt (clsA f g) + cnt (clsC f g) := by omega
      rw [e1]; omega
    · rw [hc0, hc2] at hK1
      have : ((2 ^ r : Nat) : Int) = (2 : Int) ^ r := by exact_mod_cast rfl
      omega
  -- the Z values: 2Z - 256 is 0 or +-M, and nonzero when every frequency is good
  have zvals : ∀ (M : Int), M * M = many 8 * rr (β8 f g) →
      (2 * Zc f g - 256 = 0 ∧ good (β8 f g) (supportXor g) = false) ∨
      2 * Zc f g - 256 = M ∨ 2 * Zc f g - 256 = -M := by
    intro M hMM
    have v := Balanced242Rank.spec_values (β8 f g) (cube8 f g res) M hMM (supportXor g)
    change (good (β8 f g) (supportXor g) = true →
      transform (q8 f g) (supportXor g) = M ∨ transform (q8 f g) (supportXor g) = -M) ∧
      (good (β8 f g) (supportXor g) = false → transform (q8 f g) (supportXor g) = 0) at v
    rw [zid]
    cases hg : good (β8 f g) (supportXor g)
    · left; rw [v.2 hg, Int.mul_zero]; exact ⟨rfl, rfl⟩
    · rcases v.1 hg with h | h <;> rw [h] <;> rcases hq0 with q | q <;> rw [q] <;> simp
  rcases global_levels f g res with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have ⟨hr9, hp⟩ := pow_eq r 256 (by decide) (by rw [← hr, h2]; rfl)
    have fin := finish 8 16 1 256 ((log_of r hr9).1 hp) (by decide) rfl h1 h2 (by decide)
      (by decide) (by decide)
    rcases zvals 16 (by rw [h1]; decide) with ⟨-, hg⟩ | h | h
    · rw [all_good f g h2] at hg; exact absurd hg (by decide)
    · exact fin 136 (by decide) (by decide) (by decide) (by omega)
    · exact fin 120 (by decide) (by decide) (by decide) (by omega)
  · have ⟨hr9, hp⟩ := pow_eq r 64 (by decide) (by rw [← hr, h2]; rfl)
    have fin := finish 6 32 4 64 ((log_of r hr9).2.1 hp) (by decide) rfl h1 h2 (by decide)
      (by decide) (by decide)
    rcases zvals 32 (by rw [h1]; decide) with ⟨h, -⟩ | h | h
    · exact fin 128 (by decide) (by decide) (by decide) (by omega)
    · exact fin 144 (by decide) (by decide) (by decide) (by omega)
    · exact fin 112 (by decide) (by decide) (by decide) (by omega)
  · have ⟨hr9, hp⟩ := pow_eq r 16 (by decide) (by rw [← hr, h2]; rfl)
    have fin := finish 4 64 16 16 ((log_of r hr9).2.2.1 hp) (by decide) rfl h1 h2 (by decide)
      (by decide) (by decide)
    rcases zvals 64 (by rw [h1]; decide) with ⟨h, -⟩ | h | h
    · exact fin 128 (by decide) (by decide) (by decide) (by omega)
    · exact fin 160 (by decide) (by decide) (by decide) (by omega)
    · exact fin 96 (by decide) (by decide) (by decide) (by omega)
  · have ⟨hr9, hp⟩ := pow_eq r 4 (by decide) (by rw [← hr, h2]; rfl)
    have fin := finish 2 128 64 4 ((log_of r hr9).2.2.2.1 hp) (by decide) rfl h1 h2 (by decide)
      (by decide) (by decide)
    rcases zvals 128 (by rw [h1]; decide) with ⟨h, -⟩ | h | h
    · exact fin 128 (by decide) (by decide) (by decide) (by omega)
    · exact fin 192 (by decide) (by decide) (by decide) (by omega)
    · -- Z = 64: excluded by the covering radius, or replaced by the witness 128 when t ≤ 103
      rcases hZ64 with hz | hz
      · exact absurd (by omega) hz
      · exact fin 128 (by decide) (by decide) (by decide) (by omega)
  · have ⟨hr9, hp⟩ := pow_eq r 1 (by decide) (by rw [← hr, h2]; rfl)
    have fin := finish 0 256 256 1 ((log_of r hr9).2.2.2.2 hp) (by decide) rfl h1 h2 (by decide)
      (by decide) (by decide)
    rcases zvals 256 (by rw [h1]; decide) with ⟨h, -⟩ | h | h
    · exact fin 128 (by decide) (by decide) (by decide) (by omega)
    · exact fin 256 (by decide) (by decide) (by decide) (by omega)
    · exfalso; omega

end

end Balanced242RankCond

#print axioms Balanced242RankCond.rankOK_of
#print axioms Balanced242RankCond.phase_identity
#print axioms Balanced242RankCond.phase_div
#print axioms Balanced242RankCond.Z_identity
#print axioms Balanced242RankCond.Z_pos
#print axioms Balanced242RankCond.rank_cond
