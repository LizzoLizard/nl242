/-
  Balanced242LowBlock.lean — Complete unconditional Lean 4 formalization of the universal
  low-block defect identity, autocorrelation congruence mod 32, and upper-window (`t = 100..118`)
  budget & spectral exclusions from `middle/MIDDLE_PROOF.md` and `PROOF_t100..118_CLOSED.md`.

  Zero Mathlib, zero `sorry`, zero `native_decide`, zero `SectionEnum`.
  The budget, rank classification and `no_t106_rank8` use `[propext, Quot.sound]`.
  The corollaries `t_ge_114_forces_Z64`, `t112_forces_rank4_or_Z64` and
  `t108_rank6_D_eq_rad` also use `Classical.choice`.

  Main exported theorems:
    1. `low_defect_pointwise`: `(lo f g a / 2)^2 = 144 - 80 * ind (Zset f g a) - 64 * Dlo f g a`.
    2. `low_defect_budget`: `4 * (n0 f g + 2 * n8 f g) = 2304 - 5 * Zc f g - 16 * agreements f g`
       and `1 ≤ n0 f g`, `0 ≤ n8 f g`.
    3. `low_autocorr_mod32`: `(5 * transform (ind Zset) u + 4 * transform Dlo u) % 32 = 0` for all `u : W 8`.
    4. Exact budget exclusions across `t = 94..118`:
       * `no_Zc_256_of_t_ge_64`, `no_Zc_160_of_t_ge_94`, `no_Zc_144_of_t_ge_100`,
       * `no_Zc_136_of_t_ge_102`, `no_Zc_128_of_t_ge_104`, `no_Zc_120_of_t_ge_108`,
       * `no_Zc_112_of_t_ge_110`, `no_Zc_96_of_t_ge_114`.
    5. `rank_Zc_values`: for any balanced NL-242 halves `(f, g)`, the rank `r ∈ {0, 2, 4, 6, 8}`
       forces the exact allowed `Zc` set (`{128, 256}`, `{64, 128, 192}`, `{96, 128, 160}`,
       `{112, 128, 144}`, `{120, 136}`).
    6. `t_ge_114_forces_Z64`: any balanced NL-242 halves with `114 ≤ agreements f g` MUST have
       `Zc f g = 64` (rank 2).
    7. `t112_forces_rank4_Z96_or_Z64`: at `t = 112`, `Zc f g = 96` (rank 4) or `Zc f g = 64` (rank 2).
    8. `no_t106_rank8`: unconditional exclusion of rank 8 at `t = 106` via `low_autocorr_mod32`!
    9. `t108_rank6_D_is_4zeros`: at `t = 108` rank 6 (`Zc = 112`), `n8 = 0`, `n0 = 4`,
       and `transform Dlo u = 4` on `perp (β8 f g)` and `0` elsewhere (so `supp(Dlo) = rad (β8 f g)`!).
-/
import Balanced242QuarticHighBlock

namespace Balanced242LowBlock

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Hyperplane Balanced242Reduction
open Balanced242Plateau Balanced242Rank Balanced242Global Balanced242RankCond
open Balanced242SectionFacts Balanced242QuarticHighBlock

local notation "bind" => Balanced242Plateau.ind

/-- Low residue set `Z = {a : 16 ∣ lo f g a}`. -/
def Zset (f g : Half) (a : W 8) : Bool := decide (lo f g a % 16 = 0)

/-- Low defect weight `D_lo(a) = 1` if `lo(a) = 0`, `2` if `|lo(a)| = 8`, else `0`. -/
def Dlo (f g : Half) (a : W 8) : Int :=
  if lo f g a = 0 then 1 else if (lo f g a).natAbs = 8 then 2 else 0

/-- Count `n0 = #{a : lo f g a = 0}`. -/
def n0 (f g : Half) : Int := total 8 (fun a => if lo f g a = 0 then (1 : Int) else 0)

/-- Count `n8 = #{a : |lo f g a| = 8}`. -/
def n8 (f g : Half) : Int := total 8 (fun a => if (lo f g a).natAbs = 8 then (1 : Int) else 0)

/-- Signed agreement indicator `V(x) = if f x = g x then sign (f x) else 0`. -/
def Vtbl (f g : Half) (x : W 8) : Int := if f x = g x then sign (f x) else 0

theorem lo_vals (f g : Half) (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24) (a : W 8) :
    lo f g a = -24 ∨ lo f g a = -16 ∨ lo f g a = -8 ∨ lo f g a = 0 ∨
    lo f g a = 8 ∨ lo f g a = 16 ∨ lo f g a = 24 := by
  have h1 := lores a; have h2 := locap a; omega

theorem lo_eq_2_transform_V (f g : Half) (a : W 8) :
    lo f g a = 2 * transform (Vtbl f g) a := by
  rw [lo_transform]
  unfold transform
  rw [← total_scale]
  apply congrArg (total 8); funext x
  unfold pairSign Vtbl
  cases f x <;> cases g x <;> simp [sign]

theorem Zc_eq_total_Zset (f g : Half) :
    Zc f g = total 8 (fun a => bind (Zset f g a)) := by
  unfold Zc Zset Balanced242Plateau.ind
  apply congrArg (total 8); funext a
  by_cases h : lo f g a % 16 = 0 <;> simp [h]

theorem total_Dlo_eq (f g : Half) :
    total 8 (Dlo f g) = n0 f g + 2 * n8 f g := by
  unfold n0 n8 Dlo
  rw [← total_scale, ← total_add]
  apply congrArg (total 8); funext a
  by_cases h0 : lo f g a = 0
  · rw [h0]; decide
  · by_cases h8 : (lo f g a).natAbs = 8
    · simp [h0, h8]
    · simp [h0, h8]

/-- **Theorem 1 (`low_defect_pointwise`)**:
    `(lo f g a / 2)^2 = 144 - 80 * 1_Z(a) - 64 * D_lo(a)` at every frequency `a : W 8`. -/
theorem low_defect_pointwise (f g : Half) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (a : W 8) :
    (lo f g a / 2) * (lo f g a / 2) = 144 - 80 * bind (Zset f g a) - 64 * Dlo f g a := by
  unfold Zset Dlo Balanced242Plateau.ind
  rcases lo_vals f g lores locap a with h | h | h | h | h | h | h <;> rw [h] <;> decide

/-- **Theorem 2 (`low_defect_budget`)**: Universal low-block defect budget
    `4 * (n0 + 2 * n8) = 2304 - 5 * Zc - 16 * t`, with `1 ≤ n0` and `0 ≤ n8`. -/
theorem low_defect_budget (f g : Half) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24) :
    4 * (n0 f g + 2 * n8 f g) = 2304 - 5 * Zc f g - 16 * agreements f g ∧
    1 ≤ n0 f g ∧ 0 ≤ n8 f g := by
  have hpar := Balanced242Section0320.parseval (Vtbl f g)
  have hV2 : total 8 (fun x => Vtbl f g x * Vtbl f g x) = agreements f g := by
    unfold agreements countPair Vtbl
    rw [← total_add]
    apply congrArg (total 8); funext x
    cases f x <;> cases g x <;> decide
  have htrV (a : W 8) : transform (Vtbl f g) a = lo f g a / 2 := by
    have h := lo_eq_2_transform_V f g a; omega
  have hsum : total 8 (fun a => (lo f g a / 2) * (lo f g a / 2)) = 256 * agreements f g := by
    have hm : many 8 = 256 := by decide
    rw [hV2, hm] at hpar
    have hfun : (fun a => transform (Vtbl f g) a * transform (Vtbl f g) a) =
        fun a => (lo f g a / 2) * (lo f g a / 2) := funext (fun a => by rw [htrV a])
    rw [← hfun]; exact hpar
  have hpt_sum := congrArg (total 8) (funext (low_defect_pointwise f g lores locap))
  rw [hsum, total_sub, total_sub, total_const, total_scale, total_scale,
      ← Zc_eq_total_Zset, total_Dlo_eq] at hpt_sum
  have hm : many 8 = 256 := by decide
  rw [hm] at hpt_sum
  have hn0 : 1 ≤ n0 f g := by
    have h := point_le_total 8 (fun a => if lo f g a = 0 then (1 : Int) else 0)
      (fun a => by dsimp only; split <;> omega) (zero 8)
    simp only [dc, if_true] at h; exact h
  have hn8 : 0 ≤ n8 f g := total_nonneg _ (fun a => by split <;> omega)
  exact ⟨by omega, hn0, hn8⟩

/-! ## Universal Low Autocorrelation Congruence mod 32 -/

private theorem exists_dot_true8 (u : W 8) (hu : u ≠ zero 8) : ∃ w : W 8, dot 8 w u = true := by
  have aux : ∀ {n : Nat} (r : W n), r ≠ zero n → ∃ w : W n, dot n w r = true := by
    intro n; induction n with
    | zero => intro r hr; exact absurd rfl hr
    | succ m ih =>
      intro r hr; rcases r with ⟨rb, r'⟩
      cases rb
      · have hr' : r' ≠ zero m := fun h => hr (by rw [h]; rfl)
        obtain ⟨w', hw'⟩ := ih r' hr'
        exact ⟨(false, w'), by simp [dot, hw']⟩
      · exact ⟨(true, zero m), by simp [dot, dot_zero]⟩
  exact aux u hu

private theorem total_pair8 (w u : W 8) (hwu : dot 8 w u = true) (F : W 8 → Int) :
    total 8 F = total 7 (fun y => F (secPt 7 w false y) + F (add 8 (secPt 7 w false y) u)) := by
  have hw : w ≠ zero 8 := by intro hz; rw [hz, dot_zero] at hwu; exact Bool.noConfusion hwu
  have h1 := Balanced242Quartic.sec_sum 7 w hw F
  let G : W 8 → Int := fun z => if dot 8 w z then F z else 0
  have hG1 : total 8 G = total 7 (fun y => F (secPt 7 w true y)) := by
    rw [Balanced242Quartic.sec_sum 7 w hw G]
    have h0 : total 7 (fun y => G (secPt 7 w false y)) = 0 := by
      rw [← total_zero 7]; apply congrArg (total 7); funext y
      dsimp only [G]; rw [Balanced242Quartic.secPt_dot 7 w hw false y]; rfl
    have h1' : total 7 (fun y => G (secPt 7 w true y)) = total 7 (fun y => F (secPt 7 w true y)) := by
      apply congrArg (total 7); funext y
      dsimp only [G]; rw [Balanced242Quartic.secPt_dot 7 w hw true y]; rfl
    rw [h0, h1', Int.zero_add]
  have hG2 : total 8 G = total 7 (fun y => F (add 8 (secPt 7 w false y) u)) := by
    have hsh : total 8 G = total 8 (fun z => G (add 8 z u)) := by
      rw [← sum_shift 8 u G]; apply congrArg (total 8); funext z; rw [add_comm]
    rw [hsh, Balanced242Quartic.sec_sum 7 w hw (fun z => G (add 8 z u))]
    have h0 : total 7 (fun y => G (add 8 (secPt 7 w false y) u)) =
        total 7 (fun y => F (add 8 (secPt 7 w false y) u)) := by
      apply congrArg (total 7); funext y
      dsimp only [G]; rw [dot_right, Balanced242Quartic.secPt_dot 7 w hw false y, hwu]; rfl
    have h1' : total 7 (fun y => G (add 8 (secPt 7 w true y) u)) = 0 := by
      rw [← total_zero 7]; apply congrArg (total 7); funext y
      dsimp only [G]; rw [dot_right, Balanced242Quartic.secPt_dot 7 w hw true y, hwu]; rfl
    rw [h0, h1', Int.add_zero]
  rw [h1, ← hG1, hG2, ← total_add]

/-- Every autocorrelation `∑_x V(x) V(x ⊕ u)` is EVEN (for `u = 0` by `agreements % 2 = 0`,
    and for `u ≠ 0` by pairing `{x, x ⊕ u}`). -/
theorem autocorr_V_even (f g : Half) (ht_even : agreements f g % 2 = 0) (u : W 8) :
    total 8 (fun x => Vtbl f g x * Vtbl f g (add 8 x u)) % 2 = 0 := by
  by_cases hu : u = zero 8
  · subst hu
    have hpt (x : W 8) : Vtbl f g x * Vtbl f g (add 8 x (zero 8)) =
        if f x = g x then (1 : Int) else 0 := by
      rw [add_zero_right]; unfold Vtbl; cases f x <;> cases g x <;> decide
    rw [funext hpt]
    have hag : total 8 (fun x => if f x = g x then (1 : Int) else 0) = agreements f g := by
      unfold agreements countPair; rw [← total_add]
      apply congrArg (total 8); funext x; cases f x <;> cases g x <;> decide
    rw [hag]; exact ht_even
  · obtain ⟨w, hwu⟩ := exists_dot_true8 u hu
    rw [total_pair8 w u hwu]
    have hpt (y : W 7) :
        Vtbl f g (secPt 7 w false y) * Vtbl f g (add 8 (secPt 7 w false y) u) +
        Vtbl f g (add 8 (secPt 7 w false y) u) * Vtbl f g (add 8 (add 8 (secPt 7 w false y) u) u) =
        2 * (Vtbl f g (secPt 7 w false y) * Vtbl f g (add 8 (secPt 7 w false y) u)) := by
      rw [Balanced242Plateau.add_assoc', add_self, add_zero_right, Int.mul_comm (Vtbl f g (add 8 (secPt 7 w false y) u))]
      omega
    rw [funext hpt, total_scale]; omega

/-- Wiener–Khinchin identity: `transform (fun a => (transform V a)^2) u = many n * ∑_x V x * V (x ⊕ u)`. -/
theorem transform_sq_eq_autocorr {n : Nat} (V : W n → Int) (u : W n) :
    transform (fun a => transform V a * transform V a) u =
      many n * total n (fun x => V x * V (add n x u)) := by
  have h1 : transform (fun a => transform V a * transform V a) u =
      total n (fun a => transform V a * transform (fun x => V (add n x u)) a) := by
    unfold transform
    apply congrArg (total n); funext a
    have hsh : total n (fun x => V (add n x u) * chr a x) =
        chr a u * total n (fun y => V y * chr a y) := by
      have hs := sum_shift n u (fun y => V y * chr a y)
      have hre (y : W n) : V (add n u y) * chr a (add n u y) =
          chr a u * (V (add n y u) * chr a y) := by
        rw [add_comm n u y, Balanced242Plateau.chr_add]; ac_rfl
      rw [funext hre, total_scale] at hs
      have hmul := congrArg (fun z => chr a u * z) hs
      dsimp only at hmul
      rw [← Int.mul_assoc, show chr a u * chr a u = 1 from sign_sq _, Int.one_mul] at hmul
      exact hmul
    rw [hsh]
    have hcu : chr u a = chr a u := by unfold chr; rw [dot_comm]
    rw [hcu]; dsimp only; ac_rfl
  rw [h1, parseval2]

/-- **Theorem 3 (`low_autocorr_mod32`)**: Universal low autocorrelation congruence
    `(5 * transform (1_Z) u + 4 * transform (D_lo) u) % 32 = 0` for EVERY `u : W 8`! -/
theorem low_autocorr_mod32 (f g : Half) (ht_even : agreements f g % 2 = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24) (u : W 8) :
    (5 * transform (fun a => bind (Zset f g a)) u + 4 * transform (Dlo f g) u) % 32 = 0 := by
  have hwk := transform_sq_eq_autocorr (Vtbl f g) u
  have hm8 : many 8 = 256 := by decide
  rw [hm8] at hwk
  have htrV (a : W 8) : transform (Vtbl f g) a = lo f g a / 2 := by
    have h := lo_eq_2_transform_V f g a; omega
  have hsq_fn : (fun a => transform (Vtbl f g) a * transform (Vtbl f g) a) =
      fun a => 144 - 80 * bind (Zset f g a) - 64 * Dlo f g a := by
    funext a; rw [htrV a]; exact low_defect_pointwise f g lores locap a
  rw [hsq_fn] at hwk
  -- Expand `transform (144 - 80*Z - 64*D) u`:
  have hexp : transform (fun a => 144 - 80 * bind (Zset f g a) - 64 * Dlo f g a) u =
      144 * transform (fun _ => (1 : Int)) u -
      80 * transform (fun a => bind (Zset f g a)) u -
      64 * transform (Dlo f g) u := by
    unfold transform
    have hpt (a : W 8) : (144 - 80 * bind (Zset f g a) - 64 * Dlo f g a) * chr u a =
        144 * ((1 : Int) * chr u a) - 80 * (bind (Zset f g a) * chr u a) - 64 * (Dlo f g a * chr u a) := by
      rw [Int.sub_mul, Int.sub_mul, Int.mul_assoc, Int.mul_assoc, Int.one_mul]
    rw [funext hpt, total_sub, total_sub, total_scale, total_scale, total_scale, total_scale]
  rw [hexp] at hwk
  have htr1 : transform (fun _ => (1 : Int)) u = 256 * hits (zero 8) u := by
    unfold transform
    have hpt (a : W 8) : (1 : Int) * chr u a = chr u a := Int.one_mul _
    rw [funext hpt]
    have h := identity_spectrum 8 u
    change total 8 (chr u) = _ at h
    rw [h, hm8]
    unfold hits
    by_cases hz : u = zero 8
    · subst hz; simp
    · have hz' : ¬ zero 8 = u := fun e => hz e.symm; simp [hz, hz']
  rw [htr1] at hwk
  have hev := autocorr_V_even f g ht_even u
  omega

/-! ## Universal Upper-Window (`t = 94..118`) Budget Exclusions & Rank-Zc Classification -/

theorem no_Zc_256_of_t_ge_64 (f g : Half) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (hZ : Zc f g = 256) (ht : 64 ≤ agreements f g) : False := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap; omega

theorem no_Zc_160_of_t_ge_94 (f g : Half) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (hZ : Zc f g = 160) (ht : 94 ≤ agreements f g) : False := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap; omega

theorem no_Zc_144_of_t_ge_100 (f g : Half) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (hZ : Zc f g = 144) (ht : 100 ≤ agreements f g) : False := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap; omega

theorem no_Zc_136_of_t_ge_102 (f g : Half) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (hZ : Zc f g = 136) (ht : 102 ≤ agreements f g) : False := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap; omega

theorem no_Zc_128_of_t_ge_104 (f g : Half) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (hZ : Zc f g = 128) (ht : 104 ≤ agreements f g) : False := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap; omega

theorem no_Zc_120_of_t_ge_108 (f g : Half) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (hZ : Zc f g = 120) (ht : 108 ≤ agreements f g) : False := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap; omega

theorem no_Zc_112_of_t_ge_110 (f g : Half) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (hZ : Zc f g = 112) (ht : 110 ≤ agreements f g) : False := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap; omega

theorem no_Zc_96_of_t_ge_114 (f g : Half) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (hZ : Zc f g = 96) (ht : 114 ≤ agreements f g) : False := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap; omega

/-- **Theorem 4 (`rank_Zc_values`)**: Exact classification of `(rr (β8 f g), Zc f g)` across
    all 5 quadratic phase ranks `r ∈ {0, 2, 4, 6, 8}` using `Z_identity` and `spec_values`. -/
theorem rank_Zc_values (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0) :
    (rr (β8 f g) = 256 ∧ (Zc f g = 128 ∨ Zc f g = 256)) ∨
    (rr (β8 f g) = 64 ∧ (Zc f g = 64 ∨ Zc f g = 128 ∨ Zc f g = 192)) ∨
    (rr (β8 f g) = 16 ∧ (Zc f g = 96 ∨ Zc f g = 128 ∨ Zc f g = 160)) ∨
    (rr (β8 f g) = 4 ∧ (Zc f g = 112 ∨ Zc f g = 128 ∨ Zc f g = 144)) ∨
    (rr (β8 f g) = 1 ∧ (Zc f g = 120 ∨ Zc f g = 136)) := by
  have hrc := Balanced242Global.global_levels f g res
  have hzid := Z_identity f g res dc lores
  have hzpos := Z_pos f g dc
  have hq0 : q8 f g (zero 8) = 1 ∨ q8 f g (zero 8) = -1 := sign_vals _
  have hm8 : many 8 = 256 := by decide
  have step (M : Int) (hMM : M * M = many 8 * rr (β8 f g)) :
      2 * Zc f g - 256 = 0 ∨ 2 * Zc f g - 256 = M ∨ 2 * Zc f g - 256 = -M := by
    have hv := Balanced242Rank.spec_values (β8 f g) (cube8 f g res) M hMM (supportXor g)
    have htr : transform (q8 f g) (supportXor g) = 0 ∨
        transform (q8 f g) (supportXor g) = M ∨ transform (q8 f g) (supportXor g) = -M := by
      cases hg : good (β8 f g) (supportXor g)
      · left; exact hv.2 hg
      · right; exact hv.1 hg
    rcases hq0 with h0 | h0 <;> rcases htr with ht | ht | ht <;> rw [h0, ht] at hzid <;> omega
  rcases hrc with ⟨hrr, hcnt⟩ | ⟨hrr, _⟩ | ⟨hrr, _⟩ | ⟨hrr, _⟩ | ⟨hrr, _⟩
  · -- rank 8: rr = 1, M = 16
    have hg : good (β8 f g) (supportXor g) = true := all_good f g hcnt (supportXor g)
    have hsq := spec_good (β8 f g) (cube8 f g res) (supportXor g)
    rw [hrr, hg, hm8] at hsq
    change transform (q8 f g) (supportXor g) * transform (q8 f g) (supportXor g) = 256 * (1 * 1) at hsq
    have htr : transform (q8 f g) (supportXor g) = 16 ∨ transform (q8 f g) (supportXor g) = -16 :=
      sq_cases _ 16 (by omega)
    right; right; right; right
    rcases hq0 with h0 | h0 <;> rcases htr with ht | ht <;> rw [h0, ht] at hzid <;> exact ⟨hrr, by omega⟩
  · -- rank 6: rr = 4, M = 32
    have hs := step 32 (by rw [hrr, hm8]; decide)
    right; right; right; left; exact ⟨hrr, by omega⟩
  · -- rank 4: rr = 16, M = 64
    have hs := step 64 (by rw [hrr, hm8]; decide)
    right; right; left; exact ⟨hrr, by omega⟩
  · -- rank 2: rr = 64, M = 128
    have hs := step 128 (by rw [hrr, hm8]; decide)
    right; left; exact ⟨hrr, by omega⟩
  · -- rank 0: rr = 256, M = 256
    have hs := step 256 (by rw [hrr, hm8])
    left; exact ⟨hrr, by omega⟩

/-- **Theorem 5 (`t_ge_114_forces_Z64`)**: Any balanced NL-242 halves with `t ≥ 114`
    MUST have `rr = 64` (rank 2) and `Zc = 64`! -/
theorem t_ge_114_forces_Z64 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (ht : 114 ≤ agreements f g) :
    rr (β8 f g) = 64 ∧ Zc f g = 64 := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap
  rcases rank_Zc_values f g res dc lores with
    ⟨hrr, hZ⟩ | ⟨hrr, hZ⟩ | ⟨hrr, hZ⟩ | ⟨hrr, hZ⟩ | ⟨hrr, hZ⟩ <;> omega

/-- **Theorem 6 (`t112_forces_rank4_or_Z64`)**: At `t = 112`, ONLY rank 4 (`Zc = 96`)
    or rank 2 (`Zc = 64`) can survive the low-block budget! -/
theorem t112_forces_rank4_or_Z64 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (ht : agreements f g = 112) :
    (rr (β8 f g) = 16 ∧ Zc f g = 96) ∨ (rr (β8 f g) = 64 ∧ Zc f g = 64) := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap
  rcases rank_Zc_values f g res dc lores with
    ⟨hrr, hZ⟩ | ⟨hrr, hZ⟩ | ⟨hrr, hZ⟩ | ⟨hrr, hZ⟩ | ⟨hrr, hZ⟩ <;> omega

/-- **Theorem 7 (`transform_Zset_eq`)**: Exact Walsh transform of `1_Z` at EVERY direction `u`:
    `2 * transform (1_Z) u - 256 * hits 0 u = q8(0) * transform q8 (u ⊕ supportXor g)`. -/
theorem transform_Zset_eq (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0) (u : W 8) :
    2 * transform (fun a => bind (Zset f g a)) u - 256 * hits (zero 8) u =
      q8 f g (zero 8) * transform (q8 f g) (add 8 u (supportXor g)) := by
  have pt (a : W 8) : (2 * bind (Zset f g a) - 1) * chr u a =
      q8 f g (zero 8) * (q8 f g a * chr (add 8 u (supportXor g)) a) := by
    have hc := Balanced242HighSections.coupled_phase f g a
    rw [dc] at hc
    have r1 := res a; have r0 := res (zero 8); have l1 := lores a
    have hmul : 2 * bind (Zset f g a) - 1 = q8 f g (zero 8) * (q8 f g a * chr (supportXor g) a) := by
      unfold q8 β8 Balanced242Plateau.bt H8 chr Zset Balanced242Plateau.ind
      rw [dot_comm 8 (supportXor g) a]
      cases hd : dot 8 a (supportXor g) <;> simp only [hd, if_true, Bool.false_eq_true, if_false] at hc <;>
      by_cases h1 : hi f g a / 4 / 2 % 2 = 1 <;> by_cases h0 : hi f g (zero 8) / 4 / 2 % 2 = 1 <;>
        by_cases hl : lo f g a % 16 = 0 <;>
        simp only [h1, h0, hl, decide_true, decide_false, sign, if_true, if_false,
          Bool.false_eq_true] <;> omega
    rw [hmul]
    have hchr : chr (add 8 u (supportXor g)) a = chr u a * chr (supportXor g) a := by
      unfold chr; rw [dot_comm 8 (add 8 u (supportXor g)) a, dot_right,
        dot_comm 8 a u, dot_comm 8 a (supportXor g), signMul]
    rw [hchr]; ac_rfl
  have e := congrArg (total 8) (funext pt)
  have hL : total 8 (fun a => (2 * bind (Zset f g a) - 1) * chr u a) =
      2 * transform (fun a => bind (Zset f g a)) u - 256 * hits (zero 8) u := by
    have hsub (a : W 8) : (2 * bind (Zset f g a) - 1) * chr u a =
        2 * (bind (Zset f g a) * chr u a) - chr u a := by rw [Int.sub_mul, Int.mul_assoc, Int.one_mul]
    rw [funext hsub, total_sub, total_scale]
    have hi := identity_spectrum 8 u
    change total 8 (chr u) = _ at hi
    have hm8 : many 8 = 256 := by decide
    rw [hi, hm8]
    have h256 : (if u = zero 8 then (256 : Int) else 0) = 256 * hits (zero 8) u := by
      unfold hits; by_cases hz : u = zero 8
      · subst hz; simp
      · have hz' : ¬ zero 8 = u := fun h => hz h.symm; simp [hz, hz']
    rw [h256]; rfl
  rw [hL, total_scale] at e
  exact e

/-- **Theorem 8 (`no_t106_rank8`)**: Unconditional exclusion of rank 8 at `t = 106`
    via `low_defect_budget` + `low_autocorr_mod32` + `transform_Zset_eq`! -/
theorem no_t106_rank8 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (ht : agreements f g = 106)
    (hrr : rr (β8 f g) = 1) : False := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap
  have hZc : Zc f g = 120 := by
    rcases rank_Zc_values f g res dc lores with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hZ⟩ <;> omega
  -- `4 * (n0 + 2 * n8) = 2304 - 600 - 1696 = 8`, so `n0 + 2 * n8 = 2`, `n0 ≥ 1`.
  -- Actually wait: could `n0 = 2, n8 = 0` OR `n0 = 0` (impossible since `n0 ≥ 1`)!
  -- So `n0 = 2` and `n8 = 0`!
  have hn02 : n0 f g = 2 := by omega
  have hn80 : n8 f g = 0 := by omega
  -- Find the unique nonzero zero `z1 ≠ zero 8` with `lo f g z1 = 0`!
  have h_exists_z1 : ∃ z1 : W 8, z1 ≠ zero 8 ∧ lo f g z1 = 0 := by
    cases hall : (worlds 8).all (fun a => decide (a = zero 8) || decide (lo f g a ≠ 0))
    · obtain ⟨z1, _, hz1⟩ := all_false_exists _ _ hall
      have hne : z1 ≠ zero 8 := by intro hz; subst hz; simp at hz1
      have hlo : lo f g z1 = 0 := by
        by_cases h0 : lo f g z1 = 0
        · exact h0
        · exfalso
          have hd : decide (lo f g z1 ≠ 0) = true := decide_eq_true h0
          rw [hd, Bool.or_true] at hz1; exact Bool.noConfusion hz1
      exact ⟨z1, hne, hlo⟩
    · exfalso
      rw [List.all_eq_true] at hall
      have hle : n0 f g ≤ 1 := by
        have hpt (a : W 8) : (if lo f g a = 0 then (1 : Int) else 0) ≤ hits (zero 8) a := by
          have ha := hall a (all_worlds 8 a)
          by_cases hz : a = zero 8
          · subst hz; unfold hits; simp; split <;> omega
          · have hne : ¬ zero 8 = a := fun h => hz h.symm
            have hdec : decide (a = zero 8) = false := decide_eq_false hz
            rw [hdec, Bool.false_or] at ha
            have hnz : lo f g a ≠ 0 := of_decide_eq_true ha
            unfold hits; simp [hne, hnz]
        have hm := total_mono 8 _ _ hpt; rw [diagonal] at hm; exact hm
      omega
  obtain ⟨z1, hz1_ne, hz1_lo⟩ := h_exists_z1
  -- All other points `a ∉ {0, z1}` have `Dlo f g a = 0`!
  have hD_eq (a : W 8) : Dlo f g a = hits (zero 8) a + hits z1 a := by
    have hge (x : W 8) : hits (zero 8) x + hits z1 x ≤ Dlo f g x := by
      unfold hits Dlo
      by_cases h1 : zero 8 = x
      · subst h1; have hne : ¬ z1 = zero 8 := hz1_ne
        simp [hne, dc]
      · by_cases h2 : z1 = x
        · subst h2; simp [h1, hz1_lo]
        · simp [h1, h2]; split; omega; split <;> omega
    have hdiff_nn (x : W 8) : 0 ≤ Dlo f g x - (hits (zero 8) x + hits z1 x) := by
      have := hge x; omega
    have hdiff_sum : total 8 (fun x => Dlo f g x - (hits (zero 8) x + hits z1 x)) = 0 := by
      rw [total_sub, total_add, total_Dlo_eq, diagonal, diagonal]; omega
    have hpt := point_le_total 8 (fun x => Dlo f g x - (hits (zero 8) x + hits z1 x)) hdiff_nn a
    have h0 := hdiff_nn a
    omega
  -- Pick `u` with `dot 8 u z1 = true` (hence `u ≠ zero 8`)!
  obtain ⟨u, huz1⟩ := exists_dot_true8 z1 hz1_ne
  have hu_ne : u ≠ zero 8 := by intro hz; rw [hz, dot_zero] at huz1; exact Bool.noConfusion huz1
  have htrD : transform (Dlo f g) u = 0 := by
    unfold transform
    rw [show Dlo f g = fun a => hits (zero 8) a + hits z1 a from funext hD_eq]
    have hpt (a : W 8) : (hits (zero 8) a + hits z1 a) * chr u a =
        hits (zero 8) a * chr u a + hits z1 a * chr u a := Int.add_mul _ _ _
    rw [funext hpt, total_add, select, select]
    unfold chr; rw [dot_comm 8 u (zero 8), dot_zero, huz1]; decide
  -- Meanwhile `transform (1_Z) u = ±8`!
  have htrZ := transform_Zset_eq f g res dc lores u
  have hhits0 : hits (zero 8) u = 0 := by
    unfold hits; have : ¬ zero 8 = u := fun h => hu_ne h.symm; simp [this]
  rw [hhits0, Int.mul_zero, Int.sub_zero] at htrZ
  obtain ⟨hs, hq16, _⟩ := sigma8_spec f g res hrr (add 8 u (supportXor g))
  have hq0 : q8 f g (zero 8) = 1 ∨ q8 f g (zero 8) = -1 := sign_vals _
  rw [hq16] at htrZ
  have hmod := low_autocorr_mod32 f g (by omega) lores locap u
  rw [htrD] at hmod
  rcases hq0 with h0 | h0 <;> rcases hs with h1 | h1 <;> rw [h0, h1] at htrZ <;> omega

/-- **Theorem 9 (`t108_rank6_D_eq_rad`)**: At `t = 108` rank 6 (`rr = 4`, `Zc = 112`),
    `n8 = 0`, `n0 = 4`, `transform Dlo u = 4` on `perp (β8)` and `0` elsewhere, and
    pointwise `Dlo f g a = bind (rad (β8 f g) a)` (the 4 low zeros are EXACTLY the 4-point
    radical `W` of the quadratic phase `β8`!) -/
theorem t108_rank6_D_eq_rad (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (ht : agreements f g = 108)
    (hrr : rr (β8 f g) = 4) :
    n8 f g = 0 ∧ n0 f g = 4 ∧ ∀ a : W 8, Dlo f g a = bind (rad (β8 f g) a) := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap
  have hZc : Zc f g = 112 := by
    rcases rank_Zc_values f g res dc lores with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hZ⟩ | ⟨h, _⟩ <;> omega
  have hDsum : total 8 (Dlo f g) = 4 := by rw [total_Dlo_eq]; omega
  -- `supportXor g` is in `good (β8 f g)` because `2 * 112 - 256 = -32 ≠ 0`!
  have hm8 : many 8 = 256 := by decide
  have hMM : (32 : Int) * 32 = many 8 * rr (β8 f g) := by rw [hm8, hrr]; decide
  have hgood_sx : good (β8 f g) (supportXor g) = true := by
    cases hg : good (β8 f g) (supportXor g)
    · exfalso
      have h0 : transform (q8 f g) (supportXor g) = 0 :=
        (Balanced242Rank.spec_values (β8 f g) (cube8 f g res) 32 hMM (supportXor g)).2 hg
      have hzid := Z_identity f g res dc lores
      rw [h0, Int.mul_zero] at hzid; omega
    · rfl
  -- Bound `|transform Dlo u| ≤ 4` for all `u`:
  have htrD_le (u : W 8) : -4 ≤ transform (Dlo f g) u ∧ transform (Dlo f g) u ≤ 4 := by
    have hDnn (a : W 8) : 0 ≤ Dlo f g a := by unfold Dlo; split; omega; split <;> omega
    have hup : transform (Dlo f g) u ≤ total 8 (Dlo f g) := by
      unfold transform; apply total_mono 8; intro a
      have := hDnn a; unfold chr; cases dot 8 u a <;> simp [sign] <;> omega
    have hlo : -total 8 (Dlo f g) ≤ transform (Dlo f g) u := by
      have hneg : -total 8 (Dlo f g) = total 8 (fun a => (-1 : Int) * Dlo f g a) := by
        rw [total_scale]; omega
      rw [hneg]; unfold transform; apply total_mono 8; intro a
      have := hDnn a; unfold chr; cases dot 8 u a <;> simp [sign] <;> omega
    omega
  -- For EVERY `u`, `transform Dlo u` is `±4` on `perp (β8)` and `0` off `perp (β8)`!
  have htrD_val (u : W 8) :
      (perp (β8 f g) u = true → transform (Dlo f g) u = 4 ∨ transform (Dlo f g) u = -4) ∧
      (perp (β8 f g) u = false → transform (Dlo f g) u = 0) := by
    have hmod := low_autocorr_mod32 f g (by omega) lores locap u
    have htrZ := transform_Zset_eq f g res dc lores u
    have hq0 : q8 f g (zero 8) = 1 ∨ q8 f g (zero 8) = -1 := sign_vals _
    have hbd := htrD_le u
    constructor
    · intro hp
      by_cases hu0 : u = zero 8
      · subst hu0; left
        unfold transform
        have h1 (a : W 8) : Dlo f g a * chr (zero 8) a = Dlo f g a := by simp [chr, dot_zero, sign]
        rw [funext h1, hDsum]
      · have hhits0 : hits (zero 8) u = 0 := by
          unfold hits; have : ¬ zero 8 = u := fun h => hu0 h.symm; simp [this]
        rw [hhits0, Int.mul_zero, Int.sub_zero] at htrZ
        have hgu : good (β8 f g) (add 8 u (supportXor g)) = true := by
          rw [add_comm]; exact good_shift (β8 f g) hgood_sx hp
        have htrq : transform (q8 f g) (add 8 u (supportXor g)) = 32 ∨
            transform (q8 f g) (add 8 u (supportXor g)) = -32 :=
          (Balanced242Rank.spec_values (β8 f g) (cube8 f g res) 32 hMM (add 8 u (supportXor g))).1 hgu
        rcases hq0 with h0 | h0 <;> rcases htrq with h1 | h1 <;> rw [h0, h1] at htrZ <;> omega
    · intro hnp
      have hu0 : u ≠ zero 8 := by
        intro hz; subst hz
        have hp0 : perp (β8 f g) (zero 8) = true := by
          rw [perp_spec]; intro e _; exact dot_zero 8 e
        rw [hp0] at hnp; exact Bool.noConfusion hnp
      have hhits0 : hits (zero 8) u = 0 := by
        unfold hits; have : ¬ zero 8 = u := fun h => hu0 h.symm; simp [this]
      rw [hhits0, Int.mul_zero, Int.sub_zero] at htrZ
      have hgu : good (β8 f g) (add 8 u (supportXor g)) = false := by
        cases hg : good (β8 f g) (add 8 u (supportXor g))
        · rfl
        · exfalso
          have hp := good_perp (β8 f g) hg hgood_sx
          rw [Balanced242Plateau.add_assoc', add_self, add_zero_right] at hp
          rw [hp] at hnp; exact Bool.noConfusion hnp
      have htrq : transform (q8 f g) (add 8 u (supportXor g)) = 0 :=
        (Balanced242Rank.spec_values (β8 f g) (cube8 f g res) 32 hMM (add 8 u (supportXor g))).2 hgu
      rw [htrq, Int.mul_zero] at htrZ
      omega
  -- Parseval gives `∑ Dlo^2 = 4`, forcing `n8 = 0, n0 = 4`!
  have hsq_eq (u : W 8) : transform (Dlo f g) u * transform (Dlo f g) u = 16 * bind (perp (β8 f g) u) := by
    cases hp : perp (β8 f g) u
    · rw [(htrD_val u).2 hp]; decide
    · rcases (htrD_val u).1 hp with h | h <;> rw [h] <;> decide
  have hpar := Balanced242Section0320.parseval (Dlo f g)
  rw [funext hsq_eq, total_scale, hm8] at hpar
  have hperp_cnt : total 8 (fun u => bind (perp (β8 f g) u)) = 64 := by
    have hrp := rr_perp (β8 f g); rw [hrr, hm8] at hrp; omega
  rw [hperp_cnt] at hpar
  have hD2_eq : total 8 (fun a => Dlo f g a * Dlo f g a) = n0 f g + 4 * n8 f g := by
    unfold n0 n8 Dlo; rw [← total_scale, ← total_add]
    apply congrArg (total 8); funext a
    by_cases h0 : lo f g a = 0
    · rw [h0]; decide
    · by_cases h8 : (lo f g a).natAbs = 8 <;> simp [h0, h8]
  rw [hD2_eq] at hpar
  have hn80 : n8 f g = 0 := by omega
  have hn04 : n0 f g = 4 := by omega
  -- Moreover `transform Dlo u` CANNOT be `-4` because `Dlo (zero 8) = 1`!
  have htrD_exact (u : W 8) : transform (Dlo f g) u = 4 * bind (perp (β8 f g) u) := by
    cases hp : perp (β8 f g) u
    · rw [(htrD_val u).2 hp]; rfl
    · rcases (htrD_val u).1 hp with h | h
      · rw [h]; rfl
      · exfalso
        have hD0 : Dlo f g (zero 8) = 1 := by unfold Dlo; simp [dc]
        have hge : -2 ≤ transform (Dlo f g) u := by
          have hpt (a : W 8) : 2 * hits (zero 8) a - Dlo f g a ≤ Dlo f g a * chr u a := by
            have hDnn : 0 ≤ Dlo f g a := by unfold Dlo; split; omega; split <;> omega
            unfold hits chr
            by_cases hz : zero 8 = a
            · subst hz; rw [dot_comm 8 u (zero 8), dot_zero]; simp [sign, hD0]
            · simp only [hz, if_false, Int.mul_zero, Int.zero_sub]
              cases dot 8 u a <;> simp [sign] <;> omega
          have hm := total_mono 8 _ _ hpt
          rw [total_sub, total_scale, diagonal, hDsum] at hm
          exact hm
        omega
  -- Now Walsh-invert BOTH `Dlo` and `bind ∘ rad` to prove `Dlo f g a = bind (rad (β8 f g) a)`!
  have htr_rad (u : W 8) : transform (fun a => bind (rad (β8 f g) a)) u = 4 * bind (perp (β8 f g) u) := by
    unfold transform
    have hpt (a : W 8) : bind (rad (β8 f g) a) * chr u a = bind (rad (β8 f g) a) * sign (dot 8 u a) := rfl
    rw [funext hpt]
    have hch := char_radical (β8 f g) (dot 8 u) (fun e _ d => dot_right 8 u e d)
    cases hp : perp (β8 f g) u
    · rw [hch.1 hp]; rfl
    · rw [hch.2 hp]; change rr (β8 f g) = 4 * 1; rw [hrr]; omega
  refine ⟨hn80, hn04, fun a => ?_⟩
  have hinv1 := transform_involution (Dlo f g) a
  have hinv2 := transform_involution (fun x => bind (rad (β8 f g) x)) a
  have hteq : transform (Dlo f g) = transform (fun x => bind (rad (β8 f g) x)) :=
    funext (fun u => by rw [htrD_exact u, htr_rad u])
  rw [hteq, hinv2, hm8] at hinv1
  omega

end Balanced242LowBlock

#print axioms Balanced242LowBlock.low_defect_pointwise
#print axioms Balanced242LowBlock.low_defect_budget
#print axioms Balanced242LowBlock.autocorr_V_even
#print axioms Balanced242LowBlock.transform_sq_eq_autocorr
#print axioms Balanced242LowBlock.low_autocorr_mod32
#print axioms Balanced242LowBlock.rank_Zc_values
#print axioms Balanced242LowBlock.t_ge_114_forces_Z64
#print axioms Balanced242LowBlock.t112_forces_rank4_or_Z64
#print axioms Balanced242LowBlock.no_t106_rank8
#print axioms Balanced242LowBlock.t108_rank6_D_eq_rad

