/-
  Formalization of the anchor-pair symplectic rank split, 6-variable sub-section bounds,
  and degree-2 / degree-4 Krawtchouk moment inequalities (powering `check_t94_anchor_pairs.py`
  and `replay.py`, which close `t = 94` and tighten `t = 96..102`):

    Part 1 — Anchor-pair symplectic rank split (`anchor_pair_ranks_63_64`):
      At global phase rank 8 (`Cube β`, `rr β = 1`), fixing any nonzero anchor direction
      `w : W 8` splits `β` into two 7-variable sections `β0, β1` (`c = false, true`).
      Both halves share the exact same polar bilinear form (`sec_ell_eq`), radical (`rr = 2`),
      and `perp` predicate (`sec_perp_eq`). Among the 127 nonzero quotient directions `v : W 7`:
        * exactly 63 have `perp β0 v = true`, giving 6-variable rank-4 sub-sections
          (plateau height `m = 16`) on BOTH halves simultaneously;
        * exactly 64 have `perp β0 v = false`, giving 6-variable rank-6 sub-sections
          (plateau height `m = 8`) on BOTH halves simultaneously.

    Part 2 — Exact 6-variable sub-section bounds (`six_section_energy`, `six_section_div4`,
      `six_section_jensen`):
      For any 6-variable sub-section `E : W 6 → Int` (`|E| ≤ 4`, `transform E = 2 H`, `H` odd,
      `|H| ≤ 7`, plateau height `m ∈ {8, 16}`):
        * `2 * ∑ E² = 392 - M`, `4 ∣ M`, `2 ∣ (b + c)`;
        * `scale ∣ T6`, `tau = |T6 / scale| ≤ 4 * sz`;
        * integer Jensen floor `(sz - j) * q² + j * (q + 1)² ≤ ∑ E²` (`q = tau / sz`, `j = tau % sz`).

    Part 3 — Krawtchouk degree-2 equalities & degree-4 nonnegativity inequalities (all `n`):
      For pairwise disjoint Boolean subsets `P, Q, R : W n → Bool` with `A = transform (ind P)`, etc.:
        * `kraw_deg2_200`, `kraw_deg2_110` (exact equalities over nonzero `v : W n`),
        * `kraw_deg4_400`, `kraw_deg4_310`, `kraw_deg4_220`, `kraw_deg4_211` (exact lower bounds).

  Zero Mathlib, zero `sorry`, zero `native_decide`, pure `[propext, Quot.sound]`.
-/
import Balanced242Rank8

namespace Balanced242AnchorPair
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Hyperplane Balanced242Global
open Balanced242Reduction (ind cnt nz parseval2 nz_total transform_ind_zero)
open Balanced242Plateau (Cube ell rad phi rad_spec ind_nonneg add_assoc' add_zero_right sign_sq)
open Balanced242Rank (good perp rr rr_pos spec_good rr_perp spec_values section_levels perp_spec)

local notation "phase" => Balanced242Section0320.phase
local notation "bind" => Balanced242Plateau.ind

/-! ## Part 1: Anchor-pair symplectic 63/64 rank split -/

theorem secPt_zero_false : ∀ (n : Nat) (w : W (n + 1)),
    secPt n w false (zero n) = zero (n + 1)
  | 0, (true, _) => by rw [secPt_true]; simp [dot_zero_right]; rfl
  | 0, (false, _) => rfl
  | m + 1, (true, w') => by rw [secPt_true]; simp [dot_zero_right]; rfl
  | m + 1, (false, w') => by
    show (false, secPt m w' false (zero m)) = (false, zero (m + 1))
    rw [secPt_zero_false m w']

theorem secPt_add_false : ∀ (n : Nat) (w : W (n + 1)) (c : Bool) (u a : W n),
    secPt n w c (add n u a) = add (n + 1) (secPt n w false u) (secPt n w c a)
  | 0, (true, _), c, (), () => by
    rw [secPt_true, secPt_true, secPt_true]; cases c <;> rfl
  | 0, (false, _), c, (), () => by cases c <;> rfl
  | m + 1, (true, w'), c, u, a => by
    rw [secPt_true, secPt_true, secPt_true]
    change (xor c (dot (m + 1) w' (add (m + 1) u a)), add (m + 1) u a) =
           (xor (xor false (dot (m + 1) w' u)) (xor c (dot (m + 1) w' a)), add (m + 1) u a)
    rw [dot_right]
    exact Prod.ext (by cases c <;> cases dot (m + 1) w' u <;> cases dot (m + 1) w' a <;> rfl) rfl
  | m + 1, (false, w'), c, (bu, u'), (ba, a') => by
    show (xor bu ba, secPt m w' c (add m u' a')) =
         (xor bu ba, add (m + 1) (secPt m w' false u') (secPt m w' c a'))
    rw [secPt_add_false m w' c u' a']

theorem secPt_true_shift (n : Nat) (w : W (n + 1)) (a : W n) :
    secPt n w true a = add (n + 1) (secPt n w true (zero n)) (secPt n w false a) := by
  have h := secPt_add_false n w true a (zero n)
  rw [add_zero_right, add_comm (n + 1)] at h
  exact h

/-- Hyperplane restriction preserves `Cube` (quadratic phase). -/
theorem sec_cube {n : Nat} (β : W (n + 1) → Bool) (hc : Cube β) (w : W (n + 1)) (c : Bool) :
    Cube (fun a => β (secPt n w c a)) := by
  intro u v z a
  simp only [secPt_add_false]
  exact hc (secPt n w false u) (secPt n w false v) (secPt n w false z) (secPt n w c a)

/-- Both complementary hyperplanes (`c = false` and `c = true`) have the exact same polar form. -/
theorem sec_ell_eq {n : Nat} (β : W (n + 1) → Bool) (hc : Cube β) (w : W (n + 1)) (d a : W n) :
    ell (fun x => β (secPt n w false x)) d a = ell (fun x => β (secPt n w true x)) d a := by
  unfold ell
  let x1 := secPt n w true (zero n)
  let u := secPt n w false d
  let v := secPt n w false a
  have h0 := hc x1 u v (zero (n + 1))
  simp only [add_zero_right] at h0
  have e1 : secPt n w true a = add (n + 1) x1 v := secPt_true_shift n w a
  have e2 : secPt n w true d = add (n + 1) x1 u := secPt_true_shift n w d
  have e3 : secPt n w false (add n a d) = add (n + 1) u v := by
    rw [add_comm n a d, secPt_add_false]
  have e4 : secPt n w true (add n a d) = add (n + 1) x1 (add (n + 1) u v) := by
    rw [secPt_true_shift, e3]
  have e0 : secPt n w false (zero n) = zero (n + 1) := secPt_zero_false n w
  dsimp only
  rw [e0, e1, e2, e3, e4]
  revert h0
  generalize β (add (n + 1) x1 (add (n + 1) u v)) = p1
  generalize β (add (n + 1) u v) = p2
  generalize β (add (n + 1) x1 v) = p3
  generalize β v = p4
  generalize β (add (n + 1) x1 u) = p5
  generalize β u = p6
  generalize β x1 = p7
  generalize β (zero (n + 1)) = p8
  cases p1 <;> cases p2 <;> cases p3 <;> cases p4 <;>
  cases p5 <;> cases p6 <;> cases p7 <;> cases p8 <;> decide

theorem sec_rad_eq {n : Nat} (β : W (n + 1) → Bool) (hc : Cube β) (w : W (n + 1)) (d : W n) :
    rad (fun x => β (secPt n w false x)) d = rad (fun x => β (secPt n w true x)) d := by
  unfold rad
  congr 1; funext a; rw [sec_ell_eq β hc w d a]

theorem sec_perp_eq {n : Nat} (β : W (n + 1) → Bool) (hc : Cube β) (w : W (n + 1)) (v : W n) :
    perp (fun x => β (secPt n w false x)) v = perp (fun x => β (secPt n w true x)) v := by
  unfold perp
  congr 1; funext d; rw [sec_rad_eq β hc w d]

private theorem perp_zero {n : Nat} (β : W n → Bool) : perp β (zero n) = true := by
  rw [perp_spec]; intro e _; exact dot_zero n e

/-- Exact anchor-pair symplectic 63/64 rank-split theorem at global rank 8. -/
theorem anchor_pair_ranks_63_64 (β : W 8 → Bool) (hc : Cube β) (hrr : rr β = 1)
    (w : W 8) (hw : w ≠ zero 8) :
    let β0 : W 7 → Bool := fun a => β (secPt 7 w false a)
    let β1 : W 7 → Bool := fun a => β (secPt 7 w true a)
    rr β0 = 2 ∧ rr β1 = 2 ∧
    (∀ v, perp β0 v = perp β1 v) ∧
    total 7 (fun v => nz v * bind (perp β0 v)) = 63 ∧
    total 7 (fun v => nz v * bind (!perp β0 v)) = 64 ∧
    (∀ (v : W 7), v ≠ zero 7 → ∀ (c0 c1 : Bool) (y : W 6),
      let βc := fun a => β (secPt 7 w c0 a)
      (perp β0 v = true →
        transform (fun a => sign (βc (secPt 6 v c1 a))) y = 0 ∨
        transform (fun a => sign (βc (secPt 6 v c1 a))) y = 16 ∨
        transform (fun a => sign (βc (secPt 6 v c1 a))) y = -16) ∧
      (perp β0 v = false →
        transform (fun a => sign (βc (secPt 6 v c1 a))) y = 0 ∨
        transform (fun a => sign (βc (secPt 6 v c1 a))) y = 8 ∨
        transform (fun a => sign (βc (secPt 6 v c1 a))) y = -8)) := by
  intro β0 β1
  have hpeq : ∀ v, perp β0 v = perp β1 v := sec_perp_eq β hc w
  have hc0 : Cube β0 := sec_cube β hc w false
  have hc1 : Cube β1 := sec_cube β hc w true
  have hrr_eq : rr β0 = rr β1 := by
    unfold rr; apply congrArg (total 7); funext d; rw [sec_rad_eq β hc w d]
  -- Every direction `w` at rank 8 is in `perp β` since `rr β = 1` (`rad β = {0}`)
  have hperpw : perp β w = true := by
    rw [perp_spec]; intro e he
    if he0 : e = zero 8 then
      subst he0; exact dot_zero_right 8 w
    else
      exfalso
      have hne : zero 8 ≠ e := fun h => he0 h.symm
      -- If both `0` and `e` are in `rad β`, then `rr β ≥ 2`, contradicting `rr β = 1`
      have h2 : bind (rad β (zero 8)) + bind (rad β e) ≤ total 8 (fun d => bind (rad β d)) := by
        have hstep : ∀ (n : Nat) (F : W n → Int), (∀ x, 0 ≤ F x) → ∀ x y : W n, x ≠ y → F x + F y ≤ total n F := by
          intro n; induction n with
          | zero => intro F _ () () h; exact absurd rfl h
          | succ m ih =>
            intro F hnn ⟨b1, x1⟩ ⟨b2, x2⟩ hxy
            show F (b1, x1) + F (b2, x2) ≤ total m (fun z => F (false, z)) + total m (fun z => F (true, z))
            have h0 : 0 ≤ total m (fun z => F (false, z)) := by
              rw [← total_zero m]; exact total_mono m _ _ (fun z => hnn (false, z))
            have h1 : 0 ≤ total m (fun z => F (true, z)) := by
              rw [← total_zero m]; exact total_mono m _ _ (fun z => hnn (true, z))
            cases b1 <;> cases b2
            · have := ih (fun z => F (false, z)) (fun z => hnn _) x1 x2 (fun h => hxy (by rw [h]))
              dsimp only at this; omega
            · have p1 := Balanced242SectionFacts.point_le_total m (fun z => F (false, z)) (fun z => hnn _) x1
              have p2 := Balanced242SectionFacts.point_le_total m (fun z => F (true, z)) (fun z => hnn _) x2
              omega
            · have p1 := Balanced242SectionFacts.point_le_total m (fun z => F (true, z)) (fun z => hnn _) x1
              have p2 := Balanced242SectionFacts.point_le_total m (fun z => F (false, z)) (fun z => hnn _) x2
              omega
            · have := ih (fun z => F (true, z)) (fun z => hnn _) x1 x2 (fun h => hxy (by rw [h]))
              dsimp only at this; omega
        exact hstep 8 (fun d => bind (rad β d)) (fun d => ind_nonneg _) (zero 8) e hne
      rw [Balanced242Rank.rad_zero β, he] at h2
      change 1 + 1 ≤ rr β at h2; omega
  -- For `β0`, `section_levels` gives values in `{0, ±16}`, forcing `rr β0 = 2`
  have hlev0 (y : W 7) :
      transform (fun a => sign (β0 a)) y = 0 ∨
      transform (fun a => sign (β0 a)) y = 16 ∨
      transform (fun a => sign (β0 a)) y = -16 :=
    (section_levels β hc w hw false 16 (by rw [hrr]; decide) y).1 hperpw
  have hrr0 : rr β0 = 2 := by
    have hpar := Balanced242Section0320.parseval (fun a => sign (β0 a))
    have hsq1 (a : W 7) : sign (β0 a) * sign (β0 a) = 1 := sign_sq _
    rw [funext hsq1, total_const] at hpar
    have hspec_sq (y : W 7) := spec_good β0 hc0 y
    have hm128 : many 7 = 128 := by decide
    rw [hm128] at hpar
    -- There exists `y` with `good β0 y = true` since `sum (transform^2) = 16384 > 0`
    have hex : ∃ y : W 7, good β0 y = true := by
      cases hall : (worlds 7).all (fun y => !good β0 y)
      · obtain ⟨y, _, hy⟩ := Balanced242Plateau.all_false_exists _ _ hall
        exact ⟨y, by cases hg : good β0 y <;> simp [hg] at hy ⊢⟩
      · exfalso
        have hz (y : W 7) : transform (fun a => sign (β0 a)) y * transform (fun a => sign (β0 a)) y = 0 := by
          have hg : good β0 y = false := by
            have := List.all_eq_true.mp hall y (all_worlds 7 y)
            cases h : good β0 y <;> simp [h] at this ⊢
          rw [hspec_sq y, hg]; simp [Balanced242Plateau.ind]
        rw [funext hz, total_zero] at hpar; omega
    obtain ⟨y, hy⟩ := hex
    have hs := hspec_sq y
    rw [hy, hm128] at hs
    simp only [Balanced242Plateau.ind, if_true, Int.mul_one] at hs
    rcases hlev0 y with h | h | h <;> rw [h] at hs
    · have := rr_pos β0; omega
    · exact Int.eq_of_mul_eq_mul_left (by decide : (128 : Int) ≠ 0) (hs.symm.trans (by decide))
    · exact Int.eq_of_mul_eq_mul_left (by decide : (128 : Int) ≠ 0) (hs.symm.trans (by decide))
  have hrr1 : rr β1 = 2 := hrr_eq.symm.trans hrr0
  -- Exact count: 64 total in `perp β0`, so 63 nonzero (`perp = true`) and 64 nonzero (`perp = false`)
  have hperp_tot : total 7 (fun v => bind (perp β0 v)) = 64 := by
    have hp := rr_perp β0
    rw [hrr0] at hp
    have hm128 : many 7 = 128 := by decide
    rw [hm128] at hp
    exact Int.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) (hp.trans (by decide))
  have h63 : total 7 (fun v => nz v * bind (perp β0 v)) = 63 := by
    rw [nz_total, hperp_tot, perp_zero]; rfl
  have h64 : total 7 (fun v => nz v * bind (!perp β0 v)) = 64 := by
    have hsum : total 7 (fun v => nz v * bind (perp β0 v)) +
        total 7 (fun v => nz v * bind (!perp β0 v)) = 127 := by
      rw [← total_add]
      have hpt (v : W 7) : nz v * bind (perp β0 v) + nz v * bind (!perp β0 v) = nz v * 1 := by
        cases perp β0 v <;> simp [Balanced242Plateau.ind]
      rw [funext hpt, nz_total, total_const]
      have hm128 : many 7 = 128 := by decide
      rw [hm128]; decide
    omega
  refine ⟨hrr0, hrr1, hpeq, h63, h64, ?_⟩
  intro v hv c0 c1 y
  cases c0
  · have hL := section_levels β0 hc0 v hv c1 16 (by rw [hrr0]; decide) y
    refine ⟨fun hp => hL.1 hp, fun hp => ?_⟩
    have h2 := hL.2 hp
    rcases h2 with h | h | h
    · left; exact Int.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) (h.trans (by decide))
    · right; left; exact Int.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) (h.trans (by decide))
    · right; right; exact Int.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) (h.trans (by decide))
  · have hL := section_levels β1 hc1 v hv c1 16 (by rw [hrr1]; decide) y
    refine ⟨fun hp => hL.1 (by rw [← hpeq v]; exact hp), fun hp => ?_⟩
    have h2 := hL.2 (by rw [← hpeq v]; exact hp)
    rcases h2 with h | h | h
    · left; exact Int.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) (h.trans (by decide))
    · right; left; exact Int.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) (h.trans (by decide))
    · right; right; exact Int.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) (h.trans (by decide))

/-! ## Part 2: Exact 6-variable sub-section bounds (`replay.py`'s `six(p, r)`) -/

private theorem H6_vals (h : Int) (ho : h % 2 = 1) (hc : h.natAbs ≤ 7) :
    h = -7 ∨ h = -5 ∨ h = -3 ∨ h = -1 ∨ h = 1 ∨ h = 3 ∨ h = 5 ∨ h = 7 := by omega

private theorem sq_point6 (h : Int) (ho : h % 2 = 1) (hc : h.natAbs ≤ 7) :
    h * h = 49 - 8 * (6 * (if h.natAbs = 1 then (1 : Int) else 0) +
                      3 * (if h.natAbs = 5 then (1 : Int) else 0) +
                      5 * (if h.natAbs = 3 then (1 : Int) else 0)) := by
  rcases H6_vals h ho hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem t6_point6 (h : Int) (ho : h % 2 = 1) (hc : h.natAbs ≤ 7) :
    phase h * h = -7 + 8 * (if h.natAbs = 1 then (1 : Int) else 0) +
                      12 * (if h.natAbs = 5 then (1 : Int) else 0) +
                       4 * (if h.natAbs = 3 then (1 : Int) else 0) := by
  rcases H6_vals h ho hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Exact 6-variable Parseval energy: `2 * ∑ E² = 392 - M`. -/
theorem six_section_energy (E H : W 6 → Int) (hspec : ∀ a, transform E a = 2 * H a)
    (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7) :
    let a := total 6 (fun u => if (H u).natAbs = 1 then (1 : Int) else 0)
    let b := total 6 (fun u => if (H u).natAbs = 5 then (1 : Int) else 0)
    let c := total 6 (fun u => if (H u).natAbs = 3 then (1 : Int) else 0)
    2 * total 6 (fun y => E y * E y) = 392 - (6 * a + 3 * b + 5 * c) := by
  intro a b c
  have hpar := Balanced242Section0320.parseval E
  have hlhs : total 6 (fun u => transform E u * transform E u) = 4 * total 6 (fun u => H u * H u) := by
    rw [← total_scale]; apply congrArg (total 6); funext u
    rw [hspec u, Int.mul_assoc 2 (H u), Int.mul_left_comm (H u) 2 (H u), ← Int.mul_assoc 2 2]; rfl
  have hsq : total 6 (fun u => H u * H u) = 64 * 49 - 8 * (6 * a + 3 * b + 5 * c) := by
    have pt (u : W 6) := sq_point6 (H u) (hH u).1 (hH u).2
    rw [funext pt, total_sub, total_const, total_scale, total_add, total_add,
        total_scale, total_scale, total_scale]
    change (64 : Int) * 49 - 8 * (6 * a + 3 * b + 5 * c) = _; rfl
  have hm64 : many 6 = 64 := by decide
  rw [hlhs, hsq, hm64] at hpar
  omega

/-- Exact 6-variable mod-4 mass divisibility and `b + c` parity. -/
theorem six_section_div4 (E H : W 6 → Int) (hspec : ∀ a, transform E a = 2 * H a)
    (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7) :
    let a := total 6 (fun u => if (H u).natAbs = 1 then (1 : Int) else 0)
    let b := total 6 (fun u => if (H u).natAbs = 5 then (1 : Int) else 0)
    let c := total 6 (fun u => if (H u).natAbs = 3 then (1 : Int) else 0)
    (6 * a + 3 * b + 5 * c) % 4 = 0 ∧ (b + c) % 2 = 0 := by
  intro a b c
  have hene := six_section_energy E H hspec hH
  dsimp only at hene
  have heven : total 6 (fun y => E y * E y) % 2 = 0 := by
    have hdiff : total 6 (fun y => E y * E y - E y) % 2 = 0 := by
      have h2 (n : Nat) (F : W n → Int) (hF : ∀ y, F y % 2 = 0) : total n F % 2 = 0 := by
        induction n with
        | zero => exact hF ()
        | succ m ih =>
          show (total m (fun z => F (false, z)) + total m (fun z => F (true, z))) % 2 = 0
          have h0 := ih (fun z => F (false, z)) (fun z => hF (false, z))
          have h1 := ih (fun z => F (true, z)) (fun z => hF (true, z))
          omega
      apply h2 6; intro y
      have hsub : E y * E y - E y = E y * (E y - 1) := by rw [Int.mul_sub, Int.mul_one]
      rw [hsub]
      if h0 : E y % 2 = 0 then
        rw [Int.mul_emod, h0, Int.zero_mul]; rfl
      else
        have h1 : (E y - 1) % 2 = 0 := by omega
        rw [Int.mul_emod, h1, Int.mul_zero]; rfl
    have hsumE : total 6 E = 2 * H (zero 6) := by
      have hs := hspec (zero 6)
      unfold transform at hs
      have hchr (y : W 6) : E y * chr (zero 6) y = E y := by simp [chr, dot_zero, sign]
      rw [funext hchr] at hs; exact hs
    rw [total_sub, hsumE] at hdiff
    omega
  exact ⟨by omega, by omega⟩

private theorem jensen_int_pt (u q : Int) : (2 * q + 1) * u - q * (q + 1) ≤ u * u := by
  have hprod : 0 ≤ (u - q) * (u - q - 1) := by
    if h : q + 1 ≤ u then
      exact Int.mul_nonneg (by omega) (by omega)
    else if h0 : u = q then
      subst h0; simp
    else
      have h1 : u - q ≤ 0 := by omega
      have h2 : u - q - 1 ≤ 0 := by omega
      have hpos : 0 ≤ (-(u - q)) * (-(u - q - 1)) := Int.mul_nonneg (by omega) (by omega)
      rw [Int.neg_mul_neg] at hpos; exact hpos
  have hexp : (u - q) * (u - q - 1) = u * u - ((2 * q + 1) * u - q * (q + 1)) := by
    have h1 : (u - q) * (u - q - 1) = u * u - u * q - u - q * u + q * q + q := by
      simp only [Int.sub_mul, Int.mul_sub, Int.mul_one]; omega
    have h2 : (2 * q + 1) * u = q * u + q * u + u := by
      rw [Int.add_mul, Int.one_mul]
      have : 2 * q = q + q := by omega
      rw [this, Int.add_mul]
    have h3 : q * (q + 1) = q * q + q := by rw [Int.mul_add, Int.mul_one]
    rw [h1, h2, h3, Int.mul_comm u q]; omega
  omega

/-- Exact 6-variable `T6` divisibility, amplitude cap, and integer Jensen floor (`replay.py`'s `six`). -/
theorem six_section_jensen (E H : W 6 → Int) (hE : ∀ y, -4 ≤ E y ∧ E y ≤ 4)
    (hspec : ∀ a, transform E a = 2 * H a) (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7)
    (m : Int) (hm : m = 8 ∨ m = 16)
    (hplat : ∀ y, transform (fun a => phase (H a)) y = 0 ∨
      transform (fun a => phase (H a)) y = m ∨ transform (fun a => phase (H a)) y = -m) :
    let a := total 6 (fun u => if (H u).natAbs = 1 then (1 : Int) else 0)
    let b := total 6 (fun u => if (H u).natAbs = 5 then (1 : Int) else 0)
    let c := total 6 (fun u => if (H u).natAbs = 3 then (1 : Int) else 0)
    let M := 6 * a + 3 * b + 5 * c
    let T6 := -448 + 8 * a + 12 * b + 4 * c
    let scale := m / 2
    let sz := 4096 / (m * m)
    T6 % scale = 0 ∧
    let tau : Int := (T6 / scale).natAbs
    let q := tau / sz
    let j := tau % sz
    tau ≤ 4 * sz ∧
    2 * ((sz - j) * (q * q) + j * ((q + 1) * (q + 1))) ≤ 392 - M := by
  intro a b c M T6 scale sz
  let ph : W 6 → Int := fun u => phase (H u)
  let σ : W 6 → Int := fun y => transform ph y / m
  have hσ (y : W 6) : σ y = -1 ∨ σ y = 0 ∨ σ y = 1 := by
    dsimp only [σ]; rcases hm with rfl | rfl <;> rcases hplat y with h | h | h <;> rw [h] <;> decide
  have hmσ (y : W 6) : transform ph y = m * σ y := by
    dsimp only [σ]; rcases hm with rfl | rfl <;> rcases hplat y with h | h | h <;> rw [h] <;> decide
  have ht6 : total 6 (fun u => ph u * H u) = T6 := by
    have pt (u : W 6) := t6_point6 (H u) (hH u).1 (hH u).2
    dsimp only [ph, T6]
    rw [funext pt, total_add, total_add, total_add, total_const,
        total_scale, total_scale, total_scale]
    change (64 : Int) * (-7) + 8 * a + 12 * b + 4 * c = _; omega
  have hdual : m * total 6 (fun y => E y * σ y) = 2 * T6 := by
    have hd := Balanced242Section0320.duality E ph
    have hlhs : total 6 (fun y => E y * transform ph y) = m * total 6 (fun y => E y * σ y) := by
      rw [← total_scale]; apply congrArg (total 6); funext y; rw [hmσ y, Int.mul_left_comm]
    have hrhs : total 6 (fun u => ph u * transform E u) = 2 * T6 := by
      rw [← ht6, ← total_scale]; apply congrArg (total 6); funext u; rw [hspec u, Int.mul_left_comm]
    rw [← hlhs, ← hrhs]; exact hd.symm
  have hsc : scale * total 6 (fun y => E y * σ y) = T6 := by
    dsimp only [scale]; rcases hm with rfl | rfl <;> omega
  have hdiv : T6 % scale = 0 := by rw [← hsc, Int.mul_emod_right]
  have htau_val : total 6 (fun y => E y * σ y) = T6 / scale := by
    have hpos : scale ≠ 0 := by dsimp only [scale]; rcases hm with rfl | rfl <;> decide
    rw [← hsc, Int.mul_ediv_cancel_left _ hpos]
  have hsz : total 6 (fun y => if σ y = 0 then (0 : Int) else 1) = sz := by
    have hpar := Balanced242Section0320.parseval ph
    have hq1 (u : W 6) : ph u * ph u = 1 := by
      dsimp only [ph]; unfold Balanced242Section0320.phase; split <;> decide
    have hqsq (y : W 6) : transform ph y * transform ph y = (m * m) * (if σ y = 0 then (0 : Int) else 1) := by
      rw [hmσ y]; rcases hσ y with h | h | h <;> rw [h] <;> simp
    rw [funext hqsq, total_scale, funext hq1, total_const] at hpar
    have hm64 : many 6 = 64 := by decide
    rw [hm64] at hpar; dsimp only [sz]; rcases hm with rfl | rfl <;> omega
  -- Pick sign `ε ∈ {1, -1}` so `ε * total 6 (E * σ) = tau`
  let tau : Int := (T6 / scale).natAbs
  let q := tau / sz
  let j := tau % sz
  let ε : Int := if 0 ≤ T6 / scale then 1 else -1
  have hε : ε = 1 ∨ ε = -1 := by
    dsimp only [ε]; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hε_tau : ε * total 6 (fun y => E y * σ y) = tau := by
    rw [htau_val]; dsimp only [ε, tau]; split <;> omega
  have hcap4 : tau ≤ 4 * sz := by
    have hpt (y : W 6) : ε * (E y * σ y) ≤ 4 * (if σ y = 0 then (0 : Int) else 1) := by
      have hEy := hE y
      rcases hε with h1 | h1 <;> rw [h1] <;> rcases hσ y with h2 | h2 | h2 <;> rw [h2] <;> simp <;> omega
    have hsum := total_mono 6 _ _ hpt
    rw [total_scale, total_scale, hε_tau, hsz] at hsum; exact hsum
  have hjen : (2 * q + 1) * tau - sz * (q * (q + 1)) ≤ total 6 (fun y => E y * E y) := by
    have hpt (y : W 6) :
        (2 * q + 1) * (ε * (E y * σ y)) - (q * (q + 1)) * (if σ y = 0 then (0 : Int) else 1) ≤
          E y * E y := by
      rcases hσ y with h2 | h2 | h2
      · rw [h2]; simp only [show (-1 : Int) ≠ 0 from by decide, if_false, Int.mul_one]
        have hj := jensen_int_pt (ε * (E y * -1)) q
        have hsq : (ε * (E y * -1)) * (ε * (E y * -1)) = E y * E y := by
          rcases hε with h1 | h1 <;> rw [h1] <;>
            simp [Int.mul_neg, Int.neg_mul, Int.neg_neg]
        rw [hsq] at hj; exact hj
      · rw [h2]; simp only [Int.mul_zero, if_true, Int.sub_self]
        exact if h : 0 ≤ E y then Int.mul_nonneg h h else Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      · rw [h2]; simp only [show (1 : Int) ≠ 0 from by decide, if_false, Int.mul_one]
        have hj := jensen_int_pt (ε * E y) q
        have hsq : (ε * E y) * (ε * E y) = E y * E y := by
          rcases hε with h1 | h1 <;> rw [h1] <;>
            simp [Int.mul_neg, Int.neg_mul, Int.neg_neg]
        rw [hsq] at hj; exact hj
    have hsum := total_mono 6 _ _ hpt
    rw [total_sub, total_scale, total_scale, total_scale, hε_tau, hsz, Int.mul_comm (q * (q + 1)) sz] at hsum
    exact hsum
  have hident : (sz - j) * (q * q) + j * ((q + 1) * (q + 1)) = (2 * q + 1) * tau - sz * (q * (q + 1)) := by
    have hdiv_tau : sz * q + j = tau := Int.ediv_add_emod tau sz
    rw [← hdiv_tau]
    have e1 : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by
      simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]; omega
    have e2 : (2 * q + 1) * (sz * q + j) = 2 * sz * (q * q) + sz * q + 2 * j * q + j := by
      simp only [Int.add_mul, Int.mul_add, Int.one_mul]
      have a1 : 2 * q * (sz * q) = 2 * sz * (q * q) := by
        rw [Int.mul_assoc 2 q, Int.mul_left_comm q sz q, ← Int.mul_assoc 2 sz]
      have a2 : 2 * q * j = 2 * j * q := by rw [Int.mul_assoc 2 q j, Int.mul_comm q j, ← Int.mul_assoc]
      rw [a1, a2]; omega
    have e3 : sz * (q * (q + 1)) = sz * (q * q) + sz * q := by
      rw [Int.mul_add, Int.mul_one, Int.mul_add]
    have e4 : (sz - j) * (q * q) + j * (q * q + 2 * q + 1) = sz * (q * q) + 2 * j * q + j := by
      rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_one]
      have a3 : j * (2 * q) = 2 * j * q := by rw [← Int.mul_assoc, Int.mul_comm j 2]
      rw [a3]; omega
    have h2k : 2 * sz * (q * q) = 2 * (sz * (q * q)) := Int.mul_assoc 2 sz (q * q)
    rw [e1, e2, e3, e4, h2k]; omega
  have hene := six_section_energy E H hspec hH
  dsimp only at hene
  refine ⟨hdiv, hcap4, ?_⟩
  rw [hident]; omega

/-! ## Part 3: Degree-2 and degree-4 Krawtchouk identities & inequalities (all `n`) -/

def kraw1 (A : Int) : Int := A
def kraw2 (s A : Int) : Int := A * A - s
def kraw3 (s A : Int) : Int := A * A * A - (3 * s - 2) * A
def kraw4 (s A : Int) : Int := A * A * A * A - (6 * s - 8) * (A * A) + 3 * s * (s - 2)

private theorem sum_chr_nonneg {n : Nat} (y : W n) : 0 ≤ total n (fun v => chr v y) := by
  have heq : (fun v => chr v y) = chr y := funext fun v => by simp only [chr, dot_comm n v y]
  rw [heq]
  have id := identity_spectrum n y
  change total n (chr y) = if y = zero n then many n else 0 at id
  rw [id]; split
  · exact Int.le_of_lt (many_pos n)
  · exact Int.le_refl 0

private theorem ind_sq (P : W n → Bool) (x : W n) : ind P x * ind P x = ind P x := by
  unfold ind; cases P x <;> decide

private theorem ind_ge0 {n : Nat} (P : W n → Bool) (x : W n) : 0 ≤ ind P x := by
  unfold ind; cases P x <;> decide

private theorem mul5_nonneg {a b c d e : Int}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ a * b * c * d * e :=
  Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg ha hb) hc) hd) he

private theorem total_of_nonneg {n : Nat} (F : W n → Int) (h : ∀ x, 0 ≤ F x) : 0 ≤ total n F := by
  rw [← total_zero n]; exact total_mono n _ _ h

private theorem kraw2_distinct {n : Nat} (P : W n → Bool) (v : W n) :
    kraw2 (cnt P) (transform (ind P) v) =
      total n (fun x1 => total n (fun x2 =>
        if x1 = x2 then (0 : Int) else ind P x1 * ind P x2 * chr v (add n x1 x2))) := by
  unfold kraw2 transform
  rw [rectangular]
  have hsplit (x1 : W n) :
      total n (fun x2 => ind P x1 * chr v x1 * (ind P x2 * chr v x2)) =
        ind P x1 + total n (fun x2 =>
          if x1 = x2 then (0 : Int) else ind P x1 * ind P x2 * chr v (add n x1 x2)) := by
    have hdiag : ind P x1 = total n (fun x2 =>
        if x1 = x2 then ind P x1 * ind P x2 * chr v (add n x1 x2) else 0) := by
      have hsel := select n x1 (fun x2 => ind P x1 * ind P x2 * chr v (add n x1 x2))
      have h0 : ind P x1 * ind P x1 * chr v (add n x1 x1) = ind P x1 := by
        rw [ind_sq, add_self]; simp [chr, dot_zero_right, sign]
      have hsel' : total n (fun x2 => hits x1 x2 * (ind P x1 * ind P x2 * chr v (add n x1 x2))) = ind P x1 :=
        hsel.trans h0
      refine hsel'.symm.trans ?_
      apply congrArg (total n); funext x2
      unfold hits; split <;> simp
    have hrhs : ind P x1 + total n (fun x2 =>
          if x1 = x2 then (0 : Int) else ind P x1 * ind P x2 * chr v (add n x1 x2)) =
        total n (fun x2 =>
          (if x1 = x2 then ind P x1 * ind P x2 * chr v (add n x1 x2) else 0) +
          (if x1 = x2 then (0 : Int) else ind P x1 * ind P x2 * chr v (add n x1 x2))) :=
      (congrArg (· + _) hdiag).trans (total_add n _ _).symm
    rw [hrhs]
    apply congrArg (total n); funext x2
    have hprod : ind P x1 * chr v x1 * (ind P x2 * chr v x2) =
        ind P x1 * ind P x2 * chr v (add n x1 x2) := by
      rw [chr_add]; ac_rfl
    rw [hprod]; split <;> simp
  rw [funext hsplit, total_add]
  unfold cnt; omega

private theorem kraw3_distinct {n : Nat} (P : W n → Bool) (v : W n) :
    kraw3 (cnt P) (transform (ind P) v) =
      total n (fun x1 => total n (fun x2 => total n (fun x3 =>
        if x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then (0 : Int)
        else ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 (add n x2 x3))))) := by
  let s := cnt P
  let A := transform (ind P) v
  have hmul : kraw2 s A * A =
      total n (fun x1 => total n (fun x2 => total n (fun x3 =>
        if x1 = x2 then (0 : Int)
        else ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 (add n x2 x3))))) := by
    rw [kraw2_distinct]
    rw [Int.mul_comm, ← total_scale]; apply congrArg (total n); funext x1
    rw [← total_scale]; apply congrArg (total n); funext x2
    rw [Int.mul_comm A]; unfold A transform
    rw [← total_scale]; apply congrArg (total n); funext x3
    split
    · simp
    · simp only [chr_add]; ac_rfl
  -- Split `x3 = x1`, `x3 = x2`, and `x3 ∉ {x1, x2}`
  have hdecomp (x1 x2 : W n) :
      total n (fun x3 => if x1 = x2 then (0 : Int)
        else ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 (add n x2 x3))) =
      (if x1 = x2 then 0 else ind P x1 * ind P x2 * chr v x2) +
      (if x1 = x2 then 0 else ind P x1 * ind P x2 * chr v x1) +
      total n (fun x3 => if x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then (0 : Int)
        else ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 (add n x2 x3))) := by
    if h12 : x1 = x2 then
      simp [h12, total_zero]
    else
      have hsel1 : ind P x1 * ind P x2 * chr v x2 =
          total n (fun x3 => if x1 = x3 then ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 (add n x2 x3)) else 0) := by
        have hs := select n x1 (fun x3 => ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 (add n x2 x3)))
        have hval : ind P x1 * ind P x2 * ind P x1 * chr v (add n x1 (add n x2 x1)) =
            ind P x1 * ind P x2 * chr v x2 := by
          have ha : add n x1 (add n x2 x1) = x2 := by
            rw [add_comm n x2 x1, ← Balanced242Plateau.add_assoc', add_self, add_zero_left]
          rw [ha, Int.mul_right_comm (ind P x1) (ind P x2) (ind P x1), ind_sq]
        have hs' := hs.trans hval
        rw [← hs']; apply congrArg (total n); funext x3; unfold hits; split <;> simp
      have hsel2 : ind P x1 * ind P x2 * chr v x1 =
          total n (fun x3 => if x2 = x3 then ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 (add n x2 x3)) else 0) := by
        have hs := select n x2 (fun x3 => ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 (add n x2 x3)))
        have hval : ind P x1 * ind P x2 * ind P x2 * chr v (add n x1 (add n x2 x2)) =
            ind P x1 * ind P x2 * chr v x1 := by
          rw [add_self, add_zero_right, Int.mul_assoc (ind P x1), ind_sq]
        have hs' := hs.trans hval
        rw [← hs']; apply congrArg (total n); funext x3; unfold hits; split <;> simp
      simp only [h12, if_false, false_or]
      rw [hsel1, hsel2, ← total_add, ← total_add]
      apply congrArg (total n); funext x3
      if h13 : x1 = x3 then
        have h23 : ¬ x2 = x3 := fun h => h12 (h13.trans h.symm)
        simp [h13, h23]
      else if h23 : x2 = x3 then
        simp [h13, h23]
      else
        simp [h13, h23]
  have hterm1 : total n (fun x1 => total n (fun x2 =>
      if x1 = x2 then (0 : Int) else ind P x1 * ind P x2 * chr v x2)) = (s - 1) * A := by
    rw [swap]
    have inner (x2 : W n) : total n (fun x1 => if x1 = x2 then (0 : Int) else ind P x1 * ind P x2 * chr v x2) =
        (s - 1) * (ind P x2 * chr v x2) := by
      have hs : total n (fun x1 => if x1 = x2 then (0 : Int) else ind P x1) = s - ind P x2 := by
        have hsel := select n x2 (ind P)
        have hpt (x1 : W n) : (if x1 = x2 then (0 : Int) else ind P x1) + hits x2 x1 * ind P x1 = ind P x1 := by
          unfold hits
          if h : x1 = x2 then subst h; simp else
            have h' : ¬ x2 = x1 := fun e => h e.symm
            simp [h, h']
        have hsum := congrArg (total n) (funext hpt)
        rw [total_add, hsel] at hsum; unfold s cnt; omega
      have hsc : total n (fun x1 => if x1 = x2 then (0 : Int) else ind P x1 * ind P x2 * chr v x2) =
          total n (fun x1 => if x1 = x2 then (0 : Int) else ind P x1) * (ind P x2 * chr v x2) := by
        rw [Int.mul_comm, ← total_scale]
        apply congrArg (total n); funext x1; split <;> simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      rw [hsc, hs]
      unfold ind; cases P x2 <;> simp
    rw [funext inner, total_scale]; rfl
  have hterm2 : total n (fun x1 => total n (fun x2 =>
      if x1 = x2 then (0 : Int) else ind P x1 * ind P x2 * chr v x1)) = (s - 1) * A := by
    rw [← hterm1, swap]
    apply congrArg (total n); funext x1; apply congrArg (total n); funext x2
    if h : x1 = x2 then subst h; simp else
      have h' : ¬ x2 = x1 := fun e => h e.symm
      simp [h, h', Int.mul_comm]
  have hfull : kraw2 s A * A = (s - 1) * A + (s - 1) * A +
      total n (fun x1 => total n (fun x2 => total n (fun x3 =>
        if x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then (0 : Int)
        else ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 (add n x2 x3))))) := by
    rw [hmul]
    simp only [hdecomp, total_add, hterm1, hterm2]
  have halg : kraw3 s A = kraw2 s A * A - ((s - 1) * A + (s - 1) * A) := by
    unfold kraw3 kraw2
    simp only [Int.sub_mul, Int.one_mul]
    have h3 : 3 * s * A = s * A + s * A + s * A := by
      have : 3 * s = s + s + s := by omega
      rw [this, Int.add_mul, Int.add_mul]
    have h2 : 2 * A = A + A := by omega
    rw [h3, h2]; omega
  rw [halg, hfull]; omega

private theorem kraw4_distinct {n : Nat} (P : W n → Bool) (v : W n) :
    kraw4 (cnt P) (transform (ind P) v) =
      total n (fun x1 => total n (fun x2 => total n (fun x3 => total n (fun x4 =>
        if x1 = x2 ∨ x1 = x3 ∨ x1 = x4 ∨ x2 = x3 ∨ x2 = x4 ∨ x3 = x4 then (0 : Int)
        else ind P x1 * ind P x2 * ind P x3 * ind P x4 *
             chr v (add n x1 (add n x2 (add n x3 x4))))))) := by
  let s := cnt P
  let A := transform (ind P) v
  have hmul : kraw3 s A * A =
      total n (fun x1 => total n (fun x2 => total n (fun x3 => total n (fun x4 =>
        if x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then (0 : Int)
        else ind P x1 * ind P x2 * ind P x3 * ind P x4 *
             chr v (add n x1 (add n x2 (add n x3 x4))))))) := by
    rw [kraw3_distinct]
    show (total n _) * total n (fun x4 => ind P x4 * chr v x4) = _
    rw [Int.mul_comm, ← total_scale]; apply congrArg (total n); funext x1
    rw [← total_scale]; apply congrArg (total n); funext x2
    rw [← total_scale]; apply congrArg (total n); funext x3
    rw [Int.mul_comm (total n _), ← total_scale]
    apply congrArg (total n); funext x4
    split
    · simp
    · simp only [chr_add]; ac_rfl
  -- Split `x4 ∈ {x1, x2, x3}` vs `x4 ∉ {x1, x2, x3}`
  have hdecomp (x1 x2 x3 : W n) :
      total n (fun x4 => if x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then (0 : Int)
        else ind P x1 * ind P x2 * ind P x3 * ind P x4 * chr v (add n x1 (add n x2 (add n x3 x4)))) =
      (if x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then 0 else ind P x1 * ind P x2 * ind P x3 * chr v (add n x2 x3)) +
      (if x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then 0 else ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 x3)) +
      (if x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then 0 else ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 x2)) +
      total n (fun x4 => if x1 = x2 ∨ x1 = x3 ∨ x1 = x4 ∨ x2 = x3 ∨ x2 = x4 ∨ x3 = x4 then (0 : Int)
        else ind P x1 * ind P x2 * ind P x3 * ind P x4 * chr v (add n x1 (add n x2 (add n x3 x4)))) := by
    if h123 : x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then
      have hbad (x4 : W n) : x1 = x2 ∨ x1 = x3 ∨ x1 = x4 ∨ x2 = x3 ∨ x2 = x4 ∨ x3 = x4 := by
        rcases h123 with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      simp [h123, hbad, total_zero]
    else
      have n12 : x1 ≠ x2 := fun h => h123 (Or.inl h)
      have n13 : x1 ≠ x3 := fun h => h123 (Or.inr (Or.inl h))
      have n23 : x2 ≠ x3 := fun h => h123 (Or.inr (Or.inr h))
      have hs1 : ind P x1 * ind P x2 * ind P x3 * chr v (add n x2 x3) =
          total n (fun x4 => if x1 = x4 then ind P x1 * ind P x2 * ind P x3 * ind P x4 *
            chr v (add n x1 (add n x2 (add n x3 x4))) else 0) := by
        have hs := select n x1 (fun x4 => ind P x1 * ind P x2 * ind P x3 * ind P x4 *
            chr v (add n x1 (add n x2 (add n x3 x4))))
        have ha : add n x1 (add n x2 (add n x3 x1)) = add n x2 x3 := by
          rw [add_comm n x3 x1, ← Balanced242Plateau.add_assoc' n x2 x1 x3, add_comm n x2 x1,
              Balanced242Plateau.add_assoc' n x1 x2 x3,
              ← Balanced242Plateau.add_assoc' n x1 x1, add_self, add_zero_left]
        have hv : ind P x1 * ind P x2 * ind P x3 * ind P x1 * chr v (add n x1 (add n x2 (add n x3 x1))) =
            ind P x1 * ind P x2 * ind P x3 * chr v (add n x2 x3) := by
          rw [ha]
          have : ind P x1 * ind P x2 * ind P x3 * ind P x1 = (ind P x1 * ind P x1) * ind P x2 * ind P x3 := by ac_rfl
          rw [this, ind_sq]
        rw [hv] at hs; rw [← hs]; apply congrArg (total n); funext x4; unfold hits; split <;> simp
      have hs2 : ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 x3) =
          total n (fun x4 => if x2 = x4 then ind P x1 * ind P x2 * ind P x3 * ind P x4 *
            chr v (add n x1 (add n x2 (add n x3 x4))) else 0) := by
        have hs := select n x2 (fun x4 => ind P x1 * ind P x2 * ind P x3 * ind P x4 *
            chr v (add n x1 (add n x2 (add n x3 x4))))
        have ha : add n x1 (add n x2 (add n x3 x2)) = add n x1 x3 := by
          rw [add_comm n x3 x2, ← Balanced242Plateau.add_assoc' n x2 x2 x3, add_self, add_zero_left]
        have hv : ind P x1 * ind P x2 * ind P x3 * ind P x2 * chr v (add n x1 (add n x2 (add n x3 x2))) =
            ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 x3) := by
          rw [ha]
          have : ind P x1 * ind P x2 * ind P x3 * ind P x2 = ind P x1 * (ind P x2 * ind P x2) * ind P x3 := by ac_rfl
          rw [this, ind_sq]
        rw [hv] at hs; rw [← hs]; apply congrArg (total n); funext x4; unfold hits; split <;> simp
      have hs3 : ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 x2) =
          total n (fun x4 => if x3 = x4 then ind P x1 * ind P x2 * ind P x3 * ind P x4 *
            chr v (add n x1 (add n x2 (add n x3 x4))) else 0) := by
        have hs := select n x3 (fun x4 => ind P x1 * ind P x2 * ind P x3 * ind P x4 *
            chr v (add n x1 (add n x2 (add n x3 x4))))
        have ha : add n x1 (add n x2 (add n x3 x3)) = add n x1 x2 := by
          rw [add_self, add_zero_right]
        have hv : ind P x1 * ind P x2 * ind P x3 * ind P x3 * chr v (add n x1 (add n x2 (add n x3 x3))) =
            ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 x2) := by
          rw [ha, Int.mul_assoc (ind P x1 * ind P x2), ind_sq]
        rw [hv] at hs; rw [← hs]; apply congrArg (total n); funext x4; unfold hits; split <;> simp
      simp only [h123, if_false]
      rw [hs1, hs2, hs3, ← total_add, ← total_add, ← total_add]
      apply congrArg (total n); funext x4
      if h14 : x1 = x4 then
        have h24 : ¬ x2 = x4 := fun h => n12 (h14.trans h.symm)
        have h34 : ¬ x3 = x4 := fun h => n13 (h14.trans h.symm)
        simp [n12, n13, n23, h14, h24, h34]
      else if h24 : x2 = x4 then
        have h34 : ¬ x3 = x4 := fun h => n23 (h24.trans h.symm)
        simp [n12, n13, n23, h14, h24, h34]
      else if h34 : x3 = x4 then
        simp [n12, n13, n23, h14, h24, h34]
      else
        simp [n12, n13, n23, h14, h24, h34]
  -- Each of the three collision sums equals `(s - 2) * kraw2 s A`
  have hcol3 : total n (fun x1 => total n (fun x2 => total n (fun x3 =>
      if x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then (0 : Int)
      else ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 x2)))) = (s - 2) * kraw2 s A := by
    rw [kraw2_distinct, ← total_scale]
    apply congrArg (total n); funext x1
    rw [← total_scale]; apply congrArg (total n); funext x2
    if h12 : x1 = x2 then
      simp [h12, total_zero]
    else
      simp only [h12, if_false, false_or]
      have hcnt : total n (fun x3 => if x1 = x3 ∨ x2 = x3 then (0 : Int) else ind P x3) =
          s - ind P x1 - ind P x2 := by
        have hs1 := select n x1 (ind P)
        have hs2 := select n x2 (ind P)
        have hpt (x3 : W n) :
            (if x1 = x3 ∨ x2 = x3 then (0 : Int) else ind P x3) +
            hits x1 x3 * ind P x3 + hits x2 x3 * ind P x3 = ind P x3 := by
          unfold hits
          if h13 : x1 = x3 then
            have h23 : ¬ x2 = x3 := fun h => h12 (h13.trans h.symm)
            simp [h13, h23]
          else if h23 : x2 = x3 then
            simp [h13, h23]
          else
            simp [h13, h23]
        have hsum := congrArg (total n) (funext hpt)
        rw [total_add, total_add, hs1, hs2] at hsum; unfold s cnt; omega
      have hsc : total n (fun x3 => if x1 = x3 ∨ x2 = x3 then (0 : Int)
          else ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 x2)) =
          total n (fun x3 => if x1 = x3 ∨ x2 = x3 then (0 : Int) else ind P x3) *
          (ind P x1 * ind P x2 * chr v (add n x1 x2)) := by
        rw [Int.mul_comm (total n _), ← total_scale]; apply congrArg (total n); funext x3
        split
        · simp
        · ac_rfl
      rw [hsc, hcnt]
      have h2 : s - 1 - 1 = s - 2 := by omega
      unfold ind; cases P x1 <;> cases P x2 <;> simp [h2]
  have hcol2 : total n (fun x1 => total n (fun x2 => total n (fun x3 =>
      if x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then (0 : Int)
      else ind P x1 * ind P x2 * ind P x3 * chr v (add n x1 x3)))) = (s - 2) * kraw2 s A := by
    rw [← hcol3]
    apply congrArg (total n); funext x1; rw [swap]
    apply congrArg (total n); funext x2; apply congrArg (total n); funext x3
    have heq : (x1 = x3 ∨ x1 = x2 ∨ x3 = x2) ↔ (x1 = x2 ∨ x1 = x3 ∨ x2 = x3) := by
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h.symm)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h.symm)
    if h : x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then
      have h' : x1 = x3 ∨ x1 = x2 ∨ x3 = x2 := heq.mpr h
      simp [h, h']
    else
      have h' : ¬ (x1 = x3 ∨ x1 = x2 ∨ x3 = x2) := fun hc => h (heq.mp hc)
      simp only [h, h', if_false]; ac_rfl
  have hcol1 : total n (fun x1 => total n (fun x2 => total n (fun x3 =>
      if x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then (0 : Int)
      else ind P x1 * ind P x2 * ind P x3 * chr v (add n x2 x3)))) = (s - 2) * kraw2 s A := by
    rw [← hcol2, swap]
    apply congrArg (total n); funext x1; apply congrArg (total n); funext x2; apply congrArg (total n); funext x3
    have heq : (x2 = x1 ∨ x2 = x3 ∨ x1 = x3) ↔ (x1 = x2 ∨ x1 = x3 ∨ x2 = x3) := by
      constructor
      · rintro (h | h | h)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      · rintro (h | h | h)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
    if h : x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then
      have h' : x2 = x1 ∨ x2 = x3 ∨ x1 = x3 := heq.mpr h
      simp [h, h']
    else
      have h' : ¬ (x2 = x1 ∨ x2 = x3 ∨ x1 = x3) := fun hc => h (heq.mp hc)
      simp only [h, h', if_false]; ac_rfl
  have hfull : kraw3 s A * A = (s - 2) * kraw2 s A + (s - 2) * kraw2 s A + (s - 2) * kraw2 s A +
      total n (fun x1 => total n (fun x2 => total n (fun x3 => total n (fun x4 =>
        if x1 = x2 ∨ x1 = x3 ∨ x1 = x4 ∨ x2 = x3 ∨ x2 = x4 ∨ x3 = x4 then (0 : Int)
        else ind P x1 * ind P x2 * ind P x3 * ind P x4 *
             chr v (add n x1 (add n x2 (add n x3 x4))))))) := by
    rw [hmul]
    simp only [hdecomp, total_add, hcol1, hcol2, hcol3]
  have halg : kraw4 s A = kraw3 s A * A - 3 * ((s - 2) * kraw2 s A) := by
    unfold kraw4 kraw3 kraw2
    have e1 : (A * A * A - (3 * s - 2) * A) * A = A * A * A * A - (3 * s - 2) * (A * A) := by
      rw [Int.sub_mul, Int.mul_assoc (3 * s - 2) A A]
    have e2 : 3 * ((s - 2) * (A * A - s)) = (3 * s - 6) * (A * A) - 3 * s * (s - 2) := by
      rw [Int.mul_sub, Int.mul_sub, ← Int.mul_assoc 3, Int.mul_sub 3 s 2]
      have h32 : (3 : Int) * 2 = 6 := rfl
      have h3s : 3 * ((s - 2) * s) = 3 * s * (s - 2) := by ac_rfl
      rw [h32, h3s]
    have e3 : (3 * s - 2) * (A * A) + (3 * s - 6) * (A * A) = (6 * s - 8) * (A * A) := by
      rw [← Int.add_mul]; congr 1; omega
    rw [e1, e2]; omega
  rw [halg, hfull]; omega

private theorem kraw_at_zero (s : Int) :
    kraw1 s = s ∧
    kraw2 s s = s * (s - 1) ∧
    kraw3 s s = s * (s - 1) * (s - 2) ∧
    kraw4 s s = s * (s - 1) * (s - 2) * (s - 3) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · unfold kraw2; rw [Int.mul_sub, Int.mul_one]
  · unfold kraw3
    have e1 : s * (s - 1) * (s - 2) = s * s * s - 3 * s * s + 2 * s := by
      simp only [Int.mul_sub, Int.sub_mul, Int.mul_one]
      have a1 : s * s * 2 = 2 * s * s := by ac_rfl
      have a2 : s * 2 = 2 * s := by ac_rfl
      have a3 : 3 * s * s = s * s + 2 * s * s := by
        have : 3 * s = s + 2 * s := by omega
        rw [this, Int.add_mul]
      rw [a1, a2, a3]; omega
    have e2 : (3 * s - 2) * s = 3 * s * s - 2 * s := by rw [Int.sub_mul]
    rw [e1, e2]; omega
  · unfold kraw4
    have e1 : s * (s - 1) * (s - 2) * (s - 3) =
        s * s * s * s - 6 * s * s * s + 11 * s * s - 6 * s := by
      have h3 : s * (s - 1) * (s - 2) = s * s * s - 3 * s * s + 2 * s := by
        simp only [Int.mul_sub, Int.sub_mul, Int.mul_one]
        have a1 : s * s * 2 = 2 * s * s := by ac_rfl
        have a2 : s * 2 = 2 * s := by ac_rfl
        have a3 : 3 * s * s = s * s + 2 * s * s := by
          have : 3 * s = s + 2 * s := by omega
          rw [this, Int.add_mul]
        rw [a1, a2, a3]; omega
      rw [h3, Int.mul_sub, Int.add_mul, Int.sub_mul, Int.add_mul, Int.sub_mul]
      have c1 : s * s * s * 3 = 3 * s * s * s := by ac_rfl
      have c2 : 3 * s * s * s = 3 * s * s * s := rfl
      have c3 : 3 * s * s * 3 = 9 * s * s := by
        have : 3 * s * s * 3 = (3 * 3) * s * s := by ac_rfl
        rw [this]; rfl
      have c4 : 2 * s * s = 2 * s * s := rfl
      have c5 : 2 * s * 3 = 6 * s := by rw [Int.mul_assoc 2 s 3, Int.mul_comm s 3, ← Int.mul_assoc]; rfl
      have c6 : 6 * s * s * s = 3 * s * s * s + 3 * s * s * s := by
        have : 6 * s = 3 * s + 3 * s := by omega
        rw [this, Int.add_mul, Int.add_mul]
      have c7 : 11 * s * s = 2 * s * s + 9 * s * s := by
        have : 11 * s = 2 * s + 9 * s := by omega
        rw [this, Int.add_mul]
      rw [c1, c3, c5, c6, c7]; omega
    have e2 : (6 * s - 8) * (s * s) = 6 * s * s * s - 8 * s * s := by
      rw [Int.sub_mul, ← Int.mul_assoc (6 * s) s s, ← Int.mul_assoc 8 s s]
    have e3 : 3 * s * (s - 2) = 3 * s * s - 6 * s := by
      rw [Int.mul_sub]
      have : 3 * s * 2 = 6 * s := by rw [Int.mul_assoc 3 s 2, Int.mul_comm s 2, ← Int.mul_assoc]; rfl
      rw [this]
    have e4 : 11 * s * s = 8 * s * s + 3 * s * s := by
      have : 11 * s = 8 * s + 3 * s := by omega
      rw [this, Int.add_mul]
    rw [e1, e2, e3, e4]; omega

/-- Degree-2 Krawtchouk equality (type `(2, 0, 0)`): `∑_{v ≠ 0} (A_v² - s) = -s(s - 1)`. -/
theorem kraw_deg2_200 {n : Nat} (P : W n → Bool) :
    total n (fun v => nz v * kraw2 (cnt P) (transform (ind P) v)) = -(cnt P * (cnt P - 1)) := by
  rw [nz_total, transform_ind_zero, (kraw_at_zero (cnt P)).2.1]
  have hsum : total n (fun v => kraw2 (cnt P) (transform (ind P) v)) = 0 := by
    unfold kraw2
    rw [total_sub, parseval2, total_const]
    have hsq : total n (fun x => ind P x * ind P x) = cnt P := by
      unfold cnt; apply congrArg (total n); funext x; exact ind_sq P x
    rw [hsq, Int.mul_comm (many n) (cnt P)]; omega
  rw [hsum]; omega

/-- Degree-2 Krawtchouk equality (type `(1, 1, 0)`): `∑_{v ≠ 0} A_v B_v = -s_P s_Q`. -/
theorem kraw_deg2_110 {n : Nat} (P Q : W n → Bool) (hPQ : ∀ x, (P x && Q x) = false) :
    total n (fun v => nz v * (kraw1 (transform (ind P) v) * kraw1 (transform (ind Q) v))) =
      -(cnt P * cnt Q) := by
  rw [nz_total, transform_ind_zero, transform_ind_zero]
  unfold kraw1
  rw [parseval2]
  have h0 (x : W n) : ind P x * ind Q x = 0 := by
    have := hPQ x; unfold ind; cases hp : P x <;> cases hq : Q x <;> simp [hp, hq] at this ⊢
  rw [funext h0, total_zero, Int.mul_zero]; omega

/-- Degree-4 Krawtchouk inequality (type `(4, 0, 0)`): `∑_{v ≠ 0} kraw4(s, A_v) ≥ -s(s-1)(s-2)(s-3)`. -/
theorem kraw_deg4_400 {n : Nat} (P : W n → Bool) :
    -(cnt P * (cnt P - 1) * (cnt P - 2) * (cnt P - 3)) ≤
      total n (fun v => nz v * kraw4 (cnt P) (transform (ind P) v)) := by
  rw [nz_total, transform_ind_zero, (kraw_at_zero (cnt P)).2.2.2]
  have hnn : 0 ≤ total n (fun v => kraw4 (cnt P) (transform (ind P) v)) := by
    simp only [kraw4_distinct]
    rw [swap]; apply total_of_nonneg; intro x1
    rw [swap]; apply total_of_nonneg; intro x2
    rw [swap]; apply total_of_nonneg; intro x3
    rw [swap]; apply total_of_nonneg; intro x4
    if h : x1 = x2 ∨ x1 = x3 ∨ x1 = x4 ∨ x2 = x3 ∨ x2 = x4 ∨ x3 = x4 then
      simp [h, total_zero]
    else
      simp only [h, if_false, total_scale]
      exact mul5_nonneg (ind_ge0 P x1) (ind_ge0 P x2) (ind_ge0 P x3) (ind_ge0 P x4) (sum_chr_nonneg _)
  omega

/-- Degree-4 Krawtchouk inequality (type `(3, 1, 0)`): `∑_{v ≠ 0} kraw3(sP, A_v) B_v ≥ -sP(sP-1)(sP-2)sQ`. -/
theorem kraw_deg4_310 {n : Nat} (P Q : W n → Bool) :
    -(cnt P * (cnt P - 1) * (cnt P - 2) * cnt Q) ≤
      total n (fun v => nz v * (kraw3 (cnt P) (transform (ind P) v) * kraw1 (transform (ind Q) v))) := by
  rw [nz_total, transform_ind_zero, transform_ind_zero, (kraw_at_zero (cnt P)).2.2.1]
  unfold kraw1
  have hnn : 0 ≤ total n (fun v => kraw3 (cnt P) (transform (ind P) v) * transform (ind Q) v) := by
    have hexp (v : W n) : kraw3 (cnt P) (transform (ind P) v) * transform (ind Q) v =
        total n (fun x1 => total n (fun x2 => total n (fun x3 => total n (fun y =>
          if x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then (0 : Int)
          else ind P x1 * ind P x2 * ind P x3 * ind Q y * chr v (add n x1 (add n x2 (add n x3 y))))))) := by
      rw [kraw3_distinct]
      show (total n _) * total n (fun y => ind Q y * chr v y) = _
      rw [Int.mul_comm, ← total_scale]; apply congrArg (total n); funext x1
      rw [← total_scale]; apply congrArg (total n); funext x2
      rw [← total_scale]; apply congrArg (total n); funext x3
      rw [Int.mul_comm (total n _), ← total_scale]; apply congrArg (total n); funext y
      split
      · simp
      · simp only [chr_add]; ac_rfl
    rw [funext hexp]
    rw [swap]; apply total_of_nonneg; intro x1
    rw [swap]; apply total_of_nonneg; intro x2
    rw [swap]; apply total_of_nonneg; intro x3
    rw [swap]; apply total_of_nonneg; intro y
    if h : x1 = x2 ∨ x1 = x3 ∨ x2 = x3 then
      simp [h, total_zero]
    else
      simp only [h, if_false, total_scale]
      exact mul5_nonneg (ind_ge0 P x1) (ind_ge0 P x2) (ind_ge0 P x3) (ind_ge0 Q y) (sum_chr_nonneg _)
  omega

/-- Degree-4 Krawtchouk inequality (type `(2, 2, 0)`): `∑_{v ≠ 0} kraw2(sP, A_v) kraw2(sQ, B_v) ≥ -sP(sP-1)sQ(sQ-1)`. -/
theorem kraw_deg4_220 {n : Nat} (P Q : W n → Bool) :
    -(cnt P * (cnt P - 1) * (cnt Q * (cnt Q - 1))) ≤
      total n (fun v => nz v * (kraw2 (cnt P) (transform (ind P) v) * kraw2 (cnt Q) (transform (ind Q) v))) := by
  rw [nz_total, transform_ind_zero, transform_ind_zero,
      (kraw_at_zero (cnt P)).2.1, (kraw_at_zero (cnt Q)).2.1]
  have hnn : 0 ≤ total n (fun v => kraw2 (cnt P) (transform (ind P) v) * kraw2 (cnt Q) (transform (ind Q) v)) := by
    have hexp (v : W n) : kraw2 (cnt P) (transform (ind P) v) * kraw2 (cnt Q) (transform (ind Q) v) =
        total n (fun x1 => total n (fun x2 => total n (fun y1 => total n (fun y2 =>
          if x1 = x2 ∨ y1 = y2 then (0 : Int)
          else ind P x1 * ind P x2 * ind Q y1 * ind Q y2 * chr v (add n (add n x1 x2) (add n y1 y2)))))) := by
      rw [kraw2_distinct, kraw2_distinct]
      rw [Int.mul_comm, ← total_scale]; apply congrArg (total n); funext x1
      rw [← total_scale]; apply congrArg (total n); funext x2
      rw [Int.mul_comm (total n _), ← total_scale]; apply congrArg (total n); funext y1
      rw [← total_scale]; apply congrArg (total n); funext y2
      if hx : x1 = x2 then simp [hx]
      else if hy : y1 = y2 then simp [hx, hy]
      else simp only [hx, hy, or_self, if_false]; simp only [chr_add]; ac_rfl
    rw [funext hexp]
    rw [swap]; apply total_of_nonneg; intro x1
    rw [swap]; apply total_of_nonneg; intro x2
    rw [swap]; apply total_of_nonneg; intro y1
    rw [swap]; apply total_of_nonneg; intro y2
    if h : x1 = x2 ∨ y1 = y2 then
      simp [h, total_zero]
    else
      simp only [h, if_false, total_scale]
      exact mul5_nonneg (ind_ge0 P x1) (ind_ge0 P x2) (ind_ge0 Q y1) (ind_ge0 Q y2) (sum_chr_nonneg _)
  omega

/-- Degree-4 Krawtchouk inequality (type `(2, 1, 1)`): `∑_{v ≠ 0} kraw2(sP, A_v) B_v C_v ≥ -sP(sP-1)sQ sR`. -/
theorem kraw_deg4_211 {n : Nat} (P Q R : W n → Bool) :
    -(cnt P * (cnt P - 1) * cnt Q * cnt R) ≤
      total n (fun v => nz v * (kraw2 (cnt P) (transform (ind P) v) *
        kraw1 (transform (ind Q) v) * kraw1 (transform (ind R) v))) := by
  rw [nz_total, transform_ind_zero, transform_ind_zero, transform_ind_zero,
      (kraw_at_zero (cnt P)).2.1]
  unfold kraw1
  have hnn : 0 ≤ total n (fun v => kraw2 (cnt P) (transform (ind P) v) *
      transform (ind Q) v * transform (ind R) v) := by
    have hexp (v : W n) : kraw2 (cnt P) (transform (ind P) v) * transform (ind Q) v * transform (ind R) v =
        total n (fun x1 => total n (fun x2 => total n (fun y => total n (fun z =>
          if x1 = x2 then (0 : Int)
          else ind P x1 * ind P x2 * ind Q y * ind R z * chr v (add n (add n x1 x2) (add n y z)))))) := by
      rw [kraw2_distinct]
      show (total n _) * total n (fun y => ind Q y * chr v y) * total n (fun z => ind R z * chr v z) = _
      have hsub (c : Int) (F G : W n → Int) :
          (total n F * total n G) * c = total n (fun y => total n (fun z => c * F y * G z)) := by
        rw [rectangular, Int.mul_comm, ← total_scale]
        apply congrArg (total n); funext y
        rw [← total_scale]; apply congrArg (total n); funext z; ac_rfl
      rw [Int.mul_assoc, Int.mul_comm (total n _), ← total_scale]
      apply congrArg (total n); funext x1
      rw [← total_scale]; apply congrArg (total n); funext x2
      rw [hsub]; apply congrArg (total n); funext y; apply congrArg (total n); funext z
      split
      · simp
      · simp only [chr_add]; ac_rfl
    rw [funext hexp]
    rw [swap]; apply total_of_nonneg; intro x1
    rw [swap]; apply total_of_nonneg; intro x2
    rw [swap]; apply total_of_nonneg; intro y
    rw [swap]; apply total_of_nonneg; intro z
    if h : x1 = x2 then
      simp [h, total_zero]
    else
      simp only [h, if_false, total_scale]
      exact mul5_nonneg (ind_ge0 P x1) (ind_ge0 P x2) (ind_ge0 Q y) (ind_ge0 R z) (sum_chr_nonneg _)
  omega

end Balanced242AnchorPair

#print axioms Balanced242AnchorPair.sec_ell_eq
#print axioms Balanced242AnchorPair.anchor_pair_ranks_63_64
#print axioms Balanced242AnchorPair.six_section_energy
#print axioms Balanced242AnchorPair.six_section_div4
#print axioms Balanced242AnchorPair.six_section_jensen
#print axioms Balanced242AnchorPair.kraw_deg2_200
#print axioms Balanced242AnchorPair.kraw_deg2_110
#print axioms Balanced242AnchorPair.kraw_deg4_400
#print axioms Balanced242AnchorPair.kraw_deg4_310
#print axioms Balanced242AnchorPair.kraw_deg4_220
#print axioms Balanced242AnchorPair.kraw_deg4_211
