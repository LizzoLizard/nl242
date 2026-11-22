/-
  Balanced242T112.lean — Complete, unconditional, LP-free, covering-radius-free zero-Mathlib
  Lean 4 exclusion of `t = 112` (`agreements f g ≠ 112`)!

  Zero Mathlib, zero `sorry`, zero `native_decide`, zero `SectionEnum`, zero `CoveringRadius244`,
  zero LP / Farkas certificates, zero matrices!

  Proof overview:
    1. `Balanced242Z64Switch.t112_forces_rank4_Z96`: `t = 112` unconditionally forces rank 4
       (`rr (β8 f g) = 16`, `Zc f g = 96`) and low-block budget `n0 + 2 * n8 = 8`.
    2. **Rank-4 `Z = 96` Zero-Set Theorem** (`rank4_Z96_n0_ge8`, `rank4_Z96_n0_eq8_subspace`):
       For ANY even `t` with rank 4 (`rr = 16`) and `Zc = 96`, `transform (1_Z) u ∈ {0, ±32, 96}`
       so `low_autocorr_mod32` gives `8 ∣ transform Dlo u` for all `u : W 8`, hence `4 ∣ w u`,
       forcing every first and second incidence count `c(u)`, `c2(u, v)` of `Z0 = {lo = 0}` to be
       EVEN. Elementary counting eliminates `n0 ∈ {2, 4, 6}` unconditionally (reusable at `t = 110`!)
       and at `n0 = 8` forces `∀ u, c(u) ∈ {0, 4}`, proving `Z0` is a linear 3-subspace of `W 8`!
       At `t = 112` (`n0 + 2 * n8 = 8`), this INSTANTLY forces `n0 = 8, n8 = 0`!
    3. **Symplectic Reduction to Canonical `W 4` Quadric `SZ`** (`isSZ c := !((c0 || c1) ^^ (c2 && c3))`):
       Extracts 4 symplectic vectors `u1, v1, u2, v2 : W 8` and their `readMask` duals `d0, d1, d2, d3`
       spanning `rad(β8)^⊥`, plus a basis `r0, r1, r2, r3` of the 16-element radical `rad(β8)`.
       Because NO two nonzero points of `SZ` sum into `SZ`, the linear 3-subspace `Z0` meets `SZ`
       in at most 2 cosets (`|Z0 ∩ R| ∈ {4, 8}`), so EVERY `s ∈ SZ` has `tot[s] ∈ {32, 48, 64}`
       (`16 ∣ tot[s]`), and at least **4** cosets `s ∈ SZ` have `tot[s] = 64` (zero-free!).
    4. **729-Cell Kernel Table on `W 4`** (`cell4_props`):
       Every 16-point cell `v_y ∈ {-1, 0, 1}^16` satisfies `3 ∣ transform v_y c` for all `c ∈ SZc`,
       so it is determined by its 6 residues mod 3 on `SZ` (`3^6 = 729` cells, kernel-verified!).
       This immediately forces `r = 0` (all 16 cells even) and `k ∈ {0, 2, 3, 6}` where `k = #{m=12}`.
    5. **Pure-Algebra Exclusions of ALL Four Cases `k ∈ {0, 2, 3, 6}` (ZERO enumeration!)**:
       * `k = 3`: mod-16 divisibility forces `≤ 6 * 4 = 24 < 28` hits of `4` on `SZ`.
       * `k = 2`: the single `m = 8` cell saturates 2 cosets `{s1, s2} ⊂ SZ` (`64`), forcing all 8
         `m = 10` cells to vanish on `{s1, s2}` and collide at `pickC s1 s2 ∈ SZc` (`8*36 = 288 > 144`).
       * `k = 6`: mod-16 forces all 4 `m = 10` cells to share the same 4 active cosets in `SZ`;
         a zero-free one has `g = gA + 2 gT` (`|A| = 4, |T| = 3`) with `|W_4(g)| = 4`, contradicting
         the 3-line cubic identity `3 W_4(gA) = 7 u - u^3 = -6 ε1 ε2 ε3 χ_{t1⊕t2⊕t3}` (`|gA| = 2 > 1`)!
       * `k = 0`: two `m = 6` cells (`y1 ≠ y2, d = y1 ⊕ y2`) plus ten `m = 10` cells (`X_10`).
         Parseval forces every zero-free `s ∈ SZ` (at least 4 of them) to have `supp_s` closed under
         `⊕ d`, hence `X_10` is 5 `d`-pairs and each `P_s = X_10 \ supp_s` is one `d`-pair; the
         4-pair Walsh square identity `0 = 96` forces the 4-pair XOR to lie in `{0, d}`, so any
         two distinct `P_s ≠ P_{s'}` (forced since each cell has only 2 zeros in `SZ`) give `P_s = P_{s'}`!

  Main exported theorems:
    * `rank4_Z96_n0_ge8`: at rank 4, `Zc = 96` (any even `t`), `8 ≤ n0 f g` (`n0 ∉ {2, 4, 6}`).
    * `rank4_Z96_n0_eq8_subspace`: when additionally `n0 f g = 8`, `Z0 = {lo = 0}` is a linear
      3-subspace of `W 8` (`∀ a b, lo a = 0 → lo b = 0 → lo (a ⊕ b) = 0`).
    * `no_t112`: complete, unconditional exclusion of `t = 112`!
-/
import Balanced242Z64Switch

namespace Balanced242T112

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Hyperplane Balanced242Reduction
open Balanced242Plateau Balanced242Rank Balanced242Global Balanced242RankCond
open Balanced242SectionFacts Balanced242QuarticHighBlock Balanced242LowBlock
open Balanced242Z64Switch

local notation "bind" => Balanced242Plateau.ind

/-! ## Section 1: Universal Rank-4 `Z = 96` Zero-Set Theorem (Zero Matrices!) -/

private theorem exists_dot_true {n : Nat} (u : W n) (hu : u ≠ zero n) :
    ∃ w : W n, dot n w u = true := by
  induction n with
  | zero => exact absurd rfl hu
  | succ m ih =>
    rcases u with ⟨b, r⟩
    cases b
    · have hr : r ≠ zero m := fun h => hu (by rw [h]; rfl)
      obtain ⟨w, hw⟩ := ih r hr
      exact ⟨(false, w), by simp [dot, hw]⟩
    · exact ⟨(true, zero m), by simp [dot, dot_zero]⟩

private theorem add_cancel_left {n : Nat} (a b c : W n) (h : add n a b = add n a c) : b = c := by
  have h1 := congrArg (add n a) h
  rw [← Balanced242Plateau.add_assoc', ← Balanced242Plateau.add_assoc', add_self,
      add_zero_left, add_zero_left] at h1
  exact h1

/-- Every rank-4 `Zc = 96` table (at ANY even `t`) has `8 ∣ transform Dlo u` for all `u`,
    so `c(u) = #{a ∈ Z0 : u·a = 1}` and `c2(u, v) = #{a ∈ Z0 : u·a = 1 ∧ v·a = 1}` are EVEN! -/
theorem rank4_Z96_zero_moments (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (ht_even : agreements f g % 2 = 0)
    (hrr : rr (β8 f g) = 16) (_hZc : Zc f g = 96) :
    (∀ u : W 8, transform (Dlo f g) u % 8 = 0) ∧
    (n0 f g % 2 = 0) ∧
    (∀ u : W 8, total 8 (fun a => (if lo f g a = 0 then (1 : Int) else 0) * bind (dot 8 u a)) % 2 = 0) ∧
    (∀ u v : W 8, total 8 (fun a => (if lo f g a = 0 then (1 : Int) else 0) * bind (dot 8 u a && dot 8 v a)) % 2 = 0) := by
  have hm8 : many 8 = 256 := by decide
  have hMM : 64 * 64 = many 8 * rr (β8 f g) := by rw [hm8, hrr]; decide
  have htrZ_div32 (u : W 8) : transform (fun a => bind (Zset f g a)) u % 32 = 0 := by
    have htrZ := transform_Zset_eq f g res dc lores u
    have hv := Balanced242Rank.spec_values (β8 f g) (cube8 f g res) 64 hMM (add 8 u (supportXor g))
    have hq : transform (q8 f g) (add 8 u (supportXor g)) = 0 ∨
        transform (q8 f g) (add 8 u (supportXor g)) = 64 ∨
        transform (q8 f g) (add 8 u (supportXor g)) = -64 := by
      cases hg : good (β8 f g) (add 8 u (supportXor g))
      · left; exact hv.2 hg
      · right; exact hv.1 hg
    have hq0 : q8 f g (zero 8) = 1 ∨ q8 f g (zero 8) = -1 := sign_vals _
    have hh : hits (zero 8) u = 0 ∨ hits (zero 8) u = 1 := by unfold hits; split <;> omega
    rcases hq0 with h0 | h0 <;> rcases hq with h1 | h1 | h1 <;> rcases hh with h2 | h2 <;>
      rw [h0, h1, h2] at htrZ <;> omega
  have htrD_div8 (u : W 8) : transform (Dlo f g) u % 8 = 0 := by
    have hmod := low_autocorr_mod32 f g ht_even lores locap u
    have h32 := htrZ_div32 u
    omega
  have htotD_div8 : total 8 (Dlo f g) % 8 = 0 := by
    have h0 := htrD_div8 (zero 8)
    have heq : transform (Dlo f g) (zero 8) = total 8 (Dlo f g) := by
      unfold transform; apply congrArg (total 8); funext a; unfold chr; rw [dot_zero]; simp [sign]
    rw [heq] at h0; exact h0
  have hn0_even : n0 f g % 2 = 0 := by rw [total_Dlo_eq] at htotD_div8; omega
  let w (u : W 8) : Int := total 8 (fun a => Dlo f g a * bind (dot 8 u a))
  have hw_div4 (u : W 8) : w u % 4 = 0 := by
    have h2w : 2 * w u = total 8 (Dlo f g) - transform (Dlo f g) u := by
      dsimp only [w]; unfold transform; rw [← total_scale, ← total_sub]
      apply congrArg (total 8); funext a
      unfold chr Balanced242Plateau.ind; cases dot 8 u a <;> simp [sign] <;> omega
    have h0 := htotD_div8; have hu := htrD_div8 u; omega
  let c (u : W 8) : Int := total 8 (fun a => (if lo f g a = 0 then (1 : Int) else 0) * bind (dot 8 u a))
  let m (u : W 8) : Int := total 8 (fun a => (if (lo f g a).natAbs = 8 then (1 : Int) else 0) * bind (dot 8 u a))
  have hw_split (u : W 8) : w u = c u + 2 * m u := by
    dsimp only [w, c, m]; rw [← total_scale, ← total_add]
    apply congrArg (total 8); funext a; unfold Dlo
    by_cases h0 : lo f g a = 0
    · rw [h0]; simp
    · by_cases h8 : (lo f g a).natAbs = 8 <;> simp [h0, h8]
  have hc_even (u : W 8) : c u % 2 = 0 := by
    have := hw_div4 u; have := hw_split u; omega
  have hc2_even (u v : W 8) :
      total 8 (fun a => (if lo f g a = 0 then (1 : Int) else 0) * bind (dot 8 u a && dot 8 v a)) % 2 = 0 := by
    have hdiff : w u + w v - w (add 8 u v) =
        2 * total 8 (fun a => (if lo f g a = 0 then (1 : Int) else 0) * bind (dot 8 u a && dot 8 v a)) +
        4 * total 8 (fun a => (if (lo f g a).natAbs = 8 then (1 : Int) else 0) * bind (dot 8 u a && dot 8 v a)) := by
      dsimp only [w]; rw [← total_add, ← total_sub, ← total_scale, ← total_scale, ← total_add]
      apply congrArg (total 8); funext a
      rw [dot_comm 8 (add 8 u v) a, dot_right, dot_comm 8 a u, dot_comm 8 a v]
      unfold Dlo
      by_cases h0 : lo f g a = 0
      · rw [h0]; simp only [if_true, Int.one_mul]; cases dot 8 u a <;> cases dot 8 v a <;> decide
      · by_cases h8 : (lo f g a).natAbs = 8
        · simp only [h0, h8, if_false, if_true]; cases dot 8 u a <;> cases dot 8 v a <;> decide
        · simp [h0, h8]
    have h1 := hw_div4 u; have h2 := hw_div4 v; have h3 := hw_div4 (add 8 u v)
    omega
  exact ⟨htrD_div8, hn0_even, hc_even, hc2_even⟩

/-- Helper: if `A : W 8 → Bool` has `total 8 (fun a => bind (A a)) = 2`, then there exist TWO
    distinct elements `a1 ≠ a2` with `A a = true ↔ a = a1 ∨ a = a2`, and hence a vector `v`
    with `total 8 (fun a => bind (A a) * bind (dot 8 v a)) = 1`! -/
private theorem odd_hit_of_size2 (A : W 8 → Bool)
    (hsize : total 8 (fun a => bind (A a)) = 2) :
    ∃ v : W 8, total 8 (fun a => bind (A a) * bind (dot 8 v a)) = 1 := by
  have hex1 : ∃ a1 : W 8, A a1 = true := by
    cases h : (worlds 8).all (fun a => !A a)
    · obtain ⟨a1, _, ha1⟩ := all_false_exists _ _ h
      exact ⟨a1, by cases hb : A a1 <;> rw [hb] at ha1 <;> simp_all⟩
    · exfalso; rw [List.all_eq_true] at h
      have h0 : total 8 (fun a => bind (A a)) = 0 := by
        rw [← total_zero 8]; apply congrArg (total 8); funext a
        have ha := h a (all_worlds 8 a)
        cases hb : A a <;> rw [hb] at ha <;> simp [Balanced242Plateau.ind] at ha ⊢
      omega
  obtain ⟨a1, ha1⟩ := hex1
  have hex2 : ∃ a2 : W 8, a2 ≠ a1 ∧ A a2 = true := by
    cases h : (worlds 8).all (fun a => decide (a = a1) || !A a)
    · obtain ⟨a2, _, ha2⟩ := all_false_exists _ _ h
      have hne : a2 ≠ a1 := by intro e; subst e; simp at ha2
      have hA : A a2 = true := by cases hb : A a2 <;> rw [hb] at ha2 <;> simp [hne] at ha2 ⊢
      exact ⟨a2, hne, hA⟩
    · exfalso; rw [List.all_eq_true] at h
      have hle : total 8 (fun a => bind (A a)) ≤ 1 := by
        have hm := total_mono 8 (fun a => bind (A a)) (hits a1) (fun a => by
          have ha := h a (all_worlds 8 a); unfold hits Balanced242Plateau.ind
          by_cases e : a = a1
          · subst e; simp; cases A a <;> decide
          · have hne : ¬ a1 = a := fun h' => e h'.symm
            rw [decide_eq_false e, Bool.false_or] at ha; dsimp only
            cases hb : A a <;> simp [hne, hb] at ha ⊢)
        rw [diagonal 8 a1] at hm; exact hm
      omega
  obtain ⟨a2, ha2_ne, ha2⟩ := hex2
  -- Show `A a = true → a = a1 ∨ a = a2`!
  have hmem (a : W 8) : bind (A a) = hits a1 a + hits a2 a := by
    have hge (x : W 8) : 0 ≤ bind (A x) - (hits a1 x + hits a2 x) := by
      unfold hits Balanced242Plateau.ind
      by_cases e1 : a1 = x
      · subst e1; have hne : ¬ a2 = a1 := ha2_ne; simp [ha1, hne]
      · by_cases e2 : a2 = x
        · subst e2; simp [ha2, e1]
        · simp [e1, e2]; cases A x <;> decide
    have hsum : total 8 (fun x => bind (A x) - (hits a1 x + hits a2 x)) = 0 := by
      rw [total_sub, total_add, diagonal 8 a1, diagonal 8 a2, hsize]; omega
    have hp := point_le_total 8 _ hge a; rw [hsum] at hp; have h0 := hge a; omega
  have hdiff_ne : add 8 a1 a2 ≠ zero 8 := by
    intro hz; apply ha2_ne; have h := congrArg (add 8 a1) hz
    rw [← Balanced242Plateau.add_assoc', add_self, add_zero_left, add_zero_right] at h; exact h
  obtain ⟨v, hv⟩ := exists_dot_true (add 8 a1 a2) hdiff_ne
  refine ⟨v, ?_⟩
  have hpt (a : W 8) : bind (A a) * bind (dot 8 v a) =
      hits a1 a * bind (dot 8 v a1) + hits a2 a * bind (dot 8 v a2) := by
    rw [hmem a, Int.add_mul]
    congr 1 <;> (unfold hits; split <;> simp_all)
  rw [funext hpt, total_add]
  have s1 : total 8 (fun a => hits a1 a * bind (dot 8 v a1)) = bind (dot 8 v a1) := by
    have h : (fun a => hits a1 a * bind (dot 8 v a1)) = fun a => bind (dot 8 v a1) * hits a1 a :=
      funext (fun a => Int.mul_comm _ _)
    rw [h, total_scale, diagonal 8 a1, Int.mul_one]
  have s2 : total 8 (fun a => hits a2 a * bind (dot 8 v a2)) = bind (dot 8 v a2) := by
    have h : (fun a => hits a2 a * bind (dot 8 v a2)) = fun a => bind (dot 8 v a2) * hits a2 a :=
      funext (fun a => Int.mul_comm _ _)
    rw [h, total_scale, diagonal 8 a2, Int.mul_one]
  rw [s1, s2]
  rw [dot_right] at hv
  cases h1 : dot 8 v a1 <;> cases h2 : dot 8 v a2 <;> rw [h1, h2] at hv <;> simp [Balanced242Plateau.ind] at hv ⊢

/-- Helper: if `S : W 8 → Bool` satisfies `S 0 = false`, `c(u)` even, `c2(u, v)` even,
    then NEVER `c(u) = 2`, and NEVER `c(u) = |S| - 1` when `|S|` is odd! -/
private theorem rank4_zero_count_cases (Z0 : W 8 → Bool) (h0 : Z0 (zero 8) = true)
    (heven : ∀ u : W 8, total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) % 2 = 0)
    (hpair : ∀ u v : W 8, total 8 (fun a => bind (Z0 a) * bind (dot 8 u a && dot 8 v a)) % 2 = 0) :
    let N := total 8 (fun a => bind (Z0 a))
    (∀ u : W 8, total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) ≠ 2) ∧
    (N % 2 = 0 → 8 ≤ N) ∧
    (N = 8 → ∀ u : W 8, total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) = 0 ∨
                        total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) = 4) := by
  let N := total 8 (fun a => bind (Z0 a))
  have hno2 (u : W 8) : total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) ≠ 2 := by
    intro h2
    let A : W 8 → Bool := fun a => Z0 a && dot 8 u a
    have hAsz : total 8 (fun a => bind (A a)) = 2 := by
      rw [← h2]; apply congrArg (total 8); funext a
      dsimp only [A]; cases Z0 a <;> cases dot 8 u a <;> decide
    obtain ⟨v, hv⟩ := odd_hit_of_size2 A hAsz
    have heq : total 8 (fun a => bind (Z0 a) * bind (dot 8 u a && dot 8 v a)) = 1 := by
      rw [← hv]; apply congrArg (total 8); funext a
      dsimp only [A]; cases Z0 a <;> cases dot 8 u a <;> cases dot 8 v a <;> decide
    have hp := hpair u v; omega
  have hle_N (u : W 8) : total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) ≤ N - 1 := by
    have hpt (a : W 8) : bind (Z0 a) * bind (dot 8 u a) ≤ bind (Z0 a) - hits (zero 8) a := by
      by_cases hz : a = zero 8
      · subst hz; rw [dot_zero_right]; unfold hits; simp [h0, Balanced242Plateau.ind]
      · have hne : ¬ zero 8 = a := fun e => hz e.symm
        unfold hits; simp [hne]; cases Z0 a <;> cases dot 8 u a <;> decide
    have hm := total_mono 8 _ _ hpt
    rw [total_sub, diagonal 8 (zero 8)] at hm; exact hm
  have hnn (u : W 8) : 0 ≤ total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) :=
    total_nonneg _ (fun a => by cases Z0 a <;> cases dot 8 u a <;> decide)
  -- Key helper: if `N ≥ 2`, there exists `u` with `c(u) > 0`!
  have hex_pos (hN2 : 2 ≤ N) : ∃ u : W 8, 1 ≤ total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) := by
    cases h : (worlds 8).all (fun a => decide (a = zero 8) || !Z0 a)
    · obtain ⟨a1, _, ha1⟩ := all_false_exists _ _ h
      have hne : a1 ≠ zero 8 := by intro e; subst e; simp at ha1
      have hZa : Z0 a1 = true := by cases hb : Z0 a1 <;> rw [hb] at ha1 <;> simp [hne] at ha1 ⊢
      obtain ⟨u, hu⟩ := exists_dot_true a1 hne
      refine ⟨u, ?_⟩
      have hp := point_le_total 8 (fun a => bind (Z0 a) * bind (dot 8 u a))
        (fun a => by dsimp only; cases Z0 a <;> cases dot 8 u a <;> decide) a1
      rw [hZa, hu] at hp; simpa [Balanced242Plateau.ind] using hp
    · exfalso; rw [List.all_eq_true] at h
      have hle1 : N ≤ 1 := by
        have hm := total_mono 8 (fun a => bind (Z0 a)) (hits (zero 8)) (fun a => by
          have ha := h a (all_worlds 8 a); unfold hits Balanced242Plateau.ind
          by_cases e : a = zero 8
          · subst e; simp [h0]
          · have hne : ¬ zero 8 = a := fun h' => e h'.symm
            rw [decide_eq_false e, Bool.false_or] at ha; dsimp only
            cases hb : Z0 a <;> simp [hne, hb] at ha ⊢)
        rw [diagonal 8 (zero 8)] at hm; exact hm
      omega
  -- Key helper: if `c(u) = N - 2` (so exactly 1 nonzero point of `Z0` has `u·a = 0`),
  -- then any `v` hitting that 1 point satisfies `c2(u, v) = c(v) - 1` (ODD!!), contradiction!
  have hno_Nm2 (u : W 8) (hcu : total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) = N - 2) : False := by
    -- The set `{a ≠ 0 : Z0 a ∧ !dot u a}` has size `(N - 1) - (N - 2) = 1`, so pick its element `a_miss`!
    let M (a : W 8) : Bool := decide (a ≠ zero 8) && Z0 a && !dot 8 u a
    have hMsum : total 8 (fun a => bind (M a)) = 1 := by
      have hpt (a : W 8) : bind (M a) = bind (Z0 a) - hits (zero 8) a - bind (Z0 a) * bind (dot 8 u a) := by
        dsimp only [M]; unfold hits
        by_cases hz : a = zero 8
        · subst hz; rw [dot_zero_right]; simp [h0, Balanced242Plateau.ind]
        · have hne : ¬ zero 8 = a := fun e => hz e.symm
          rw [decide_eq_true hz, Bool.true_and, if_neg hne, Int.sub_zero]
          cases Z0 a <;> cases dot 8 u a <;> decide
      rw [funext hpt, total_sub, total_sub, diagonal 8 (zero 8)]; omega
    have hex_m : ∃ am : W 8, M am = true := by
      cases h : (worlds 8).all (fun a => !M a)
      · obtain ⟨am, _, ham⟩ := all_false_exists _ _ h
        exact ⟨am, by cases hb : M am <;> rw [hb] at ham <;> simp_all⟩
      · exfalso; rw [List.all_eq_true] at h
        have h0' : total 8 (fun a => bind (M a)) = 0 := by
          rw [← total_zero 8]; apply congrArg (total 8); funext a
          have ha := h a (all_worlds 8 a)
          cases hb : M a <;> rw [hb] at ha <;> simp [Balanced242Plateau.ind] at ha ⊢
        omega
    obtain ⟨am, ham⟩ := hex_m
    have ham_ne : am ≠ zero 8 := by
      dsimp only [M] at ham; by_cases e : am = zero 8 <;> simp [e] at ham ⊢
    have ham_Z : Z0 am = true := by
      dsimp only [M] at ham; cases h1 : Z0 am <;> rw [h1] at ham <;> simp at ham ⊢
    have ham_du : dot 8 u am = false := by
      dsimp only [M] at ham; cases h1 : dot 8 u am <;> rw [h1] at ham <;> simp at ham ⊢
    -- Show `M a = true ↔ a = am`, i.e., `bind (M a) = hits am a`!
    have hM_eq (a : W 8) : bind (M a) = hits am a := by
      have hge (x : W 8) : 0 ≤ bind (M x) - hits am x := by
        unfold hits; by_cases e : am = x
        · subst e; simp [ham, Balanced242Plateau.ind]
        · simp [e]; exact Balanced242Plateau.ind_nonneg _
      have hs : total 8 (fun x => bind (M x) - hits am x) = 0 := by
        rw [total_sub, hMsum, diagonal 8 am]; omega
      have hp := point_le_total 8 _ hge a; rw [hs] at hp; have h0' := hge a; omega
    obtain ⟨v, hv⟩ := exists_dot_true am ham_ne
    -- Compute `c(v) - c2(u, v) = ∑_a bind (Z0 a) * bind (!dot u a && dot v a) = ∑_a bind (M a) * bind (dot v a) = 1`!
    have hdiff : total 8 (fun a => bind (Z0 a) * bind (dot 8 v a)) -
                 total 8 (fun a => bind (Z0 a) * bind (dot 8 u a && dot 8 v a)) = 1 := by
      rw [← total_sub]
      have hpt (a : W 8) :
          bind (Z0 a) * bind (dot 8 v a) - bind (Z0 a) * bind (dot 8 u a && dot 8 v a) =
          bind (M a) * bind (dot 8 v a) := by
        dsimp only [M]
        by_cases hz : a = zero 8
        · subst hz; rw [dot_zero_right]; simp [Balanced242Plateau.ind]
        · rw [decide_eq_true hz, Bool.true_and]
          cases Z0 a <;> cases dot 8 u a <;> cases dot 8 v a <;> decide
      rw [funext hpt]
      have hpt2 (a : W 8) : bind (M a) * bind (dot 8 v a) = hits am a := by
        rw [hM_eq a]; unfold hits; by_cases e : am = a
        · subst e; simp [hv, Balanced242Plateau.ind]
        · simp [e]
      rw [funext hpt2, diagonal 8 am]
    have he1 := heven v; have he2 := hpair u v; omega
  have hge1 : 1 ≤ N := by
    have hp := point_le_total 8 (fun a => bind (Z0 a)) (fun a => Balanced242Plateau.ind_nonneg _) (zero 8)
    rw [h0] at hp; simpa [Balanced242Plateau.ind] using hp
  refine ⟨hno2, ?_, ?_⟩
  · intro hNeven
    by_cases hlt : N < 8
    · exfalso
      have hN_cases : N = 2 ∨ N = 4 ∨ N = 6 := by omega
      obtain ⟨u, hu⟩ := hex_pos (by omega)
      have heu := heven u; have h2u := hno2 u; have hle := hle_N u
      rcases hN_cases with h2 | h4 | h6
      · omega
      · omega
      · have hcu4 : total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) = 4 := by omega
        exact hno_Nm2 u (by omega)
    · omega
  · intro hN8 u
    have heu := heven u; have h2u := hno2 u; have hle := hle_N u; have h0u := hnn u
    by_cases h6 : total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) = 6
    · exact False.elim (hno_Nm2 u (by omega))
    · omega

/-- **Theorem 1 (`rank4_Z96_n0_ge8`)**: For ANY even `t` with rank 4 (`rr = 16`) and `Zc = 96`,
    `8 ≤ n0 f g` (unconditionally excluding `n0 ∈ {2, 4, 6}`!). -/
theorem rank4_Z96_n0_ge8 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (ht_even : agreements f g % 2 = 0)
    (hrr : rr (β8 f g) = 16) (hZc : Zc f g = 96) : 8 ≤ n0 f g := by
  have ⟨_, hn0_even, hc_even, hc2_even⟩ :=
    rank4_Z96_zero_moments f g res dc lores locap ht_even hrr hZc
  let Z0 (a : W 8) : Bool := decide (lo f g a = 0)
  have hN_eq : total 8 (fun a => bind (Z0 a)) = n0 f g := by
    unfold n0; apply congrArg (total 8); funext a
    dsimp only [Z0]; unfold Balanced242Plateau.ind; by_cases h : lo f g a = 0 <;> simp [h]
  have hbind (a : W 8) : bind (Z0 a) = if lo f g a = 0 then (1 : Int) else 0 := by
    dsimp only [Z0]; unfold Balanced242Plateau.ind; by_cases h : lo f g a = 0 <;> simp [h]
  have he1 (u : W 8) : total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) % 2 = 0 := by
    have h := hc_even u; simpa only [hbind] using h
  have he2 (u v : W 8) : total 8 (fun a => bind (Z0 a) * bind (dot 8 u a && dot 8 v a)) % 2 = 0 := by
    have h := hc2_even u v; simpa only [hbind] using h
  have hres := rank4_zero_count_cases Z0 (by simp [Z0, dc]) he1 he2
  rw [hN_eq] at hres
  exact hres.2.1 hn0_even

/-- **Theorem 2 (`rank4_Z96_n0_eq8_subspace`)**: When `rr = 16`, `Zc = 96`, and `n0 f g = 8`,
    the 8-point zero set `{a : lo f g a = 0}` is a LINEAR 3-SUBSPACE of `W 8`! -/
theorem rank4_Z96_n0_eq8_subspace (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (ht_even : agreements f g % 2 = 0)
    (hrr : rr (β8 f g) = 16) (hZc : Zc f g = 96) (hn08 : n0 f g = 8) :
    ∀ a b : W 8, lo f g a = 0 → lo f g b = 0 → lo f g (add 8 a b) = 0 := by
  have ⟨_, _, hc_even, hc2_even⟩ :=
    rank4_Z96_zero_moments f g res dc lores locap ht_even hrr hZc
  let Z0 (a : W 8) : Bool := decide (lo f g a = 0)
  have hbind (a : W 8) : bind (Z0 a) = if lo f g a = 0 then (1 : Int) else 0 := by
    dsimp only [Z0]; unfold Balanced242Plateau.ind; by_cases h : lo f g a = 0 <;> simp [h]
  have hN_eq : total 8 (fun a => bind (Z0 a)) = 8 := by
    rw [← hn08]; unfold n0; apply congrArg (total 8); funext a; exact hbind a
  have hres := rank4_zero_count_cases Z0 (by simp [Z0, dc])
    (fun u => by simpa only [hbind] using hc_even u)
    (fun u v => by simpa only [hbind] using hc2_even u v)
  have hc04 (u : W 8) : total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) = 0 ∨
      total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) = 4 := hres.2.2 hN_eq u
  -- Therefore `transform (bind ∘ Z0) u ∈ {0, 8}` for EVERY `u : W 8`!
  have htr08 (u : W 8) : transform (fun a => bind (Z0 a)) u = 0 ∨
      transform (fun a => bind (Z0 a)) u = 8 := by
    have hrel : transform (fun a => bind (Z0 a)) u =
        8 - 2 * total 8 (fun a => bind (Z0 a) * bind (dot 8 u a)) := by
      rw [← hN_eq]; unfold transform; rw [← total_scale, ← total_sub]
      apply congrArg (total 8); funext a; dsimp only
      unfold chr Balanced242Plateau.ind; cases Z0 a <;> cases dot 8 u a <;> decide
    rcases hc04 u with h | h <;> rw [h] at hrel <;> omega
  -- If `transform (bind ∘ Z0) u = 8`, then EVERY `x ∈ Z0` has `chr u x = 1` (so `dot u x = false`)!
  have horth_of_8 (u : W 8) (h8 : transform (fun a => bind (Z0 a)) u = 8) (x : W 8) (hx : Z0 x = true) :
      chr u x = 1 := by
    have hge (a : W 8) : 0 ≤ bind (Z0 a) * (1 - chr u a) := by
      unfold chr; cases Z0 a <;> cases dot 8 u a <;> decide
    have hsum : total 8 (fun a => bind (Z0 a) * (1 - chr u a)) = 0 := by
      have hpt (a : W 8) : bind (Z0 a) * (1 - chr u a) = bind (Z0 a) - bind (Z0 a) * chr u a := by
        rw [Int.mul_sub, Int.mul_one]
      rw [funext hpt, total_sub, hN_eq]; change 8 - transform (fun a => bind (Z0 a)) u = 0; omega
    have hp := point_le_total 8 _ hge x; rw [hsum, hx] at hp
    have h0' := hge x; rw [hx] at h0'; simp [Balanced242Plateau.ind] at hp h0'; omega
  -- Now prove `Z0 (a ⊕ b) = true` by Walsh inversion (`transform (transform 1_{Z0}) (a ⊕ b) = 256 * bind (Z0 (a ⊕ b))`)!
  intro a b ha hb
  have hZa : Z0 a = true := by simp [Z0, ha]
  have hZb : Z0 b = true := by simp [Z0, hb]
  have hinv_ab := transform_involution (fun x => bind (Z0 x)) (add 8 a b)
  have hinv_0 := transform_involution (fun x => bind (Z0 x)) (zero 8)
  have hm8 : many 8 = 256 := by decide
  rw [hm8] at hinv_ab hinv_0
  have heq : transform (transform (fun x => bind (Z0 x))) (add 8 a b) =
      transform (transform (fun x => bind (Z0 x))) (zero 8) := by
    change total 8 (fun u => transform (fun x => bind (Z0 x)) u * chr (add 8 a b) u) =
           total 8 (fun u => transform (fun x => bind (Z0 x)) u * chr (zero 8) u)
    apply congrArg (total 8); funext u
    rcases htr08 u with h0 | h8
    · rw [h0]; simp
    · rw [h8]
      have hca := horth_of_8 u h8 a hZa
      have hcb := horth_of_8 u h8 b hZb
      have hcab : chr (add 8 a b) u = 1 := by
        have hsym : chr (add 8 a b) u = chr u (add 8 a b) := by unfold chr; rw [dot_comm]
        rw [hsym, Balanced242Plateau.chr_add, hca, hcb]; decide
      have hc0 : chr (zero 8) u = 1 := by unfold chr; rw [dot_zero]; decide
      rw [hcab, hc0]
  rw [hinv_ab, hinv_0] at heq
  have hZ00 : Z0 (zero 8) = true := by simp [Z0, dc]
  rw [hZ00] at heq
  have hZab : Z0 (add 8 a b) = true := by
    cases h : Z0 (add 8 a b) <;> rw [h] at heq <;> simp [Balanced242Plateau.ind] at heq ⊢
  exact of_decide_eq_true hZab

/-! ## Section 2: Canonical `W 4` Quadric `SZ` and Kernel-Verified 729-Cell Table -/

/-- Canonical rank-4 elliptic quadric on `W 4` (6 points):
    `q(c0, c1, c2, c3) = (c0 || c1) ^^ (c2 && c3) = false`. -/
def isSZ (c : W 4) : Bool := !xor (c.1 || c.2.1) (c.2.2.1 && c.2.2.2.1)

/-- The 6 explicit points of `SZ` on `W 4`. -/
private def SZ_pts : List (W 4) :=
  [(false, (false, (false, (false, ())))),
   (false, (false, (false, (true,  ())))),
   (false, (false, (true,  (false, ())))),
   (false, (true,  (true,  (true,  ())))),
   (true,  (false, (true,  (true,  ())))),
   (true,  (true,  (true,  (true,  ()))))]

private theorem isSZ_sum_nonzero (s1 s2 : W 4)
    (h1 : isSZ s1 = true) (h2 : isSZ s2 = true)
    (hn1 : s1 ≠ zero 4) (hn2 : s2 ≠ zero 4) (hne : s1 ≠ s2) :
    isSZ (add 4 s1 s2) = false := by
  have hall : (worlds 4).all (fun a => (worlds 4).all (fun b =>
      !(isSZ a && isSZ b && decide (a ≠ zero 4) && decide (b ≠ zero 4) && decide (a ≠ b)) ||
      !isSZ (add 4 a b))) = true := by decide
  rw [List.all_eq_true] at hall
  have h := hall s1 (all_worlds 4 s1); rw [List.all_eq_true] at h
  have h := h s2 (all_worlds 4 s2)
  rw [h1, h2, decide_eq_true hn1, decide_eq_true hn2, decide_eq_true hne] at h
  cases e : isSZ (add 4 s1 s2) <;> rw [e] at h <;> simp at h ⊢

/-- Symmetric map picking a witness `c ∈ SZc` with `z(c)^2 = 36` for any `m = 10` cell
    whose two zeros in `SZ` are `{s1, s2}`. -/
def pickC (s1 s2 : W 4) : W 4 :=
  if s1 = zero 4 then
    if s2 = (false, (false, (false, (true, ())))) ∨ s2 = (false, (false, (true, (false, ())))) then
      (false, (false, (true, (true, ()))))
    else if s2 = (false, (true, (true, (true, ())))) then
      (false, (true, (false, (true, ()))))
    else (false, (true, (false, (false, ()))))
  else if s2 = zero 4 then
    if s1 = (false, (false, (false, (true, ())))) ∨ s1 = (false, (false, (true, (false, ())))) then
      (false, (false, (true, (true, ()))))
    else if s1 = (false, (true, (true, (true, ())))) then
      (false, (true, (false, (true, ()))))
    else (false, (true, (false, (false, ()))))
  else add 4 s1 s2

private theorem pickC_not_SZ (s1 s2 : W 4) (h1 : isSZ s1 = true) (h2 : isSZ s2 = true) (hne : s1 ≠ s2) :
    isSZ (pickC s1 s2) = false := by
  have hall : (worlds 4).all (fun a => (worlds 4).all (fun b =>
      !(isSZ a && isSZ b && decide (a ≠ b)) || !isSZ (pickC a b))) = true := by decide
  rw [List.all_eq_true] at hall
  have h := hall s1 (all_worlds 4 s1); rw [List.all_eq_true] at h
  have h := h s2 (all_worlds 4 s2)
  rw [h1, h2, decide_eq_true hne] at h
  cases e : isSZ (pickC s1 s2) <;> rw [e] at h <;> simp at h ⊢

/-- Reconstruct a ternary cell `v : W 4 → Int` from its 6 mod-3 Walsh residues `(r0..r5) ∈ {0,1,2}^6` on `SZ`. -/
private def mkCell4 (r0 r1 r2 r3 r4 r5 : Int) (x : W 4) : Int :=
  mods3 (r0 * @chr 4 (false, (false, (false, (false, ())))) x +
         r1 * @chr 4 (false, (false, (false, (true,  ())))) x +
         r2 * @chr 4 (false, (false, (true,  (false, ())))) x +
         r3 * @chr 4 (false, (true,  (true,  (true,  ())))) x +
         r4 * @chr 4 (true,  (false, (true,  (true,  ())))) x +
         r5 * @chr 4 (true,  (true,  (true,  (true,  ())))) x)

/-- Fast 4-stage FWHT on 16 integers (zero recomputation, 1000x faster in Lean's kernel!). -/
private def fwht16 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Int) :
    (Int × Int × Int × Int) × (Int × Int × Int × Int) ×
    (Int × Int × Int × Int) × (Int × Int × Int × Int) :=
  let a0 := v0 + v1; let a1 := v0 - v1; let a2 := v2 + v3; let a3 := v2 - v3
  let a4 := v4 + v5; let a5 := v4 - v5; let a6 := v6 + v7; let a7 := v6 - v7
  let a8 := v8 + v9; let a9 := v8 - v9; let a10 := v10 + v11; let a11 := v10 - v11
  let a12 := v12 + v13; let a13 := v12 - v13; let a14 := v14 + v15; let a15 := v14 - v15
  let b0 := a0 + a2; let b1 := a1 + a3; let b2 := a0 - a2; let b3 := a1 - a3
  let b4 := a4 + a6; let b5 := a5 + a7; let b6 := a4 - a6; let b7 := a5 - a7
  let b8 := a8 + a10; let b9 := a9 + a11; let b10 := a8 - a10; let b11 := a9 - a11
  let b12 := a12 + a14; let b13 := a13 + a15; let b14 := a12 - a14; let b15 := a13 - a15
  let c0 := b0 + b4; let c1 := b1 + b5; let c2 := b2 + b6; let c3 := b3 + b7
  let c4 := b0 - b4; let c5 := b1 - b5; let c6 := b2 - b6; let c7 := b3 - b7
  let c8 := b8 + b12; let c9 := b9 + b13; let c10 := b10 + b14; let c11 := b11 + b15
  let c12 := b8 - b12; let c13 := b9 - b13; let c14 := b10 - b14; let c15 := b11 - b15
  ((c0 + c8, c1 + c9, c2 + c10, c3 + c11),
   (c4 + c12, c5 + c13, c6 + c14, c7 + c15),
   (c0 - c8, c1 - c9, c2 - c10, c3 - c11),
   (c4 - c12, c5 - c13, c6 - c14, c7 - c15))

private def lookup16 (t : (Int × Int × Int × Int) × (Int × Int × Int × Int) ×
                          (Int × Int × Int × Int) × (Int × Int × Int × Int)) (c : W 4) : Int :=
  match c with
  | (false, (false, (false, (false, ())))) => t.1.1
  | (false, (false, (false, (true,  ())))) => t.1.2.1
  | (false, (false, (true,  (false, ())))) => t.1.2.2.1
  | (false, (false, (true,  (true,  ())))) => t.1.2.2.2
  | (false, (true,  (false, (false, ())))) => t.2.1.1
  | (false, (true,  (false, (true,  ())))) => t.2.1.2.1
  | (false, (true,  (true,  (false, ())))) => t.2.1.2.2.1
  | (false, (true,  (true,  (true,  ())))) => t.2.1.2.2.2
  | (true,  (false, (false, (false, ())))) => t.2.2.1.1
  | (true,  (false, (false, (true,  ())))) => t.2.2.1.2.1
  | (true,  (false, (true,  (false, ())))) => t.2.2.1.2.2.1
  | (true,  (false, (true,  (true,  ())))) => t.2.2.1.2.2.2
  | (true,  (true,  (false, (false, ())))) => t.2.2.2.1
  | (true,  (true,  (false, (true,  ())))) => t.2.2.2.2.1
  | (true,  (true,  (true,  (false, ())))) => t.2.2.2.2.2.1
  | (true,  (true,  (true,  (true,  ())))) => t.2.2.2.2.2.2

private theorem fwht16_eq_transform (v : W 4 → Int) (c : W 4) :
    lookup16 (fwht16
      (v (false, (false, (false, (false, ()))))) (v (false, (false, (false, (true,  ())))))
      (v (false, (false, (true,  (false, ()))))) (v (false, (false, (true,  (true,  ())))))
      (v (false, (true,  (false, (false, ()))))) (v (false, (true,  (false, (true,  ())))))
      (v (false, (true,  (true,  (false, ()))))) (v (false, (true,  (true,  (true,  ())))))
      (v (true,  (false, (false, (false, ()))))) (v (true,  (false, (false, (true,  ())))))
      (v (true,  (false, (true,  (false, ()))))) (v (true,  (false, (true,  (true,  ())))))
      (v (true,  (true,  (false, (false, ()))))) (v (true,  (true,  (false, (true,  ())))))
      (v (true,  (true,  (true,  (false, ()))))) (v (true,  (true,  (true,  (true,  ())))))) c =
    transform v c := by
  rcases c with ⟨b0, b1, b2, b3, ⟨⟩⟩
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    (dsimp [fwht16, lookup16, transform, total, chr, dot, sign]; omega)

private def checkZ16 (m z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 : Int) : Bool :=
  let q0 := z0*z0; let q1 := z1*z1; let q2 := z2*z2; let q3 := z3*z3
  let q4 := z4*z4; let q5 := z5*z5; let q6 := z6*z6; let q7 := z7*z7
  let q8 := z8*z8; let q9 := z9*z9; let q10 := z10*z10; let q11 := z11*z11
  let q12 := z12*z12; let q13 := z13*z13; let q14 := z14*z14; let q15 := z15*z15
  let eSZc := q3 + q4 + q5 + q6 + q8 + q9 + q10 + q12 + q13 + q14
  let cSZ (t : Int) : Int :=
    (if q0 = t then 1 else 0) + (if q1 = t then 1 else 0) + (if q2 = t then 1 else 0) +
    (if q7 = t then 1 else 0) + (if q11 = t then 1 else 0) + (if q15 = t then 1 else 0)
  let allSZc (p : Int → Bool) : Bool :=
    p q3 && p q4 && p q5 && p q6 && p q8 && p q9 && p q10 && p q12 && p q13 && p q14
  let allSZ (p : Int → Bool) : Bool :=
    p q0 && p q1 && p q2 && p q7 && p q11 && p q15
  let pairOk (a b w : Int) : Bool := !(decide (a = 0) && decide (b = 0)) || decide (w = 36)
  if m % 2 = 1 then
    decide (11 ≤ m) && allSZc (fun q => decide (q = 9)) && decide (eSZc = 90)
  else
    decide (m = 0 ∨ m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12 ∨ m = 16) &&
    allSZc (fun q => decide (q = 0 ∨ q = 36 ∨ q = 144)) &&
    (if m = 0 then decide (eSZc = 0) && allSZ (fun q => decide (q = 0))
     else if m = 6 then decide (eSZc = 0) && allSZ (fun q => decide (q = 16))
     else if m = 8 then
       decide (eSZc = 0) && allSZ (fun q => decide (q = 0 ∨ q = 64)) && decide (cSZ 64 = 2)
     else if m = 10 then
       decide (eSZc = 144) && allSZ (fun q => decide (q = 0 ∨ q = 4)) && decide (cSZ 4 = 4) &&
       pairOk z0 z1 q3 && pairOk z0 z2 q3 && pairOk z0 z7 q5 && pairOk z0 z11 q4 && pairOk z0 z15 q4 &&
       pairOk z1 z2 q3 && pairOk z1 z7 q6 && pairOk z1 z11 q10 && pairOk z1 z15 q14 &&
       pairOk z2 z7 q5 && pairOk z2 z11 q9 && pairOk z2 z15 q13 &&
       pairOk z7 z11 q12 && pairOk z7 z15 q8 && pairOk z11 z15 q4
     else if m = 12 then
       decide (eSZc = 144) && allSZ (fun q => decide (q = 0 ∨ q = 16)) && decide (cSZ 16 = 3)
     else
       decide (eSZc = 0) && allSZ (fun q => decide (q = 0 ∨ q = 256)) && decide (cSZ 256 = 1))

private def checkVec16 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Int) : Bool :=
  let m := v0*v0 + v1*v1 + v2*v2 + v3*v3 + v4*v4 + v5*v5 + v6*v6 + v7*v7 +
           v8*v8 + v9*v9 + v10*v10 + v11*v11 + v12*v12 + v13*v13 + v14*v14 + v15*v15
  let ((z0, z1, z2, z3), (z4, z5, z6, z7), (z8, z9, z10, z11), (z12, z13, z14, z15)) :=
    fwht16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  checkZ16 m z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15

/-- Fast zero-recomputation boolean checker for any one of the `3^6 = 729` ternary cells on `W 4`. -/
private def checkOneCellFast (r0 r1 r2 r3 r4 r5 : Int) : Bool :=
  checkVec16
    (mods3 (r0 + r1 + r2 + r3 + r4 + r5)) (mods3 (r0 - r1 + r2 - r3 - r4 - r5))
    (mods3 (r0 + r1 - r2 - r3 - r4 - r5)) (mods3 (r0 - r1 - r2 + r3 + r4 + r5))
    (mods3 (r0 + r1 + r2 - r3 + r4 - r5)) (mods3 (r0 - r1 + r2 + r3 - r4 + r5))
    (mods3 (r0 + r1 - r2 + r3 - r4 + r5)) (mods3 (r0 - r1 - r2 - r3 + r4 - r5))
    (mods3 (r0 + r1 + r2 + r3 - r4 - r5)) (mods3 (r0 - r1 + r2 - r3 + r4 + r5))
    (mods3 (r0 + r1 - r2 - r3 + r4 + r5)) (mods3 (r0 - r1 - r2 + r3 - r4 - r5))
    (mods3 (r0 + r1 + r2 - r3 - r4 + r5)) (mods3 (r0 - r1 + r2 + r3 + r4 - r5))
    (mods3 (r0 + r1 - r2 + r3 + r4 - r5)) (mods3 (r0 - r1 - r2 - r3 - r4 + r5))

private def checkAll729Fast : Bool :=
  let ds : List Int := [0, 1, 2]
  ds.all (fun r0 => ds.all (fun r1 => ds.all (fun r2 =>
  ds.all (fun r3 => ds.all (fun r4 => ds.all (fun r5 => checkOneCellFast r0 r1 r2 r3 r4 r5))))))

/-- Pure kernel verification of all 729 ternary 4-bit cells (runs in < 0.2s, zero axioms!). -/
private theorem checkAll729Fast_ok : checkAll729Fast = true := by decide +kernel

private theorem checkOneCellFast_of_mod3 (r0 r1 r2 r3 r4 r5 : Int)
    (h0 : r0 = 0 ∨ r0 = 1 ∨ r0 = 2) (h1 : r1 = 0 ∨ r1 = 1 ∨ r1 = 2)
    (h2 : r2 = 0 ∨ r2 = 1 ∨ r2 = 2) (h3 : r3 = 0 ∨ r3 = 1 ∨ r3 = 2)
    (h4 : r4 = 0 ∨ r4 = 1 ∨ r4 = 2) (h5 : r5 = 0 ∨ r5 = 1 ∨ r5 = 2) :
    checkOneCellFast r0 r1 r2 r3 r4 r5 = true := by
  have hall := checkAll729Fast_ok
  unfold checkAll729Fast at hall
  have mem3 (r : Int) (hr : r = 0 ∨ r = 1 ∨ r = 2) : r ∈ ([0, 1, 2] : List Int) := by
    rcases hr with rfl | rfl | rfl <;> simp
  rw [List.all_eq_true] at hall; have hall := hall r0 (mem3 r0 h0)
  rw [List.all_eq_true] at hall; have hall := hall r1 (mem3 r1 h1)
  rw [List.all_eq_true] at hall; have hall := hall r2 (mem3 r2 h2)
  rw [List.all_eq_true] at hall; have hall := hall r3 (mem3 r3 h3)
  rw [List.all_eq_true] at hall; have hall := hall r4 (mem3 r4 h4)
  rw [List.all_eq_true] at hall; exact hall r5 (mem3 r5 h5)

set_option maxHeartbeats 600000 in
/-- Any ternary `v : W 4 → Int` whose 4-bit Walsh transform is divisible by 3 on `SZc`
    equals `mkCell4 (z s0 % 3) ... (z s5 % 3)` and therefore satisfies the complete cell specification! -/
private theorem cell4_spec (v : W 4 → Int)
    (htern : ∀ x : W 4, v x = -1 ∨ v x = 0 ∨ v x = 1)
    (hmod3 : ∀ c : W 4, isSZ c = false → transform v c % 3 = 0) :
    let m := total 4 (fun x => v x * v x)
    let z (c : W 4) := transform v c
    let eSZc := total 4 (fun c => if !isSZ c then z c * z c else 0)
    (m % 2 = 1 → 11 ≤ m ∧ eSZc = 90 ∧ ∀ c, isSZ c = false → z c * z c = 9) ∧
    (m % 2 = 0 →
      (m = 0 ∨ m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12 ∨ m = 16) ∧
      (∀ c, isSZ c = false → z c * z c = 0 ∨ z c * z c = 36 ∨ z c * z c = 144) ∧
      (m = 0 → eSZc = 0 ∧ ∀ s, isSZ s = true → z s * z s = 0) ∧
      (m = 6 → eSZc = 0 ∧ ∀ s, isSZ s = true → z s * z s = 16) ∧
      (m = 8 → eSZc = 0 ∧ (∀ s, isSZ s = true → z s * z s = 0 ∨ z s * z s = 64) ∧
               total 4 (fun s => if isSZ s && decide (z s * z s = 64) then (1 : Int) else 0) = 2) ∧
      (m = 10 → eSZc = 144 ∧ (∀ s, isSZ s = true → z s * z s = 0 ∨ z s * z s = 4) ∧
                total 4 (fun s => if isSZ s && decide (z s * z s = 4) then (1 : Int) else 0) = 4 ∧
                ∀ s1 s2, isSZ s1 = true → isSZ s2 = true → s1 ≠ s2 → z s1 = 0 → z s2 = 0 →
                  z (pickC s1 s2) * z (pickC s1 s2) = 36) ∧
      (m = 12 → eSZc = 144 ∧ (∀ s, isSZ s = true → z s * z s = 0 ∨ z s * z s = 16) ∧
                total 4 (fun s => if isSZ s && decide (z s * z s = 16) then (1 : Int) else 0) = 3) ∧
      (m = 16 → eSZc = 0 ∧ (∀ s, isSZ s = true → z s * z s = 0 ∨ z s * z s = 256) ∧
                total 4 (fun s => if isSZ s && decide (z s * z s = 256) then (1 : Int) else 0) = 1)) := by
  let s0 : W 4 := (false, (false, (false, (false, ()))))
  let s1 : W 4 := (false, (false, (false, (true,  ()))))
  let s2 : W 4 := (false, (false, (true,  (false, ()))))
  let s3 : W 4 := (false, (true,  (true,  (true,  ()))))
  let s4 : W 4 := (true,  (false, (true,  (true,  ()))))
  let s5 : W 4 := (true,  (true,  (true,  (true,  ()))))
  let r0 := transform v s0 % 3; let r1 := transform v s1 % 3; let r2 := transform v s2 % 3
  let r3 := transform v s3 % 3; let r4 := transform v s4 % 3; let r5 := transform v s5 % 3
  have hrm (c : W 4) : transform v c % 3 = 0 ∨ transform v c % 3 = 1 ∨ transform v c % 3 = 2 := by omega
  have hfast : checkOneCellFast r0 r1 r2 r3 r4 r5 = true :=
    checkOneCellFast_of_mod3 r0 r1 r2 r3 r4 r5 (hrm s0) (hrm s1) (hrm s2) (hrm s3) (hrm s4) (hrm s5)
  have hveq : v = mkCell4 r0 r1 r2 r3 r4 r5 := by
    funext x
    have hinv := transform_involution v x
    have hm4 : many 4 = 16 := by decide
    rw [hm4] at hinv
    have htr_mod :
        (transform (transform v) x -
          (r0 * chr s0 x + r1 * chr s1 x + r2 * chr s2 x +
           r3 * chr s3 x + r4 * chr s4 x + r5 * chr s5 x)) % 3 = 0 := by
      have hsplit : transform (transform v) x =
          total 4 (fun c => if isSZ c then transform v c * chr c x else 0) +
          total 4 (fun c => if !isSZ c then transform v c * chr c x else 0) := by
        rw [← total_add]; unfold transform; apply congrArg (total 4); funext c
        have hsym : chr x c = chr c x := by unfold chr; rw [dot_comm]
        rw [hsym]; cases isSZ c <;> simp
      have hSZc0 : total 4 (fun c => if !isSZ c then transform v c * chr c x else 0) % 3 = 0 := by
        have hdiv (c : W 4) : (if !isSZ c then transform v c * chr c x else 0) % 3 = 0 := by
          cases hc : isSZ c
          · simp only [Bool.not_false, if_true]; have h3 := hmod3 c hc
            have hchr : chr c x = 1 ∨ chr c x = -1 := sign_vals _
            rcases hchr with e | e <;> rw [e] <;> omega
          · simp
        have aux : ∀ {m : Nat} (F : W m → Int), (∀ c, F c % 3 = 0) → total m F % 3 = 0 := by
          intro m; induction m with
          | zero => intro F hF; exact hF ()
          | succ m ih =>
            intro F hF
            change (total m (fun y => F (false, y)) + total m (fun y => F (true, y))) % 3 = 0
            have h1 := ih (fun y => F (false, y)) (fun y => hF _)
            have h2 := ih (fun y => F (true, y)) (fun y => hF _)
            omega
        exact aux _ hdiv
      have hSZ_exp (F : W 4 → Int) :
          total 4 (fun c => if isSZ c then F c else 0) =
          F s0 + F s1 + F s2 + F s3 + F s4 + F s5 := by
        dsimp only [s0, s1, s2, s3, s4, s5]
        change (((F (false, (false, (false, (false, ())))) + F (false, (false, (false, (true, ()))))) +
                (F (false, (false, (true, (false, ())))) + 0)) +
               ((0 + 0) + (0 + F (false, (true, (true, (true, ()))))))) +
              (((0 + 0) + (0 + F (true, (false, (true, (true, ())))))) +
               ((0 + 0) + (0 + F (true, (true, (true, (true, ()))))))) = _
        omega
      rw [hsplit, hSZ_exp]
      have hm (c : W 4) : (transform v c * chr c x - (transform v c % 3) * chr c x) % 3 = 0 := by
        have hc : chr c x = 1 ∨ chr c x = -1 := sign_vals _
        rcases hc with e | e <;> rw [e] <;> omega
      have m0 := hm s0; have m1 := hm s1; have m2 := hm s2
      have m3 := hm s3; have m4 := hm s4; have m5 := hm s5
      dsimp only [r0, r1, r2, r3, r4, r5]; omega
    rw [hinv] at htr_mod
    dsimp only [mkCell4]
    have hmod1 : (v x - (r0 * chr s0 x + r1 * chr s1 x + r2 * chr s2 x +
        r3 * chr s3 x + r4 * chr s4 x + r5 * chr s5 x)) % 3 = 0 := by omega
    have hspec (u z : Int) (hu : u = -1 ∨ u = 0 ∨ u = 1) (hm : (u - z) % 3 = 0) : u = mods3 z := by
      unfold mods3; rcases hu with rfl | rfl | rfl <;> omega
    exact hspec (v x) _ (htern x) hmod1
  -- Connect the 16 fast entries directly to `m`, `transform v`, and `eSZc`!
  have hv0  : v (false, (false, (false, (false, ())))) = mods3 (r0 + r1 + r2 + r3 + r4 + r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv1  : v (false, (false, (false, (true,  ())))) = mods3 (r0 - r1 + r2 - r3 - r4 - r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv2  : v (false, (false, (true,  (false, ())))) = mods3 (r0 + r1 - r2 - r3 - r4 - r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv3  : v (false, (false, (true,  (true,  ())))) = mods3 (r0 - r1 - r2 + r3 + r4 + r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv4  : v (false, (true,  (false, (false, ())))) = mods3 (r0 + r1 + r2 - r3 + r4 - r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv5  : v (false, (true,  (false, (true,  ())))) = mods3 (r0 - r1 + r2 + r3 - r4 + r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv6  : v (false, (true,  (true,  (false, ())))) = mods3 (r0 + r1 - r2 + r3 - r4 + r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv7  : v (false, (true,  (true,  (true,  ())))) = mods3 (r0 - r1 - r2 - r3 + r4 - r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv8  : v (true,  (false, (false, (false, ())))) = mods3 (r0 + r1 + r2 + r3 - r4 - r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv9  : v (true,  (false, (false, (true,  ())))) = mods3 (r0 - r1 + r2 - r3 + r4 + r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv10 : v (true,  (false, (true,  (false, ())))) = mods3 (r0 + r1 - r2 - r3 + r4 + r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv11 : v (true,  (false, (true,  (true,  ())))) = mods3 (r0 - r1 - r2 + r3 - r4 - r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv12 : v (true,  (true,  (false, (false, ())))) = mods3 (r0 + r1 + r2 - r3 - r4 + r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv13 : v (true,  (true,  (false, (true,  ())))) = mods3 (r0 - r1 + r2 + r3 + r4 - r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv14 : v (true,  (true,  (true,  (false, ())))) = mods3 (r0 + r1 - r2 + r3 + r4 - r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hv15 : v (true,  (true,  (true,  (true,  ())))) = mods3 (r0 - r1 - r2 - r3 - r4 + r5) := by rw [hveq]; dsimp [mkCell4, chr, dot, sign]; congr 1; omega
  have hfw (c : W 4) := fwht16_eq_transform v c
  rw [hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15] at hfw
  -- Express `m`, `eSZc`, `cSZ t` in terms of the 16 entries of `v` and `transform v`!
  let w0  : W 4 := (false, (false, (false, (false, ())))); let w1  : W 4 := (false, (false, (false, (true,  ()))))
  let w2  : W 4 := (false, (false, (true,  (false, ())))); let w3  : W 4 := (false, (false, (true,  (true,  ()))))
  let w4  : W 4 := (false, (true,  (false, (false, ())))); let w5  : W 4 := (false, (true,  (false, (true,  ()))))
  let w6  : W 4 := (false, (true,  (true,  (false, ())))); let w7  : W 4 := (false, (true,  (true,  (true,  ()))))
  let w8  : W 4 := (true,  (false, (false, (false, ())))); let w9  : W 4 := (true,  (false, (false, (true,  ()))))
  let w10 : W 4 := (true,  (false, (true,  (false, ())))); let w11 : W 4 := (true,  (false, (true,  (true,  ()))))
  let w12 : W 4 := (true,  (true,  (false, (false, ())))); let w13 : W 4 := (true,  (true,  (false, (true,  ()))))
  let w14 : W 4 := (true,  (true,  (true,  (false, ())))); let w15 : W 4 := (true,  (true,  (true,  (true,  ()))))
  have htot4 (F : W 4 → Int) :
      total 4 F =
      F w0 + F w1 + F w2 + F w3 + F w4 + F w5 + F w6 + F w7 +
      F w8 + F w9 + F w10 + F w11 + F w12 + F w13 + F w14 + F w15 := by
    dsimp only [total, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]; omega
  have hm_eq : total 4 (fun x => v x * v x) =
      v w0*v w0 + v w1*v w1 + v w2*v w2 + v w3*v w3 + v w4*v w4 + v w5*v w5 + v w6*v w6 + v w7*v w7 +
      v w8*v w8 + v w9*v w9 + v w10*v w10 + v w11*v w11 + v w12*v w12 + v w13*v w13 + v w14*v w14 + v w15*v w15 :=
    htot4 (fun x => v x * v x)
  have he_eq : total 4 (fun c => if !isSZ c then transform v c * transform v c else 0) =
      transform v w3*transform v w3 + transform v w4*transform v w4 + transform v w5*transform v w5 +
      transform v w6*transform v w6 + transform v w8*transform v w8 + transform v w9*transform v w9 +
      transform v w10*transform v w10 + transform v w12*transform v w12 + transform v w13*transform v w13 +
      transform v w14*transform v w14 := by
    rw [htot4]; dsimp [isSZ, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]; omega
  have hcSZ_eq (t : Int) : total 4 (fun s => if isSZ s && decide (transform v s * transform v s = t) then (1 : Int) else 0) =
      (if transform v w0*transform v w0 = t then 1 else 0) + (if transform v w1*transform v w1 = t then 1 else 0) +
      (if transform v w2*transform v w2 = t then 1 else 0) + (if transform v w7*transform v w7 = t then 1 else 0) +
      (if transform v w11*transform v w11 = t then 1 else 0) + (if transform v w15*transform v w15 = t then 1 else 0) := by
    rw [htot4]
    have hSZt : isSZ w0 = true ∧ isSZ w1 = true ∧ isSZ w2 = true ∧ isSZ w7 = true ∧ isSZ w11 = true ∧ isSZ w15 = true := by decide
    have hSZf : isSZ w3 = false ∧ isSZ w4 = false ∧ isSZ w5 = false ∧ isSZ w6 = false ∧ isSZ w8 = false ∧
                isSZ w9 = false ∧ isSZ w10 = false ∧ isSZ w12 = false ∧ isSZ w13 = false ∧ isSZ w14 = false := by decide
    simp only [hSZt.1, hSZt.2.1, hSZt.2.2.1, hSZt.2.2.2.1, hSZt.2.2.2.2.1, hSZt.2.2.2.2.2,
               hSZf.1, hSZf.2.1, hSZf.2.2.1, hSZf.2.2.2.1, hSZf.2.2.2.2.1, hSZf.2.2.2.2.2.1,
               hSZf.2.2.2.2.2.2.1, hSZf.2.2.2.2.2.2.2.1, hSZf.2.2.2.2.2.2.2.2.1, hSZf.2.2.2.2.2.2.2.2.2,
               Bool.true_and, Bool.false_and, Bool.false_eq_true, if_false, decide_eq_true_eq]
    omega
  -- Rewrite the 16 `v` and `z` entries inside `hfast` cleanly via `checkVec16` and `checkZ16`!
  unfold checkOneCellFast at hfast
  rw [← hv0, ← hv1, ← hv2, ← hv3, ← hv4, ← hv5, ← hv6, ← hv7,
      ← hv8, ← hv9, ← hv10, ← hv11, ← hv12, ← hv13, ← hv14, ← hv15] at hfast
  unfold checkVec16 at hfast
  have hz0  : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).1.1 = transform v w0 := fwht16_eq_transform v w0
  have hz1  : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).1.2.1 = transform v w1 := fwht16_eq_transform v w1
  have hz2  : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).1.2.2.1 = transform v w2 := fwht16_eq_transform v w2
  have hz3  : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).1.2.2.2 = transform v w3 := fwht16_eq_transform v w3
  have hz4  : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).2.1.1 = transform v w4 := fwht16_eq_transform v w4
  have hz5  : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).2.1.2.1 = transform v w5 := fwht16_eq_transform v w5
  have hz6  : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).2.1.2.2.1 = transform v w6 := fwht16_eq_transform v w6
  have hz7  : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).2.1.2.2.2 = transform v w7 := fwht16_eq_transform v w7
  have hz8  : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).2.2.1.1 = transform v w8 := fwht16_eq_transform v w8
  have hz9  : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).2.2.1.2.1 = transform v w9 := fwht16_eq_transform v w9
  have hz10 : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).2.2.1.2.2.1 = transform v w10 := fwht16_eq_transform v w10
  have hz11 : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).2.2.1.2.2.2 = transform v w11 := fwht16_eq_transform v w11
  have hz12 : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).2.2.2.1 = transform v w12 := fwht16_eq_transform v w12
  have hz13 : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).2.2.2.2.1 = transform v w13 := fwht16_eq_transform v w13
  have hz14 : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).2.2.2.2.2.1 = transform v w14 := fwht16_eq_transform v w14
  have hz15 : (fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15)).2.2.2.2.2.2 = transform v w15 := fwht16_eq_transform v w15
  have hfw_tup : fwht16 (v w0) (v w1) (v w2) (v w3) (v w4) (v w5) (v w6) (v w7) (v w8) (v w9) (v w10) (v w11) (v w12) (v w13) (v w14) (v w15) =
      ((transform v w0, transform v w1, transform v w2, transform v w3),
       (transform v w4, transform v w5, transform v w6, transform v w7),
       (transform v w8, transform v w9, transform v w10, transform v w11),
       (transform v w12, transform v w13, transform v w14, transform v w15)) := by
    apply Prod.ext
    · exact Prod.ext hz0 (Prod.ext hz1 (Prod.ext hz2 hz3))
    · apply Prod.ext
      · exact Prod.ext hz4 (Prod.ext hz5 (Prod.ext hz6 hz7))
      · apply Prod.ext
        · exact Prod.ext hz8 (Prod.ext hz9 (Prod.ext hz10 hz11))
        · exact Prod.ext hz12 (Prod.ext hz13 (Prod.ext hz14 hz15))
  rw [hfw_tup, ← hm_eq] at hfast
  unfold checkZ16 at hfast
  dsimp only at hfast
  rw [← he_eq] at hfast
  have hallSZc (P : Int → Prop) [DecidablePred P]
      (h : (((((((((decide (P (transform v w3*transform v w3)) = true ∧ decide (P (transform v w4*transform v w4)) = true) ∧
           decide (P (transform v w5*transform v w5)) = true) ∧ decide (P (transform v w6*transform v w6)) = true) ∧
           decide (P (transform v w8*transform v w8)) = true) ∧ decide (P (transform v w9*transform v w9)) = true) ∧
           decide (P (transform v w10*transform v w10)) = true) ∧ decide (P (transform v w12*transform v w12)) = true) ∧
           decide (P (transform v w13*transform v w13)) = true) ∧ decide (P (transform v w14*transform v w14)) = true))
      (c : W 4) (hc : isSZ c = false) : P (transform v c * transform v c) := by
    simp only [decide_eq_true_eq] at h
    rcases c with ⟨b0, b1, b2, b3, ⟨⟩⟩
    cases b0
    · cases b1
      · cases b2
        · cases b3
          · exact absurd hc (by decide)
          · exact absurd hc (by decide)
        · cases b3
          · exact absurd hc (by decide)
          · exact h.1.1.1.1.1.1.1.1.1
      · cases b2
        · cases b3
          · exact h.1.1.1.1.1.1.1.1.2
          · exact h.1.1.1.1.1.1.1.2
        · cases b3
          · exact h.1.1.1.1.1.1.2
          · exact absurd hc (by decide)
    · cases b1
      · cases b2
        · cases b3
          · exact h.1.1.1.1.1.2
          · exact h.1.1.1.1.2
        · cases b3
          · exact h.1.1.1.2
          · exact absurd hc (by decide)
      · cases b2
        · cases b3
          · exact h.1.1.2
          · exact h.1.2
        · cases b3
          · exact h.2
          · exact absurd hc (by decide)
  have hallSZ (P : Int → Prop) [DecidablePred P]
      (h : (((((decide (P (transform v w0*transform v w0)) = true ∧ decide (P (transform v w1*transform v w1)) = true) ∧
           decide (P (transform v w2*transform v w2)) = true) ∧ decide (P (transform v w7*transform v w7)) = true) ∧
           decide (P (transform v w11*transform v w11)) = true) ∧ decide (P (transform v w15*transform v w15)) = true))
      (s : W 4) (hs : isSZ s = true) : P (transform v s * transform v s) := by
    simp only [decide_eq_true_eq] at h
    rcases s with ⟨b0, b1, b2, b3, ⟨⟩⟩
    cases b0
    · cases b1
      · cases b2
        · cases b3
          · exact h.1.1.1.1.1
          · exact h.1.1.1.1.2
        · cases b3
          · exact h.1.1.1.2
          · exact absurd hs (by decide)
      · cases b2
        · cases b3
          · exact absurd hs (by decide)
          · exact absurd hs (by decide)
        · cases b3
          · exact absurd hs (by decide)
          · exact h.1.1.2
    · cases b1
      · cases b2
        · cases b3
          · exact absurd hs (by decide)
          · exact absurd hs (by decide)
        · cases b3
          · exact absurd hs (by decide)
          · exact h.1.2
      · cases b2
        · cases b3
          · exact absurd hs (by decide)
          · exact absurd hs (by decide)
        · cases b3
          · exact absurd hs (by decide)
          · exact h.2
  dsimp only
  constructor
  · intro hodd
    rw [if_pos hodd] at hfast
    simp only [Bool.and_eq_true] at hfast
    exact ⟨of_decide_eq_true hfast.1.1, of_decide_eq_true hfast.2, hallSZc (fun q => q = 9) hfast.1.2⟩
  · intro hev
    have hne : ¬ total 4 (fun x => v x * v x) % 2 = 1 := by omega
    rw [if_neg hne] at hfast
    simp only [Bool.and_eq_true] at hfast
    refine ⟨of_decide_eq_true hfast.1.1,
            hallSZc (fun q => q = 0 ∨ q = 36 ∨ q = 144) hfast.1.2,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hm0; have h2 := hfast.2; rw [hm0, if_pos rfl] at h2; simp only [Bool.and_eq_true] at h2
      exact ⟨of_decide_eq_true h2.1, hallSZ (fun q => q = 0) h2.2⟩
    · intro hm6; have h2 := hfast.2; rw [hm6, if_neg (by decide), if_pos rfl] at h2; simp only [Bool.and_eq_true] at h2
      exact ⟨of_decide_eq_true h2.1, hallSZ (fun q => q = 16) h2.2⟩
    · intro hm8; have h2 := hfast.2
      rw [hm8, if_neg (by decide), if_neg (by decide), if_pos rfl] at h2; simp only [Bool.and_eq_true] at h2
      exact ⟨of_decide_eq_true h2.1.1, hallSZ (fun q => q = 0 ∨ q = 64) h2.1.2, by rw [hcSZ_eq 64]; exact of_decide_eq_true h2.2⟩
    · intro hm10; have h2 := hfast.2
      rw [hm10, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl] at h2
      simp only [Bool.and_eq_true] at h2
      refine ⟨of_decide_eq_true h2.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1,
              hallSZ (fun q => q = 0 ∨ q = 4) h2.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
              by rw [hcSZ_eq 4]; exact of_decide_eq_true h2.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, ?_⟩
      intro s1 s2 hs1 hs2 hne12 hz1' hz2'
      have hp (a b w : Int) (ho : (!(decide (a = 0) && decide (b = 0)) || decide (w = 36)) = true)
          (ha : a = 0) (hb : b = 0) : w = 36 := by
        rw [decide_eq_true ha, decide_eq_true hb] at ho; simpa using ho
      have isSZ_cases (s : W 4) (hs : isSZ s = true) :
          s = w0 ∨ s = w1 ∨ s = w2 ∨ s = w7 ∨ s = w11 ∨ s = w15 := by
        rcases s with ⟨b0, b1, b2, b3, ⟨⟩⟩
        cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
          first | exact absurd hs (by decide) | exact Or.inl rfl | exact Or.inr (Or.inl rfl) |
                  exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl))) |
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) |
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      have p01 := h2.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      have p02 := h2.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      have p07 := h2.1.1.1.1.1.1.1.1.1.1.1.1.2
      have p011 := h2.1.1.1.1.1.1.1.1.1.1.1.2
      have p015 := h2.1.1.1.1.1.1.1.1.1.1.2
      have p12 := h2.1.1.1.1.1.1.1.1.1.2
      have p17 := h2.1.1.1.1.1.1.1.1.2
      have p111 := h2.1.1.1.1.1.1.1.2
      have p115 := h2.1.1.1.1.1.1.2
      have p27 := h2.1.1.1.1.1.2
      have p211 := h2.1.1.1.1.2
      have p215 := h2.1.1.1.2
      have p711 := h2.1.1.2
      have p715 := h2.1.2
      have p1115 := h2.2
      rcases isSZ_cases s1 hs1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases isSZ_cases s2 hs2 with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hne12
      · exact hp _ _ _ p01 hz1' hz2'
      · exact hp _ _ _ p02 hz1' hz2'
      · exact hp _ _ _ p07 hz1' hz2'
      · exact hp _ _ _ p011 hz1' hz2'
      · exact hp _ _ _ p015 hz1' hz2'
      · exact hp _ _ _ p01 hz2' hz1'
      · exact absurd rfl hne12
      · exact hp _ _ _ p12 hz1' hz2'
      · exact hp _ _ _ p17 hz1' hz2'
      · exact hp _ _ _ p111 hz1' hz2'
      · exact hp _ _ _ p115 hz1' hz2'
      · exact hp _ _ _ p02 hz2' hz1'
      · exact hp _ _ _ p12 hz2' hz1'
      · exact absurd rfl hne12
      · exact hp _ _ _ p27 hz1' hz2'
      · exact hp _ _ _ p211 hz1' hz2'
      · exact hp _ _ _ p215 hz1' hz2'
      · exact hp _ _ _ p07 hz2' hz1'
      · exact hp _ _ _ p17 hz2' hz1'
      · exact hp _ _ _ p27 hz2' hz1'
      · exact absurd rfl hne12
      · exact hp _ _ _ p711 hz1' hz2'
      · exact hp _ _ _ p715 hz1' hz2'
      · exact hp _ _ _ p011 hz2' hz1'
      · exact hp _ _ _ p111 hz2' hz1'
      · exact hp _ _ _ p211 hz2' hz1'
      · exact hp _ _ _ p711 hz2' hz1'
      · exact absurd rfl hne12
      · exact hp _ _ _ p1115 hz1' hz2'
      · exact hp _ _ _ p015 hz2' hz1'
      · exact hp _ _ _ p115 hz2' hz1'
      · exact hp _ _ _ p215 hz2' hz1'
      · exact hp _ _ _ p715 hz2' hz1'
      · exact hp _ _ _ p1115 hz2' hz1'
      · exact absurd rfl hne12
    · intro hm12; have h2 := hfast.2
      rw [hm12, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl] at h2
      simp only [Bool.and_eq_true] at h2
      exact ⟨of_decide_eq_true h2.1.1, hallSZ (fun q => q = 0 ∨ q = 16) h2.1.2, by rw [hcSZ_eq 16]; exact of_decide_eq_true h2.2⟩
    · intro hm16; have h2 := hfast.2
      rw [hm16, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)] at h2
      simp only [Bool.and_eq_true] at h2
      exact ⟨of_decide_eq_true h2.1.1, hallSZ (fun q => q = 0 ∨ q = 256) h2.1.2, by rw [hcSZ_eq 256]; exact of_decide_eq_true h2.2⟩

/-! ## Section 3: Two Pure-Algebra 4-Bit Spectral Lemmas (Killing `k = 6` and `k = 0`!) -/

/-- **Cubic Identity Lemma (`no_4twos_3fours_walsh8`, kills `k = 6` in 5 lines!)**:
    NO function `h : W 4 → Int` taking values `±2` on at most 4 points (`A`), `±4` on 3 distinct
    points (`t1, t2, t3`), and `0` elsewhere can satisfy `|transform h r| = 8` for all `r : W 4`! -/
private theorem no_4twos_3fours_walsh8 (gA : W 4 → Int) (t1 t2 t3 : W 4) (e1 e2 e3 : Int)
    (he1 : e1 = 1 ∨ e1 = -1) (he2 : e2 = 1 ∨ e2 = -1) (he3 : e3 = 1 ∨ e3 = -1)
    (hgA_val : ∀ x : W 4, gA x = -1 ∨ gA x = 0 ∨ gA x = 1)
    (hgA_cnt : total 4 (fun x => gA x * gA x) = 4)
    (hspec : ∀ r : W 4,
      let u := e1 * chr t1 r + e2 * chr t2 r + e3 * chr t3 r
      transform gA r + 2 * u = 4 ∨ transform gA r + 2 * u = -4) : False := by
  have hgA_bdd (r : W 4) : -4 ≤ transform gA r ∧ transform gA r ≤ 4 := by
    have h1 (x : W 4) : -(gA x * gA x) ≤ gA x * chr r x ∧ gA x * chr r x ≤ gA x * gA x := by
      have hc : chr r x = 1 ∨ chr r x = -1 := sign_vals _
      rcases hgA_val x with h | h | h <;> rcases hc with c | c <;> rw [h, c] <;> decide
    have hlo := total_mono 4 (fun x => -(gA x * gA x)) (fun x => gA x * chr r x) (fun x => (h1 x).1)
    have hhi := total_mono 4 (fun x => gA x * chr r x) (fun x => gA x * gA x) (fun x => (h1 x).2)
    have hneg : total 4 (fun x => -(gA x * gA x)) = -total 4 (fun x => gA x * gA x) := by
      have h : (fun x => -(gA x * gA x)) = fun x => (-1 : Int) * (gA x * gA x) := funext (fun x => by omega)
      rw [h, total_scale]; omega
    rw [hneg, hgA_cnt] at hlo; rw [hgA_cnt] at hhi
    exact ⟨hlo, hhi⟩
  -- The 3-line cubic identity: `transform gA r = -2 * e1 * e2 * e3 * chr (t1 ⊕ t2 ⊕ t3) r` for ALL `r : W 4`!
  let t123 : W 4 := add 4 t1 (add 4 t2 t3)
  have htr_exact (r : W 4) : transform gA r = -2 * (e1 * e2 * e3) * chr t123 r := by
    have hchr : chr t123 r = chr t1 r * (chr t2 r * chr t3 r) := by
      dsimp only [t123]
      have hsym (a : W 4) : chr a r = chr r a := by unfold chr; rw [dot_comm]
      rw [hsym, hsym t1, hsym t2, hsym t3, Balanced242Plateau.chr_add, Balanced242Plateau.chr_add]
    rw [hchr]
    have hsp := hspec r; dsimp only at hsp
    have ⟨hlo, hhi⟩ := hgA_bdd r
    have c1 : chr t1 r = 1 ∨ chr t1 r = -1 := sign_vals _
    have c2 : chr t2 r = 1 ∨ chr t2 r = -1 := sign_vals _
    have c3 : chr t3 r = 1 ∨ chr t3 r = -1 := sign_vals _
    rcases he1 with a | a <;> rcases he2 with b | b <;> rcases he3 with c | c <;>
    rcases c1 with d | d <;> rcases c2 with e | e <;> rcases c3 with f | f <;>
      rw [a, b, c, d, e, f] at hsp ⊢ <;> omega
  -- Walsh inversion at `t123` gives `16 * gA t123 = 16 * (-2 * e1 * e2 * e3) = ±32`, so `|gA t123| = 2`, impossible!
  have hinv := transform_involution gA t123
  have hm4 : many 4 = 16 := by decide
  rw [hm4] at hinv
  have hsum : transform (transform gA) t123 = 16 * (-2 * (e1 * e2 * e3)) := by
    change total 4 (fun r => transform gA r * chr t123 r) = _
    have hpt (r : W 4) : transform gA r * chr t123 r = -2 * (e1 * e2 * e3) := by
      rw [htr_exact r, Int.mul_assoc, show chr t123 r * chr t123 r = 1 from sign_sq _, Int.mul_one]
    rw [funext hpt, total_const, hm4]
  rw [hsum] at hinv
  rcases hgA_val t123 with h | h | h <;> rcases he1 with a | a <;> rcases he2 with b | b <;> rcases he3 with c | c <;>
    rw [h, a, b, c] at hinv <;> omega

/-- **4-Pair Walsh Square Lemma (`four_dpairs_xor_in_0d`, kills `k = 0` in 10 lines!)**:
    If 4 points `x1, x2, x3, x4 : W 4` belong to 4 distinct `d`-pairs (`x_i ⊕ x_j ∉ {0, d}` for `i ≠ j`)
    and `s1..s4 ∈ {±1}` satisfy `(s1 chr x1 r + ... + s4 chr x4 r)^2 = 4` for all `r : W 4` with
    `chr d r = eps` (`eps ∈ {±1}`), then `x1 ⊕ x2 ⊕ x3 ⊕ x4 ∈ {zero 4, d}`! -/
private theorem four_dpairs_xor_in_0d (d x1 x2 x3 x4 : W 4) (eps s1 s2 s3 s4 : Int)
    (hd_ne : d ≠ zero 4) (heps : eps = 1 ∨ eps = -1)
    (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1)
    (hs3 : s3 = 1 ∨ s3 = -1) (hs4 : s4 = 1 ∨ s4 = -1)
    (h12 : add 4 x1 x2 ≠ zero 4 ∧ add 4 x1 x2 ≠ d)
    (h13 : add 4 x1 x3 ≠ zero 4 ∧ add 4 x1 x3 ≠ d)
    (h14 : add 4 x1 x4 ≠ zero 4 ∧ add 4 x1 x4 ≠ d)
    (h23 : add 4 x2 x3 ≠ zero 4 ∧ add 4 x2 x3 ≠ d)
    (h24 : add 4 x2 x4 ≠ zero 4 ∧ add 4 x2 x4 ≠ d)
    (h34 : add 4 x3 x4 ≠ zero 4 ∧ add 4 x3 x4 ≠ d)
    (hsq : ∀ r : W 4, chr d r = eps →
      (s1 * chr x1 r + s2 * chr x2 r + s3 * chr x3 r + s4 * chr x4 r) *
      (s1 * chr x1 r + s2 * chr x2 r + s3 * chr x3 r + s4 * chr x4 r) = 4) :
    add 4 (add 4 x1 x2) (add 4 x3 x4) = zero 4 ∨ add 4 (add 4 x1 x2) (add 4 x3 x4) = d := by
  by_cases hgoal : add 4 (add 4 x1 x2) (add 4 x3 x4) = zero 4 ∨ add 4 (add 4 x1 x2) (add 4 x3 x4) = d
  · exact hgoal
  · exfalso
    have hnot0 : add 4 (add 4 x1 x2) (add 4 x3 x4) ≠ zero 4 := fun h => hgoal (Or.inl h)
    have hnotd : add 4 (add 4 x1 x2) (add 4 x3 x4) ≠ d := fun h => hgoal (Or.inr h)
    -- Define the 6 pair characters `P_ij(r) = s_i s_j chr(x_i ⊕ x_j) r`.
    -- On `chr d r = eps`, `S(r) := P12 + P13 + P14 + P23 + P24 + P34 = 0`!
    let p12 := add 4 x1 x2; let p13 := add 4 x1 x3; let p14 := add 4 x1 x4
    let p23 := add 4 x2 x3; let p24 := add 4 x2 x4; let p34 := add 4 x3 x4
    let S (r : W 4) : Int :=
      s1 * s2 * chr p12 r + s1 * s3 * chr p13 r + s1 * s4 * chr p14 r +
      s2 * s3 * chr p23 r + s2 * s4 * chr p24 r + s3 * s4 * chr p34 r
    have hS0 (r : W 4) : (1 + eps * chr d r) * (S r * S r) = 0 := by
      have hcd : chr d r = 1 ∨ chr d r = -1 := sign_vals _
      by_cases he : chr d r = eps
      · have hq := hsq r he
        have hc (a b : W 4) : chr (add 4 a b) r = chr a r * chr b r := by
          have hsym (u : W 4) : chr u r = chr r u := by unfold chr; rw [dot_comm]
          rw [hsym, hsym a, hsym b, Balanced242Plateau.chr_add]
        have hS_eq : 2 * S r =
            (s1 * chr x1 r + s2 * chr x2 r + s3 * chr x3 r + s4 * chr x4 r) *
            (s1 * chr x1 r + s2 * chr x2 r + s3 * chr x3 r + s4 * chr x4 r) - 4 := by
          dsimp only [S, p12, p13, p14, p23, p24, p34]
          rw [hc x1 x2, hc x1 x3, hc x1 x4, hc x2 x3, hc x2 x4, hc x3 x4]
          have c1 : chr x1 r = 1 ∨ chr x1 r = -1 := sign_vals _
          have c2 : chr x2 r = 1 ∨ chr x2 r = -1 := sign_vals _
          have c3 : chr x3 r = 1 ∨ chr x3 r = -1 := sign_vals _
          have c4 : chr x4 r = 1 ∨ chr x4 r = -1 := sign_vals _
          rcases hs1 with a | a <;> rcases hs2 with b | b <;> rcases hs3 with c | c <;> rcases hs4 with e | e <;>
          rcases c1 with f | f <;> rcases c2 with g | g <;> rcases c3 with h | h <;> rcases c4 with i | i <;>
            rw [a, b, c, e, f, g, h, i] <;> decide
        have hSr0 : S r = 0 := by omega
        rw [hSr0]; simp
      · have h0 : 1 + eps * chr d r = 0 := by
          rcases heps with a | a <;> rcases hcd with b | b <;> rw [a, b] at he ⊢ <;> omega
        rw [h0, Int.zero_mul]
    -- Helper: `total 4 (fun r => (1 + eps * chr d r) * (chr a r * chr b r))` = `16` if `a = b`, `0` if `a ⊕ b ∉ {0, d}`!
    have hpair_int (a b : W 4) (h0 : add 4 a b ≠ zero 4) (hd : add 4 a b ≠ d) :
        total 4 (fun r => (1 + eps * chr d r) * (chr a r * chr b r)) = 0 := by
      have hpt (r : W 4) : (1 + eps * chr d r) * (chr a r * chr b r) =
          chr (add 4 a b) r + eps * chr (add 4 d (add 4 a b)) r := by
        have hsym (u : W 4) : chr u r = chr r u := by unfold chr; rw [dot_comm]
        rw [hsym (add 4 a b), hsym (add 4 d (add 4 a b)), hsym a, hsym b, hsym d,
            Balanced242Plateau.chr_add, Balanced242Plateau.chr_add, Balanced242Plateau.chr_add]
        rw [Int.add_mul, Int.one_mul, Int.mul_assoc]
      rw [funext hpt, total_add, total_scale]
      have hi1 : total 4 (chr (add 4 a b)) = 0 := by
        have h := identity_spectrum 4 (add 4 a b); change total 4 (chr (add 4 a b)) = _ at h; rw [h]; simp [h0]
      have hne_dab : add 4 d (add 4 a b) ≠ zero 4 := by
        intro hz; apply hd; have h := congrArg (add 4 d) hz
        rw [← Balanced242Plateau.add_assoc', add_self, add_zero_left, add_zero_right] at h; exact h
      have hi2 : total 4 (chr (add 4 d (add 4 a b))) = 0 := by
        have h := identity_spectrum 4 (add 4 d (add 4 a b))
        change total 4 (chr (add 4 d (add 4 a b))) = _ at h; rw [h]; simp [hne_dab]
      rw [hi1, hi2]; omega
    have hdiag_int (a : W 4) (hd : d ≠ zero 4) :
        total 4 (fun r => (1 + eps * chr d r) * (chr a r * chr a r)) = 16 := by
      have hpt (r : W 4) : (1 + eps * chr d r) * (chr a r * chr a r) = 1 + eps * chr d r := by
        rw [show chr a r * chr a r = 1 from sign_sq _, Int.mul_one]
      rw [funext hpt, total_add, total_const, total_scale]
      have hi : total 4 (chr d) = 0 := by
        have h := identity_spectrum 4 d; change total 4 (chr d) = _ at h; rw [h]; simp [hd]
      have hm4 : many 4 = 16 := by decide
      rw [hm4, hi]; omega
    -- Every pair `(p_ij, p_kl)` with `{i,j} ≠ {k,l}` has `p_ij ⊕ p_kl ∉ {0, d}`!
    have hxor_comm4 (a b c e : W 4) : add 4 (add 4 a b) (add 4 c e) = add 4 (add 4 a c) (add 4 b e) := by
      rw [Balanced242Plateau.add_assoc', ← Balanced242Plateau.add_assoc' 4 b c e,
          add_comm 4 b c, Balanced242Plateau.add_assoc' 4 c b e, ← Balanced242Plateau.add_assoc']
    have hxor_cancel (a b c : W 4) : add 4 (add 4 a b) (add 4 a c) = add 4 b c := by
      rw [hxor_comm4 a b a c, add_self, add_zero_left]
    -- Compute `total 4 (fun r => (1 + eps * chr d r) * (S r * S r))` = `6 * 16 = 96`, contradicting `0`!
    have hzero : total 4 (fun r => (1 + eps * chr d r) * (S r * S r)) = 0 := by
      rw [funext hS0, total_zero]
    -- Expand `(a1 + a2 + a3 + a4 + a5 + a6)^2` into 6 diagonal + 15 double cross terms!
    let t12 (r : W 4) := s1 * s2 * chr p12 r
    let t13 (r : W 4) := s1 * s3 * chr p13 r
    let t14 (r : W 4) := s1 * s4 * chr p14 r
    let t23 (r : W 4) := s2 * s3 * chr p23 r
    let t24 (r : W 4) := s2 * s4 * chr p24 r
    let t34 (r : W 4) := s3 * s4 * chr p34 r
    have hsq_exp (r : W 4) : (1 + eps * chr d r) * (S r * S r) =
        (1 + eps * chr d r) * (t12 r * t12 r) + (1 + eps * chr d r) * (t13 r * t13 r) +
        (1 + eps * chr d r) * (t14 r * t14 r) + (1 + eps * chr d r) * (t23 r * t23 r) +
        (1 + eps * chr d r) * (t24 r * t24 r) + (1 + eps * chr d r) * (t34 r * t34 r) +
        2 * ((1 + eps * chr d r) * (t12 r * t13 r) + (1 + eps * chr d r) * (t12 r * t14 r) +
             (1 + eps * chr d r) * (t12 r * t23 r) + (1 + eps * chr d r) * (t12 r * t24 r) +
             (1 + eps * chr d r) * (t12 r * t34 r) + (1 + eps * chr d r) * (t13 r * t14 r) +
             (1 + eps * chr d r) * (t13 r * t23 r) + (1 + eps * chr d r) * (t13 r * t24 r) +
             (1 + eps * chr d r) * (t13 r * t34 r) + (1 + eps * chr d r) * (t14 r * t23 r) +
             (1 + eps * chr d r) * (t14 r * t24 r) + (1 + eps * chr d r) * (t14 r * t34 r) +
             (1 + eps * chr d r) * (t23 r * t24 r) + (1 + eps * chr d r) * (t23 r * t34 r) +
             (1 + eps * chr d r) * (t24 r * t34 r)) := by
      dsimp only [S, t12, t13, t14, t23, t24, t34]
      generalize 1 + eps * chr d r = w
      generalize s1 * s2 * chr p12 r = a; generalize s1 * s3 * chr p13 r = b
      generalize s1 * s4 * chr p14 r = c; generalize s2 * s3 * chr p23 r = e
      generalize s2 * s4 * chr p24 r = f; generalize s3 * s4 * chr p34 r = g
      have h1 : (a + b + c + e + f + g) * (a + b + c + e + f + g) =
          a * a + b * b + c * c + e * e + f * f + g * g +
          2 * (a * b + a * c + a * e + a * f + a * g + b * c + b * e + b * f + b * g +
               c * e + c * f + c * g + e * f + e * g + f * g) := by
        simp only [Int.add_mul, Int.mul_add]
        rw [Int.mul_comm b a, Int.mul_comm c a, Int.mul_comm e a, Int.mul_comm f a, Int.mul_comm g a,
            Int.mul_comm c b, Int.mul_comm e b, Int.mul_comm f b, Int.mul_comm g b,
            Int.mul_comm e c, Int.mul_comm f c, Int.mul_comm g c,
            Int.mul_comm f e, Int.mul_comm g e, Int.mul_comm g f]
        omega
      rw [h1]; simp only [Int.mul_add, Int.mul_left_comm]
    have hdiag_t (si sj : Int) (hsi : si = 1 ∨ si = -1) (hsj : sj = 1 ∨ sj = -1) (p : W 4) :
        total 4 (fun r => (1 + eps * chr d r) * ((si * sj * chr p r) * (si * sj * chr p r))) = 16 := by
      have h1 : ∀ r, (1 + eps * chr d r) * ((si * sj * chr p r) * (si * sj * chr p r)) =
          (1 + eps * chr d r) * (chr p r * chr p r) := by
        intro r; rcases hsi with a | a <;> rcases hsj with b | b <;> rw [a, b] <;> simp [Int.mul_assoc]
      rw [funext h1]; exact hdiag_int p hd_ne
    have hcross_t (c1 c2 : Int) (pa pb : W 4) (h0 : add 4 pa pb ≠ zero 4) (hd : add 4 pa pb ≠ d) :
        total 4 (fun r => (1 + eps * chr d r) * ((c1 * chr pa r) * (c2 * chr pb r))) = 0 := by
      have h1 : ∀ r, (1 + eps * chr d r) * ((c1 * chr pa r) * (c2 * chr pb r)) =
          (c1 * c2) * ((1 + eps * chr d r) * (chr pa r * chr pb r)) := fun r => by ac_rfl
      rw [funext h1, total_scale, hpair_int pa pb h0 hd, Int.mul_zero]
    rw [funext hsq_exp] at hzero
    simp only [total_add, total_scale] at hzero
    dsimp only [t12, t13, t14, t23, t24, t34] at hzero
    rw [hdiag_t s1 s2 hs1 hs2 p12, hdiag_t s1 s3 hs1 hs3 p13, hdiag_t s1 s4 hs1 hs4 p14,
        hdiag_t s2 s3 hs2 hs3 p23, hdiag_t s2 s4 hs2 hs4 p24, hdiag_t s3 s4 hs3 hs4 p34] at hzero
    have hne_12_13 : add 4 p12 p13 ≠ zero 4 ∧ add 4 p12 p13 ≠ d := by dsimp only [p12, p13]; rw [hxor_cancel]; exact h23
    have hne_12_14 : add 4 p12 p14 ≠ zero 4 ∧ add 4 p12 p14 ≠ d := by dsimp only [p12, p14]; rw [hxor_cancel]; exact h24
    have hne_12_23 : add 4 p12 p23 ≠ zero 4 ∧ add 4 p12 p23 ≠ d := by dsimp only [p12, p23]; rw [add_comm 4 x1 x2, hxor_cancel]; exact h13
    have hne_12_24 : add 4 p12 p24 ≠ zero 4 ∧ add 4 p12 p24 ≠ d := by dsimp only [p12, p24]; rw [add_comm 4 x1 x2, hxor_cancel]; exact h14
    have hne_12_34 : add 4 p12 p34 ≠ zero 4 ∧ add 4 p12 p34 ≠ d := ⟨hnot0, hnotd⟩
    have hne_13_14 : add 4 p13 p14 ≠ zero 4 ∧ add 4 p13 p14 ≠ d := by dsimp only [p13, p14]; rw [hxor_cancel]; exact h34
    have hne_13_23 : add 4 p13 p23 ≠ zero 4 ∧ add 4 p13 p23 ≠ d := by dsimp only [p13, p23]; rw [add_comm 4 x1 x3, add_comm 4 x2 x3, hxor_cancel]; exact h12
    have hne_13_24 : add 4 p13 p24 ≠ zero 4 ∧ add 4 p13 p24 ≠ d := by dsimp only [p13, p24]; rw [hxor_comm4]; exact ⟨hnot0, hnotd⟩
    have hne_13_34 : add 4 p13 p34 ≠ zero 4 ∧ add 4 p13 p34 ≠ d := by dsimp only [p13, p34]; rw [add_comm 4 x1 x3, hxor_cancel]; exact h14
    have hne_14_23 : add 4 p14 p23 ≠ zero 4 ∧ add 4 p14 p23 ≠ d := by dsimp only [p14, p23]; rw [hxor_comm4, add_comm 4 x4 x3]; exact ⟨hnot0, hnotd⟩
    have hne_14_24 : add 4 p14 p24 ≠ zero 4 ∧ add 4 p14 p24 ≠ d := by dsimp only [p14, p24]; rw [add_comm 4 x1 x4, add_comm 4 x2 x4, hxor_cancel]; exact h12
    have hne_14_34 : add 4 p14 p34 ≠ zero 4 ∧ add 4 p14 p34 ≠ d := by dsimp only [p14, p34]; rw [add_comm 4 x1 x4, add_comm 4 x3 x4, hxor_cancel]; exact h13
    have hne_23_24 : add 4 p23 p24 ≠ zero 4 ∧ add 4 p23 p24 ≠ d := by dsimp only [p23, p24]; rw [hxor_cancel]; exact h34
    have hne_23_34 : add 4 p23 p34 ≠ zero 4 ∧ add 4 p23 p34 ≠ d := by dsimp only [p23, p34]; rw [add_comm 4 x2 x3, hxor_cancel]; exact h24
    have hne_24_34 : add 4 p24 p34 ≠ zero 4 ∧ add 4 p24 p34 ≠ d := by dsimp only [p24, p34]; rw [add_comm 4 x2 x4, add_comm 4 x3 x4, hxor_cancel]; exact h23
    rw [hcross_t _ _ p12 p13 hne_12_13.1 hne_12_13.2, hcross_t _ _ p12 p14 hne_12_14.1 hne_12_14.2,
        hcross_t _ _ p12 p23 hne_12_23.1 hne_12_23.2, hcross_t _ _ p12 p24 hne_12_24.1 hne_12_24.2,
        hcross_t _ _ p12 p34 hne_12_34.1 hne_12_34.2, hcross_t _ _ p13 p14 hne_13_14.1 hne_13_14.2,
        hcross_t _ _ p13 p23 hne_13_23.1 hne_13_23.2, hcross_t _ _ p13 p24 hne_13_24.1 hne_13_24.2,
        hcross_t _ _ p13 p34 hne_13_34.1 hne_13_34.2, hcross_t _ _ p14 p23 hne_14_23.1 hne_14_23.2,
        hcross_t _ _ p14 p24 hne_14_24.1 hne_14_24.2, hcross_t _ _ p14 p34 hne_14_34.1 hne_14_34.2,
        hcross_t _ _ p23 p24 hne_23_24.1 hne_23_24.2, hcross_t _ _ p23 p34 hne_23_34.1 hne_23_34.2,
        hcross_t _ _ p24 p34 hne_24_34.1 hne_24_34.2] at hzero
    omega

/-! ## Section 4: Symplectic Decomposition & Main Theorem `no_t112` -/

private def lin4 (u1 v1 u2 v2 : W 8) (c : W 4) : W 8 :=
  add 8 (if c.1 then u1 else zero 8)
    (add 8 (if c.2.1 then v1 else zero 8)
      (add 8 (if c.2.2.1 then u2 else zero 8)
             (if c.2.2.2.1 then v2 else zero 8)))

private theorem lin4_add (u1 v1 u2 v2 : W 8) (a b : W 4) :
    lin4 u1 v1 u2 v2 (add 4 a b) = add 8 (lin4 u1 v1 u2 v2 a) (lin4 u1 v1 u2 v2 b) := by
  rcases a with ⟨a0, a1, a2, a3, ⟨⟩⟩
  rcases b with ⟨b0, b1, b2, b3, ⟨⟩⟩
  have hadd4 : add 4 (a0, (a1, (a2, (a3, ())))) (b0, (b1, (b2, (b3, ())))) =
      (xor a0 b0, (xor a1 b1, (xor a2 b2, (xor a3 b3, ())))) := rfl
  rw [hadd4]; dsimp only [lin4]
  have step (p q : Bool) (w : W 8) :
      (if xor p q then w else zero 8) = add 8 (if p then w else zero 8) (if q then w else zero 8) := by
    cases p <;> cases q <;> simp [add_zero_left, add_zero_right, add_self]
  rw [step a0 b0 u1, step a1 b1 v1, step a2 b2 u2, step a3 b3 v2]
  have sh (w1 w2 w3 w4 : W 8) :
      add 8 (add 8 w1 w2) (add 8 w3 w4) = add 8 (add 8 w1 w3) (add 8 w2 w4) := by
    rw [Balanced242Plateau.add_assoc', ← Balanced242Plateau.add_assoc' 8 w2 w3 w4,
        add_comm 8 w2 w3, Balanced242Plateau.add_assoc' 8 w3 w2 w4, ← Balanced242Plateau.add_assoc']
  rw [sh (if a2 then u2 else zero 8) (if b2 then u2 else zero 8)
         (if a3 then v2 else zero 8) (if b3 then v2 else zero 8),
      sh (if a1 then v1 else zero 8) (if b1 then v1 else zero 8),
      sh (if a0 then u1 else zero 8) (if b0 then u1 else zero 8)]

private theorem lin4_zero (u1 v1 u2 v2 : W 8) : lin4 u1 v1 u2 v2 (zero 4) = zero 8 := by
  change add 8 (if false then u1 else zero 8) (add 8 (if false then v1 else zero 8)
    (add 8 (if false then u2 else zero 8) (if false then v2 else zero 8))) = zero 8
  simp [add_zero_left]

private theorem ell_symm {n : Nat} (β : W n → Bool) (a b : W n) : ell β a b = ell β b a := by
  unfold ell; rw [add_comm n b a]
  generalize β a = x1; generalize β b = x2; generalize β (add n a b) = x3; generalize β (zero n) = x0
  revert x1 x2 x3 x0; decide

private theorem ell_self {n : Nat} (β : W n → Bool) (a : W n) : ell β a a = false := by
  unfold ell; rw [add_self]
  generalize β a = x1; generalize β (zero n) = x0
  revert x1 x0; decide

private theorem ell_zero {n : Nat} (β : W n → Bool) (a : W n) : ell β a (zero n) = false := by
  unfold ell; rw [add_zero_left]
  generalize β a = x1; generalize β (zero n) = x0
  revert x1 x0; decide

/-- Extract a 4-element symplectic complement `(u1, v1, u2, v2)` AND a 4-element basis
    `(r0, r1, r2, r3)` of `rad(β8)` for ANY rank-4 `Zc = 96` quadratic phase `Q = !Zset`! -/
private theorem rank4_Z96_symplectic_decomp (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (hrr : rr (β8 f g) = 16) (hZc : Zc f g = 96) :
    ∃ u1 v1 u2 v2 r0 r1 r2 r3 d0 d1 d2 d3 : W 8,
      (∀ c r : W 4, Zset f g (add 8 (lin4 u1 v1 u2 v2 c) (lin4 r0 r1 r2 r3 r)) = isSZ c) ∧
      (∀ r : W 4, rad (β8 f g) (lin4 r0 r1 r2 r3 r) = true) ∧
      (∀ x : W 8, ∃ p : W 4 × W 4, x = add 8 (lin4 u1 v1 u2 v2 p.1) (lin4 r0 r1 r2 r3 p.2) ∧
        ∀ p' : W 4 × W 4, x = add 8 (lin4 u1 v1 u2 v2 p'.1) (lin4 r0 r1 r2 r3 p'.2) → p' = p) ∧
      (∀ c x : W 4, dot 8 (lin4 u1 v1 u2 v2 c) (lin4 d0 d1 d2 d3 x) = dot 4 c x) ∧
      (∀ r x : W 4, dot 8 (lin4 r0 r1 r2 r3 r) (lin4 d0 d1 d2 d3 x) = false) ∧
      (∀ r y : W 4, dot 8 (lin4 r0 r1 r2 r3 r) (lin4 u1 v1 u2 v2 y) = false ∨ True) := by
  -- Note: even simpler! Instead of requiring `d_i` to be orthogonal to `r_j` AND picking an
  -- arbitrary basis `y_j` of `W 8 / R^⊥`, we pick `r0..r3` spanning `R` (so `lin4 r0 r1 r2 r3 : W 4 → R`
  -- is bijective onto `R`) AND dual vectors `e0..e3` for `R` (`dot r_i e_j = δ_ij`, `dot u_k e_j = 0`)!
  -- Let's construct `(u1, v1, u2, v2)` first via `ell (β8 f g)`.
  let Q (a : W 8) : Bool := !Zset f g a
  have hQ0 : Q (zero 8) = false := by simp [Q, Zset, dc]
  have hZe (a : W 8) : Q a = xor (xor (β8 f g a) (β8 f g (zero 8))) (dot 8 (supportXor g) a) := by
    have hc := Balanced242HighSections.coupled_phase f g a
    rw [dc] at hc
    have r1 := res a; have r0 := res (zero 8); have l1 := lores a
    dsimp only [Q]; unfold Zset β8 Balanced242Plateau.bt H8
    rw [dot_comm 8 (supportXor g) a]
    cases hd : dot 8 a (supportXor g) <;> simp only [hd, if_true, Bool.false_eq_true, if_false] at hc <;>
    by_cases h1 : hi f g a / 4 / 2 % 2 = 1 <;> by_cases h0 : hi f g (zero 8) / 4 / 2 % 2 = 1 <;>
      by_cases hl : lo f g a % 16 = 0 <;> simp [h1, h0, hl] <;> omega
  -- Polar form of `Q` equals `ell (β8 f g)`!
  have hQ_pol (a b : W 8) : xor (xor (Q (add 8 a b)) (Q a)) (Q b) = ell (β8 f g) a b := by
    rw [hZe, hZe, hZe, dot_right]; unfold ell; rw [add_comm 8 b a]
    generalize β8 f g (add 8 a b) = x1; generalize β8 f g a = x2
    generalize β8 f g b = x3; generalize β8 f g (zero 8) = x0
    generalize dot 8 (supportXor g) a = da; generalize dot 8 (supportXor g) b = db
    revert x1 x2 x3 x0 da db; decide
  have hQ_rad (w : W 8) (hw : rad (β8 f g) w = true) (a : W 8) : Q (add 8 a w) = xor (Q a) (Q w) := by
    have hel : ell (β8 f g) a w = false := by
      have h1 := (Balanced242Rank.all_spec (p := fun x => !ell (β8 f g) w x)).mp hw a
      rw [ell_symm] at h1
      cases h2 : ell (β8 f g) a w <;> rw [h2] at h1 <;> simp at h1 ⊢
    have hp := hQ_pol a w; rw [hel] at hp
    cases h1 : Q (add 8 a w) <;> cases h2 : Q a <;> cases h3 : Q w <;> rw [h1, h2, h3] at hp <;> simp at hp ⊢
  -- Crucial: `Q w = false` for EVERY `w ∈ rad (β8 f g)` (since `Zc = 96 ≠ 128`, `good (β8 f g) (supportXor g) = true`!)
  have hQ_on_rad (w : W 8) (hw : rad (β8 f g) w = true) : Q w = false := by
    have hgood : good (β8 f g) (supportXor g) = true := by
      cases hg : good (β8 f g) (supportXor g)
      · exfalso
        have hm8 : many 8 = 256 := by decide
        have hMM : 64 * 64 = many 8 * rr (β8 f g) := by rw [hm8, hrr]; decide
        have h0 := (Balanced242Rank.spec_values (β8 f g) (cube8 f g res) 64 hMM (supportXor g)).2 hg
        change transform (q8 f g) (supportXor g) = 0 at h0
        have hz := Z_identity f g res dc lores
        rw [h0, Int.mul_zero] at hz; omega
      · rfl
    have hphi := (Balanced242Rank.all_spec (p := fun e => !(rad (β8 f g) e && phi (β8 f g) (supportXor g) e))).mp hgood w
    rw [hw, Bool.true_and] at hphi
    have hp0 : phi (β8 f g) (supportXor g) w = false := by
      cases h : phi (β8 f g) (supportXor g) w <;> rw [h] at hphi <;> simp at hphi ⊢
    rw [hZe w]; unfold phi at hp0
    generalize β8 f g w = xa at hp0 ⊢; generalize β8 f g (zero 8) = xb at hp0 ⊢
    generalize dot 8 (supportXor g) w = xc at hp0 ⊢
    cases xa <;> cases xb <;> cases xc <;> simp at hp0 ⊢
  have hZ_rad_inv (a w : W 8) (hw : rad (β8 f g) w = true) : Zset f g (add 8 a w) = Zset f g a := by
    have h1 := hQ_rad w hw a; rw [hQ_on_rad w hw, Bool.xor_false] at h1
    dsimp only [Q] at h1
    generalize Zset f g (add 8 a w) = b1 at h1 ⊢; generalize Zset f g a = b2 at h1 ⊢
    cases b1 <;> cases b2 <;> simp at h1 ⊢
  -- Step A: Pick first symplectic pair `(a1, b1)` with `ell a1 b1 = true` (exists since `rr = 16 < 256`!).
  have hex_pair1 : ∃ a1 b1 : W 8, ell (β8 f g) a1 b1 = true := by
    cases h : (worlds 8).all (fun a => rad (β8 f g) a)
    · obtain ⟨a1, _, ha1⟩ := all_false_exists _ _ h
      unfold rad at ha1
      obtain ⟨b1, _, hb1⟩ := all_false_exists _ _ ha1
      exact ⟨a1, b1, by cases he : ell (β8 f g) a1 b1 <;> rw [he] at hb1 <;> simp at hb1 ⊢⟩
    · exfalso; rw [List.all_eq_true] at h
      have h256 : rr (β8 f g) = 256 := by
        unfold rr; have h1 : (fun a => bind (rad (β8 f g) a)) = fun _ => (1 : Int) :=
          funext (fun a => by rw [h a (all_worlds 8 a)]; rfl)
        rw [h1, total_const]; decide
      omega
  obtain ⟨a1, b1, hab1⟩ := hex_pair1
  -- Project `x ↦ proj1 x := x ⊕ (ell b1 x)*a1 ⊕ (ell a1 x)*b1` onto `{a1, b1}^⊥`!
  let proj1 (x : W 8) : W 8 :=
    add 8 x (add 8 (if ell (β8 f g) b1 x then a1 else zero 8)
                   (if ell (β8 f g) a1 x then b1 else zero 8))
  have hproj1_orth (x : W 8) : ell (β8 f g) a1 (proj1 x) = false ∧ ell (β8 f g) b1 (proj1 x) = false := by
    have hl1 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) a1
    have hl2 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) b1
    have hs1 := ell_self (β8 f g) a1
    have hs2 := ell_self (β8 f g) b1
    have hba : ell (β8 f g) b1 a1 = true := by rw [ell_symm]; exact hab1
    dsimp only [proj1]
    constructor
    · rw [hl1, hl1]
      cases h1 : ell (β8 f g) b1 x <;> cases h2 : ell (β8 f g) a1 x <;>
        simp [hs1, hab1, ell_zero]
    · rw [hl2, hl2]
      cases h1 : ell (β8 f g) b1 x <;> cases h2 : ell (β8 f g) a1 x <;>
        simp [hs2, hba, ell_zero]
  -- Step B: Pick second symplectic pair `(a2, b2)` inside `{a1, b1}^⊥` (`proj1` image!) with `ell a2 b2 = true`!
  -- If EVERY `proj1 x` were in `rad`, then `rad` would have size ≥ `256 / 4 = 64 > 16`, contradiction!
  have hex_pair2 : ∃ a2 b2 : W 8,
      ell (β8 f g) a1 a2 = false ∧ ell (β8 f g) b1 a2 = false ∧
      ell (β8 f g) a1 b2 = false ∧ ell (β8 f g) b1 b2 = false ∧
      ell (β8 f g) a2 b2 = true := by
    cases h : (worlds 8).all (fun x => rad (β8 f g) (proj1 x))
    · obtain ⟨x, _, hx⟩ := all_false_exists _ _ h
      unfold rad at hx
      obtain ⟨y, _, hy⟩ := all_false_exists _ _ hx
      have hxy : ell (β8 f g) (proj1 x) y = true := by
        cases he : ell (β8 f g) (proj1 x) y <;> rw [he] at hy <;> simp at hy ⊢
      have hxy' : ell (β8 f g) (proj1 x) (proj1 y) = true := by
        have hl := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) (proj1 x)
        have ho := hproj1_orth x
        have oa : ell (β8 f g) (proj1 x) a1 = false := by rw [ell_symm]; exact ho.1
        have ob : ell (β8 f g) (proj1 x) b1 = false := by rw [ell_symm]; exact ho.2
        dsimp only [proj1]; rw [hl, hl, hxy]
        cases ell (β8 f g) b1 y <;> cases ell (β8 f g) a1 y <;> simp [oa, ob, ell_zero]
      exact ⟨proj1 x, proj1 y, (hproj1_orth x).1, (hproj1_orth x).2, (hproj1_orth y).1, (hproj1_orth y).2, hxy'⟩
    · exfalso; rw [List.all_eq_true] at h
      -- Count `rad` size ≥ 64 by fiber size 4 of `proj1`!
      have hge64 : 64 ≤ rr (β8 f g) := by
        -- For every `x`, `x = proj1 x ⊕ (c0*a1 ⊕ c1*b1)`, so `total 8 (fun x => rad (proj1 x)) = 4 * rr`!
        have hsum4 : total 8 (fun x => bind (rad (β8 f g) (proj1 x))) = 4 * rr (β8 f g) := by
          -- Every `w ∈ rad` has `proj1 (w ⊕ c0*a1 ⊕ c1*b1) = w`, and `proj1 x` is invariant under shifting by `a1, b1`!
          have hinv_a1 (x : W 8) : proj1 (add 8 a1 x) = proj1 x := by
            have hl1 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) a1
            have hl2 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) b1
            have hs1 := ell_self (β8 f g) a1
            have hba : ell (β8 f g) b1 a1 = true := by rw [ell_symm]; exact hab1
            dsimp only [proj1]; rw [hl1, hl2, hs1, hba, Bool.false_xor, Bool.true_xor]
            cases ell (β8 f g) b1 x <;> cases ell (β8 f g) a1 x <;>
              simp [add_zero_left, add_zero_right, Balanced242Plateau.add_assoc', add_comm 8 a1, add_self]
          have hinv_b1 (x : W 8) : proj1 (add 8 b1 x) = proj1 x := by
            have hl1 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) a1
            have hl2 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) b1
            have hs2 := ell_self (β8 f g) b1
            dsimp only [proj1]; rw [hl1, hl2, hs2, hab1, Bool.false_xor, Bool.true_xor]
            cases ell (β8 f g) b1 x <;> cases ell (β8 f g) a1 x <;>
              simp [add_zero_left, add_zero_right, Balanced242Plateau.add_assoc', add_comm 8 b1, add_self]
          -- And `rad (proj1 x) = true → x = w ⊕ ...`, i.e., `rad x = true → proj1 x = x`!
          have hrad_fix (x : W 8) (hr : rad (β8 f g) x = true) : proj1 x = x := by
            have ha := (Balanced242Rank.all_spec (p := fun y => !ell (β8 f g) x y)).mp hr a1
            have hb := (Balanced242Rank.all_spec (p := fun y => !ell (β8 f g) x y)).mp hr b1
            have ea : ell (β8 f g) a1 x = false := by
              rw [ell_symm]; cases e : ell (β8 f g) x a1 <;> rw [e] at ha <;> simp at ha ⊢
            have eb : ell (β8 f g) b1 x = false := by
              rw [ell_symm]; cases e : ell (β8 f g) x b1 <;> rw [e] at hb <;> simp at hb ⊢
            dsimp only [proj1]; rw [ea, eb]; simp [add_zero_right]
          have hpt (x : W 8) :
              bind (rad (β8 f g) (proj1 x)) =
              bind (rad (β8 f g) x) + bind (rad (β8 f g) (add 8 a1 x)) +
              bind (rad (β8 f g) (add 8 b1 x)) + bind (rad (β8 f g) (add 8 a1 (add 8 b1 x))) := by
            -- Note: `proj1 x` equals ONE of `{x, a1⊕x, b1⊕x, a1⊕b1⊕x}`, and the other 3 have `ell a1 ≠ 0 ∨ ell b1 ≠ 0`, so NOT in `rad`!
            have hnot_rad (y : W 8) (h1 : ell (β8 f g) a1 y = true ∨ ell (β8 f g) b1 y = true) :
                rad (β8 f g) y = false := by
              cases hr : rad (β8 f g) y
              · rfl
              · exfalso
                rcases h1 with ha | hb
                · have := (Balanced242Rank.all_spec (p := fun z => !ell (β8 f g) y z)).mp hr a1
                  rw [ell_symm, ha] at this; exact Bool.noConfusion this
                · have := (Balanced242Rank.all_spec (p := fun z => !ell (β8 f g) y z)).mp hr b1
                  rw [ell_symm, hb] at this; exact Bool.noConfusion this
            have hl1 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) a1
            have hl2 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) b1
            have hs1 := ell_self (β8 f g) a1
            have hs2 := ell_self (β8 f g) b1
            have hba : ell (β8 f g) b1 a1 = true := by rw [ell_symm]; exact hab1
            cases ea : ell (β8 f g) a1 x <;> cases eb : ell (β8 f g) b1 x
            · have hp : proj1 x = x := by dsimp only [proj1]; simp [ea, eb, add_zero_right]
              rw [hp, hnot_rad (add 8 a1 x) (Or.inr (by rw [hl2, hba, eb]; rfl)),
                  hnot_rad (add 8 b1 x) (Or.inl (by rw [hl1, hab1, ea]; rfl)),
                  hnot_rad (add 8 a1 (add 8 b1 x)) (Or.inl (by rw [hl1, hs1, hl1, hab1, ea]; rfl))]
              simp [Balanced242Plateau.ind]
            · have hp : proj1 x = add 8 a1 x := by dsimp only [proj1]; simp [ea, eb, add_zero_right, add_comm]
              rw [hp, hnot_rad x (Or.inr eb),
                  hnot_rad (add 8 b1 x) (Or.inl (by rw [hl1, hab1, ea]; rfl)),
                  hnot_rad (add 8 a1 (add 8 b1 x)) (Or.inl (by rw [hl1, hs1, hl1, hab1, ea]; rfl))]
              simp [Balanced242Plateau.ind]
            · have hp : proj1 x = add 8 b1 x := by dsimp only [proj1]; simp [ea, eb, add_zero_left, add_zero_right, add_comm]
              rw [hp, hnot_rad x (Or.inl ea),
                  hnot_rad (add 8 a1 x) (Or.inl (by rw [hl1, hs1, ea]; rfl)),
                  hnot_rad (add 8 a1 (add 8 b1 x)) (Or.inr (by rw [hl2, hba, hl2, hs2, eb]; rfl))]
              simp [Balanced242Plateau.ind]
            · have hp : proj1 x = add 8 a1 (add 8 b1 x) := by
                dsimp only [proj1]; simp [ea, eb, Balanced242Plateau.add_assoc', add_comm 8 x]
              rw [hp, hnot_rad x (Or.inl ea),
                  hnot_rad (add 8 a1 x) (Or.inl (by rw [hl1, hs1, ea]; rfl)),
                  hnot_rad (add 8 b1 x) (Or.inr (by rw [hl2, hs2, eb]; rfl))]
              simp [Balanced242Plateau.ind]
          rw [funext hpt, total_add, total_add, total_add,
              sum_shift 8 a1 (fun x => bind (rad (β8 f g) x)),
              sum_shift 8 b1 (fun x => bind (rad (β8 f g) x))]
          have hs3 : total 8 (fun x => bind (rad (β8 f g) (add 8 a1 (add 8 b1 x)))) = rr (β8 f g) := by
            rw [show (fun x => bind (rad (β8 f g) (add 8 a1 (add 8 b1 x)))) =
                fun x => bind (rad (β8 f g) (add 8 (add 8 a1 b1) x)) from
                funext (fun x => by rw [Balanced242Plateau.add_assoc']),
                sum_shift 8 (add 8 a1 b1) (fun x => bind (rad (β8 f g) x))]
            rfl
          rw [hs3]; change rr (β8 f g) + rr (β8 f g) + rr (β8 f g) + rr (β8 f g) = _; omega
        have h256 : total 8 (fun x => bind (rad (β8 f g) (proj1 x))) = 256 := by
          have h1 : (fun x => bind (rad (β8 f g) (proj1 x))) = fun _ => (1 : Int) :=
            funext (fun x => by rw [h x (all_worlds 8 x)]; rfl)
          rw [h1, total_const]; decide
        omega
      omega
  obtain ⟨a2, b2, ha12, hb12, ha1b2, hb1b2, hab2⟩ := hex_pair2
  -- Step C: Project `proj2 x` onto `{a1, b1, a2, b2}^⊥` — its image IS EXACTLY `rad (β8 f g)` (size 16)!
  let proj2 (x : W 8) : W 8 :=
    add 8 x (lin4 a1 b1 a2 b2
      (ell (β8 f g) b1 x, (ell (β8 f g) a1 x, (ell (β8 f g) b2 x, (ell (β8 f g) a2 x, ())))))
  have hproj2_rad (x : W 8) : rad (β8 f g) (proj2 x) = true := by
    -- Wait: if SOME `proj2 x` had `rad = false`, we'd get a 3rd symplectic pair → rank ≥ 6 (`rr ≤ 4`), contradiction!
    -- Even faster: just count! Every `w ∈ rad` has `proj2 (w ⊕ lin4 a1 b1 a2 b2 c) = w`, so the 16*16 = 256
    -- elements `lin4 a1 b1 a2 b2 c ⊕ w` (`c : W 4`, `w ∈ rad`) are ALL DISTINCT (each maps under
    -- `(ell b1, ell a1, ell b2, ell a2)` to `c`, so `c` and `w = proj2 x` are UNIQUELY determined!!)!
    -- Since there are 16 choices of `c` and `rr = 16` choices of `w`, `16 * 16 = 256 = |W 8|`,
    -- so EVERY `x : W 8` has `proj2 x ∈ rad`!
    have hbij : total 8 (fun y => bind (rad (β8 f g) (proj2 y))) = 256 := by
      have hpt (y : W 8) : bind (rad (β8 f g) (proj2 y)) =
          total 4 (fun c => bind (rad (β8 f g) (add 8 y (lin4 a1 b1 a2 b2 c)))) := by
        let cy : W 4 := (ell (β8 f g) b1 y, (ell (β8 f g) a1 y, (ell (β8 f g) b2 y, (ell (β8 f g) a2 y, ()))))
        have hlin_ell (c : W 4) :
            ell (β8 f g) b1 (lin4 a1 b1 a2 b2 c) = c.1 ∧
            ell (β8 f g) a1 (lin4 a1 b1 a2 b2 c) = c.2.1 ∧
            ell (β8 f g) b2 (lin4 a1 b1 a2 b2 c) = c.2.2.1 ∧
            ell (β8 f g) a2 (lin4 a1 b1 a2 b2 c) = c.2.2.2.1 := by
          have hl1 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) b1
          have hl2 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) a1
          have hl3 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) b2
          have hl4 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) a2
          have hba1 : ell (β8 f g) b1 a1 = true := by rw [ell_symm]; exact hab1
          have hba2 : ell (β8 f g) b2 a2 = true := by rw [ell_symm]; exact hab2
          have ha2a1 : ell (β8 f g) a2 a1 = false := by rw [ell_symm]; exact ha12
          have ha2b1 : ell (β8 f g) a2 b1 = false := by rw [ell_symm]; exact hb12
          have hb2a1 : ell (β8 f g) b2 a1 = false := by rw [ell_symm]; exact ha1b2
          have hb2b1 : ell (β8 f g) b2 b1 = false := by rw [ell_symm]; exact hb1b2
          rcases c with ⟨c0, c1, c2, c3, ⟨⟩⟩
          dsimp only [lin4]
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            (first | rw [hl1, hl1, hl1] | rw [hl2, hl2, hl2] | rw [hl3, hl3, hl3] | rw [hl4, hl4, hl4]) <;>
            (cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;>
             simp [ell_zero, ell_self,
                   hab1, hba1, hab2, hba2, ha12, hb12, ha1b2, hb1b2, ha2a1, ha2b1, hb2a1, hb2b1])
        have honly (c : W 4) (hne : c ≠ cy) : rad (β8 f g) (add 8 y (lin4 a1 b1 a2 b2 c)) = false := by
          cases hr : rad (β8 f g) (add 8 y (lin4 a1 b1 a2 b2 c))
          · rfl
          · exfalso
            have hl := hlin_ell c
            have h0 (v : W 8) : ell (β8 f g) v (add 8 y (lin4 a1 b1 a2 b2 c)) = false := by
              have := (Balanced242Rank.all_spec (p := fun z => !ell (β8 f g) (add 8 y (lin4 a1 b1 a2 b2 c)) z)).mp hr v
              rw [ell_symm] at this
              cases e : ell (β8 f g) v (add 8 y (lin4 a1 b1 a2 b2 c)) <;> rw [e] at this <;> simp at this ⊢
            have e0 := h0 b1; rw [Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) b1, hl.1] at e0
            have e1 := h0 a1; rw [Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) a1, hl.2.1] at e1
            have e2 := h0 b2; rw [Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) b2, hl.2.2.1] at e2
            have e3 := h0 a2; rw [Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) a2, hl.2.2.2] at e3
            apply hne
            rcases c with ⟨c0, c1, c2, c3, ⟨⟩⟩; dsimp only [cy] at e0 e1 e2 e3 ⊢
            have eqb (p q : Bool) (h : xor p q = false) : q = p := by cases p <;> cases q <;> simp at h ⊢
            rw [eqb _ _ e0, eqb _ _ e1, eqb _ _ e2, eqb _ _ e3]
        have hsum_eq : total 4 (fun c => bind (rad (β8 f g) (add 8 y (lin4 a1 b1 a2 b2 c)))) =
            total 4 (fun c => bind (rad (β8 f g) (proj2 y)) * hits cy c) := by
          apply congrArg (total 4); funext c; unfold hits
          by_cases h : cy = c
          · subst h; simp [proj2, cy]
          · have hne : c ≠ cy := fun e => h e.symm
            rw [honly c hne]; simp [h, Balanced242Plateau.ind]
        rw [hsum_eq, total_scale, diagonal 4 cy, Int.mul_one]
      rw [funext hpt]
      have hswap : total 8 (fun y => total 4 (fun c => bind (rad (β8 f g) (add 8 y (lin4 a1 b1 a2 b2 c))))) =
          total 4 (fun c => total 8 (fun y => bind (rad (β8 f g) (add 8 y (lin4 a1 b1 a2 b2 c))))) := by
        have aux : ∀ {m : Nat} (F : W m → W 4 → Int),
            total m (fun y => total 4 (fun c => F y c)) = total 4 (fun c => total m (fun y => F y c)) := by
          intro m; induction m with
          | zero => intro F; rfl
          | succ m ih =>
            intro F
            change total m (fun y => total 4 (fun c => F (false, y) c)) +
                   total m (fun y => total 4 (fun c => F (true, y) c)) =
                   total 4 (fun c => total m (fun y => F (false, y) c) + total m (fun y => F (true, y) c))
            rw [ih, ih, ← total_add]
        exact aux _
      rw [hswap]
      have hinner (c : W 4) : total 8 (fun y => bind (rad (β8 f g) (add 8 y (lin4 a1 b1 a2 b2 c)))) = 16 := by
        have hsh := sum_shift 8 (lin4 a1 b1 a2 b2 c) (fun y => bind (rad (β8 f g) y))
        have hc : (fun y => bind (rad (β8 f g) (add 8 y (lin4 a1 b1 a2 b2 c)))) =
            fun y => bind (rad (β8 f g) (add 8 (lin4 a1 b1 a2 b2 c) y)) := funext (fun y => by rw [add_comm])
        rw [hc, hsh]; exact hrr
      rw [funext hinner, total_const]; decide
    have hnn (y : W 8) : 0 ≤ 1 - bind (rad (β8 f g) (proj2 y)) := by
      cases rad (β8 f g) (proj2 y) <;> decide
    have hsum0 : total 8 (fun y => 1 - bind (rad (β8 f g) (proj2 y))) = 0 := by
      rw [total_sub, total_const, hbij]; decide
    have hp := point_le_total 8 _ hnn x; rw [hsum0] at hp
    cases hr : rad (β8 f g) (proj2 x)
    · rw [hr] at hp; simp [Balanced242Plateau.ind] at hp
    · rfl
  -- Step D: Normalize `(a1, b1, a2, b2)` to `(u1, v1, u2, v2)` so `Q(lin4 u1 v1 u2 v2 c) = !isSZ c`!
  -- Compute `Q(lin4 a1 b1 a2 b2 c)`:
  have hQ_lin (x1 y1 x2 y2 : W 8)
      (hp1 : ell (β8 f g) x1 y1 = true) (hp2 : ell (β8 f g) x2 y2 = true)
      (h12a : ell (β8 f g) x1 x2 = false) (h12b : ell (β8 f g) x1 y2 = false)
      (h12c : ell (β8 f g) y1 x2 = false) (h12d : ell (β8 f g) y1 y2 = false)
      (c : W 4) :
      Q (lin4 x1 y1 x2 y2 c) =
      xor (xor (c.1 && c.2.1) (c.2.2.1 && c.2.2.2.1))
          (xor (xor (c.1 && Q x1) (c.2.1 && Q y1))
               (xor (c.2.2.1 && Q x2) (c.2.2.2.1 && Q y2))) := by
    rcases c with ⟨c0, c1, c2, c3, ⟨⟩⟩
    dsimp only [lin4]
    have hpol := hQ_pol
    have hl1 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) x1
    have hl2 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) y1
    have hl3 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) x2
    have hQ_add (p q : W 8) : Q (add 8 p q) = xor (xor (Q p) (Q q)) (ell (β8 f g) p q) := by
      have h := hQ_pol p q
      cases a : Q (add 8 p q) <;> cases b : Q p <;> cases c : Q q <;> cases d : ell (β8 f g) p q <;>
        rw [a, b, c, d] at h <;> simp at h ⊢
    cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;>
      simp only [if_true, if_false, Bool.false_eq_true, add_zero_left, add_zero_right, hQ0,
        hQ_add, hl1, hl2, hl3, hp1, hp2, h12a, h12b, h12c, h12d,
        Bool.false_and, Bool.true_and, Bool.false_xor, Bool.xor_false] <;>
      (cases Q x1 <;> cases Q y1 <;> cases Q x2 <;> cases Q y2 <;> decide)
  -- Since `Zc = 96`, `total 4 (fun c => bind (!Q (lin4 a1 b1 a2 b2 c))) = 6`!
  -- Wait: let's prove `total 4 (fun c => bind (Zset f g (lin4 a1 b1 a2 b2 c))) = 6` from `Zc = 96`!
  have hZ_cnt6 : total 4 (fun c => bind (Zset f g (lin4 a1 b1 a2 b2 c))) = 6 := by
    let cOf (x : W 8) : W 4 := (ell (β8 f g) b1 x, (ell (β8 f g) a1 x, (ell (β8 f g) b2 x, (ell (β8 f g) a2 x, ()))))
    have hpt (x : W 8) : bind (Zset f g x) =
        total 4 (fun c => bind (Zset f g (lin4 a1 b1 a2 b2 c)) * hits (cOf x) c) := by
      have hsum : total 4 (fun c => bind (Zset f g (lin4 a1 b1 a2 b2 c)) * hits (cOf x) c) =
          bind (Zset f g (lin4 a1 b1 a2 b2 (cOf x))) := by
        have h1 (c : W 4) : bind (Zset f g (lin4 a1 b1 a2 b2 c)) * hits (cOf x) c =
            bind (Zset f g (lin4 a1 b1 a2 b2 (cOf x))) * hits (cOf x) c := by
          unfold hits; by_cases e : cOf x = c
          · subst e; rfl
          · simp [e]
        rw [funext h1, total_scale, diagonal 4 (cOf x), Int.mul_one]
      rw [hsum]
      have hx_eq : x = add 8 (lin4 a1 b1 a2 b2 (cOf x)) (proj2 x) := by
        dsimp only [proj2, cOf]
        rw [add_comm 8 x (lin4 a1 b1 a2 b2 _), ← Balanced242Plateau.add_assoc', add_self, add_zero_left]
      have hinv := hZ_rad_inv (lin4 a1 b1 a2 b2 (cOf x)) (proj2 x) (hproj2_rad x)
      rw [← hx_eq] at hinv; rw [hinv]
    have hZc96 : total 8 (fun x => bind (Zset f g x)) = 96 := by rw [← Zc_eq_total_Zset, hZc]
    rw [funext hpt] at hZc96
    have hswap : total 8 (fun x => total 4 (fun c => bind (Zset f g (lin4 a1 b1 a2 b2 c)) * hits (cOf x) c)) =
        total 4 (fun c => bind (Zset f g (lin4 a1 b1 a2 b2 c)) * total 8 (fun x => hits (cOf x) c)) := by
      have aux : ∀ {m : Nat} (F : W m → W 4 → Int),
          total m (fun x => total 4 (fun c => F x c)) = total 4 (fun c => total m (fun x => F x c)) := by
        intro m; induction m with
        | zero => intro F; rfl
        | succ m ih =>
          intro F
          change total m (fun x => total 4 (fun c => F (false, x) c)) +
                 total m (fun x => total 4 (fun c => F (true, x) c)) =
                 total 4 (fun c => total m (fun x => F (false, x) c) + total m (fun x => F (true, x) c))
          rw [ih, ih, ← total_add]
      rw [aux]; apply congrArg (total 4); funext c; rw [total_scale]
    rw [hswap] at hZc96
    have hfib (c : W 4) : total 8 (fun x => hits (cOf x) c) = 16 := by
      have hsh := sum_shift 8 (lin4 a1 b1 a2 b2 c) (fun x => hits (cOf x) c)
      rw [← hsh]
      have hpt2 (x : W 8) : hits (cOf (add 8 (lin4 a1 b1 a2 b2 c) x)) c = bind (rad (β8 f g) x) := by
        dsimp only [cOf]
        -- Because `ell v (lin4 c ⊕ x) = c_v ⊕ ell v x`, equality with `c` is `ell v x = false` for all 4 `v`,
        -- which is `proj2 x = x`, which is `rad x = true`!
        have hlin_ell :
            ell (β8 f g) b1 (lin4 a1 b1 a2 b2 c) = c.1 ∧
            ell (β8 f g) a1 (lin4 a1 b1 a2 b2 c) = c.2.1 ∧
            ell (β8 f g) b2 (lin4 a1 b1 a2 b2 c) = c.2.2.1 ∧
            ell (β8 f g) a2 (lin4 a1 b1 a2 b2 c) = c.2.2.2.1 := by
          have hl1 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) b1
          have hl2 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) a1
          have hl3 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) b2
          have hl4 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) a2
          have hba1 : ell (β8 f g) b1 a1 = true := by rw [ell_symm]; exact hab1
          have hba2 : ell (β8 f g) b2 a2 = true := by rw [ell_symm]; exact hab2
          have ha2a1 : ell (β8 f g) a2 a1 = false := by rw [ell_symm]; exact ha12
          have ha2b1 : ell (β8 f g) a2 b1 = false := by rw [ell_symm]; exact hb12
          have hb2a1 : ell (β8 f g) b2 a1 = false := by rw [ell_symm]; exact ha1b2
          have hb2b1 : ell (β8 f g) b2 b1 = false := by rw [ell_symm]; exact hb1b2
          rcases c with ⟨c0, c1, c2, c3, ⟨⟩⟩; dsimp only [lin4]
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            (first | rw [hl1, hl1, hl1] | rw [hl2, hl2, hl2] | rw [hl3, hl3, hl3] | rw [hl4, hl4, hl4]) <;>
            (cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;>
             simp [ell_zero, ell_self,
                   hab1, hba1, hab2, hba2, ha12, hb12, ha1b2, hb1b2, ha2a1, ha2b1, hb2a1, hb2b1])
        rw [Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) b1,
            Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) a1,
            Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) b2,
            Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) a2,
            hlin_ell.1, hlin_ell.2.1, hlin_ell.2.2.1, hlin_ell.2.2.2]
        have hiff : (xor c.1 (ell (β8 f g) b1 x), (xor c.2.1 (ell (β8 f g) a1 x),
                     (xor c.2.2.1 (ell (β8 f g) b2 x), (xor c.2.2.2.1 (ell (β8 f g) a2 x), ())))) = c ↔
                    rad (β8 f g) x = true := by
          constructor
          · intro heq
            rcases c with ⟨c0, c1, c2, c3, ⟨⟩⟩
            have h0 : ell (β8 f g) b1 x = false := by
              have h := congrArg Prod.fst heq; dsimp only at h
              cases c0 <;> cases e : ell (β8 f g) b1 x <;> simp [e] at h ⊢
            have h1 : ell (β8 f g) a1 x = false := by
              have h := congrArg (fun p => p.2.1) heq; dsimp only at h
              cases c1 <;> cases e : ell (β8 f g) a1 x <;> simp [e] at h ⊢
            have h2 : ell (β8 f g) b2 x = false := by
              have h := congrArg (fun p => p.2.2.1) heq; dsimp only at h
              cases c2 <;> cases e : ell (β8 f g) b2 x <;> simp [e] at h ⊢
            have h3 : ell (β8 f g) a2 x = false := by
              have h := congrArg (fun p => p.2.2.2.1) heq; dsimp only at h
              cases c3 <;> cases e : ell (β8 f g) a2 x <;> simp [e] at h ⊢
            have hp : proj2 x = x := by
              dsimp only [proj2]; rw [h0, h1, h2, h3]
              change add 8 x (lin4 a1 b1 a2 b2 (zero 4)) = x
              rw [lin4_zero, add_zero_right]
            rw [← hp]; exact hproj2_rad x
          · intro hr
            have h0 (v : W 8) : ell (β8 f g) v x = false := by
              have := (Balanced242Rank.all_spec (p := fun z => !ell (β8 f g) x z)).mp hr v
              rw [ell_symm] at this
              cases e : ell (β8 f g) v x <;> rw [e] at this <;> simp at this ⊢
            rw [h0 b1, h0 a1, h0 b2, h0 a2]; rcases c with ⟨c0, c1, c2, c3, ⟨⟩⟩; simp
        unfold hits Balanced242Plateau.ind
        by_cases hr : rad (β8 f g) x = true
        · rw [if_pos (hiff.mpr hr), hr]; rfl
        · have hne : ¬ (xor c.1 (ell (β8 f g) b1 x), (xor c.2.1 (ell (β8 f g) a1 x),
                        (xor c.2.2.1 (ell (β8 f g) b2 x), (xor c.2.2.2.1 (ell (β8 f g) a2 x), ())))) = c :=
            fun h => hr (hiff.mp h)
          simp [hr, hne]
      rw [funext hpt2]; exact hrr
    have hmul : total 4 (fun c => bind (Zset f g (lin4 a1 b1 a2 b2 c)) * 16) = 96 := by
      simpa only [hfib] using hZc96
    have hsc : total 4 (fun c => bind (Zset f g (lin4 a1 b1 a2 b2 c)) * 16) =
        16 * total 4 (fun c => bind (Zset f g (lin4 a1 b1 a2 b2 c))) := by
      rw [← total_scale]; apply congrArg (total 4); funext c; exact Int.mul_comm _ _
    rw [hsc] at hmul; omega
  -- From `hZ_cnt6`, EXACTLY ONE of `(Q a1, Q b1)` and `(Q a2, Q b2)` is `(true, true)`, and the other is NOT `(true, true)`!
  have hQ_types : ((Q a1 = true ∧ Q b1 = true) ∧ ¬ (Q a2 = true ∧ Q b2 = true)) ∨
                  ((Q a2 = true ∧ Q b2 = true) ∧ ¬ (Q a1 = true ∧ Q b1 = true)) := by
    have hpt (c : W 4) : bind (Zset f g (lin4 a1 b1 a2 b2 c)) =
        bind (!xor (xor (c.1 && c.2.1) (c.2.2.1 && c.2.2.2.1))
              (xor (xor (c.1 && Q a1) (c.2.1 && Q b1)) (xor (c.2.2.1 && Q a2) (c.2.2.2.1 && Q b2)))) := by
      have h := hQ_lin a1 b1 a2 b2 hab1 hab2 ha12 ha1b2 hb12 hb1b2 c
      dsimp only [Q] at h; rw [← h]; cases Zset f g (lin4 a1 b1 a2 b2 c) <;> rfl
    rw [funext hpt] at hZ_cnt6
    revert hZ_cnt6
    generalize Q a1 = q1; generalize Q b1 = q2; generalize Q a2 = q3; generalize Q b2 = q4
    cases q1 <;> cases q2 <;> cases q3 <;> cases q4 <;> decide
  -- Choose `(u1, v1)` to be the `(true, true)` pair and `(u2, v2)` to be the normalized `(false, false)` pair!
  have hex_norm : ∃ u1 v1 u2 v2 : W 8,
      ell (β8 f g) u1 v1 = true ∧ ell (β8 f g) u2 v2 = true ∧
      ell (β8 f g) u1 u2 = false ∧ ell (β8 f g) u1 v2 = false ∧
      ell (β8 f g) v1 u2 = false ∧ ell (β8 f g) v1 v2 = false ∧
      Q u1 = true ∧ Q v1 = true ∧ Q u2 = false ∧ Q v2 = false := by
    have norm_pair (x y : W 8) (hxy : ell (β8 f g) x y = true) (hnot : ¬ (Q x = true ∧ Q y = true))
        (o1 o2 : W 8) (ho1x : ell (β8 f g) o1 x = false) (ho1y : ell (β8 f g) o1 y = false)
        (ho2x : ell (β8 f g) o2 x = false) (ho2y : ell (β8 f g) o2 y = false) :
        ∃ x' y' : W 8, ell (β8 f g) x' y' = true ∧ Q x' = false ∧ Q y' = false ∧
          ell (β8 f g) o1 x' = false ∧ ell (β8 f g) o1 y' = false ∧
          ell (β8 f g) o2 x' = false ∧ ell (β8 f g) o2 y' = false := by
      have hQ_add (p q : W 8) : Q (add 8 p q) = xor (xor (Q p) (Q q)) (ell (β8 f g) p q) := by
        have h := hQ_pol p q
        cases a : Q (add 8 p q) <;> cases b : Q p <;> cases c : Q q <;> cases d : ell (β8 f g) p q <;>
          rw [a, b, c, d] at h <;> simp at h ⊢
      have hl1 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) o1
      have hl2 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) o2
      cases hx : Q x <;> cases hy : Q y
      · exact ⟨x, y, hxy, hx, hy, ho1x, ho1y, ho2x, ho2y⟩
      · refine ⟨x, add 8 x y, ?_, hx, ?_, ho1x, ?_, ho2x, ?_⟩
        · rw [Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) x, ell_self, hxy]; rfl
        · rw [hQ_add, hx, hy, hxy]; rfl
        · rw [hl1, ho1x, ho1y]; rfl
        · rw [hl2, ho2x, ho2y]; rfl
      · refine ⟨add 8 x y, y, ?_, ?_, hy, ?_, ho1y, ?_, ho2y⟩
        · rw [ell_symm, Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) y,
              ell_self, ell_symm, hxy]; rfl
        · rw [hQ_add, hx, hy, hxy]; rfl
        · rw [hl1, ho1x, ho1y]; rfl
        · rw [hl2, ho2x, ho2y]; rfl
      · exact absurd ⟨hx, hy⟩ hnot
    rcases hQ_types with ⟨⟨q1, q2⟩, hnot⟩ | ⟨⟨q3, q4⟩, hnot⟩
    · obtain ⟨u2, v2, hp2, qu2, qv2, h1, h2, h3, h4⟩ :=
        norm_pair a2 b2 hab2 hnot a1 b1 ha12 ha1b2 hb12 hb1b2
      exact ⟨a1, b1, u2, v2, hab1, hp2, h1, h2, h3, h4, q1, q2, qu2, qv2⟩
    · have ha2a1 : ell (β8 f g) a2 a1 = false := by rw [ell_symm]; exact ha12
      have ha2b1 : ell (β8 f g) a2 b1 = false := by rw [ell_symm]; exact hb12
      have hb2a1 : ell (β8 f g) b2 a1 = false := by rw [ell_symm]; exact ha1b2
      have hb2b1 : ell (β8 f g) b2 b1 = false := by rw [ell_symm]; exact hb1b2
      obtain ⟨u2, v2, hp2, qu2, qv2, h1, h2, h3, h4⟩ :=
        norm_pair a1 b1 hab1 hnot a2 b2 ha2a1 ha2b1 hb2a1 hb2b1
      exact ⟨a2, b2, u2, v2, hab2, hp2, h1, h2, h3, h4, q3, q4, qu2, qv2⟩
  obtain ⟨u1, v1, u2, v2, huv1, huv2, h12a, h12b, h12c, h12d, qu1, qv1, qu2, qv2⟩ := hex_norm
  -- Step E: Pick a 4-element basis `(r0, r1, r2, r3)` of the 16-element linear subspace `rad (β8 f g)`!
  have hex_outside (S : List (W 8)) (hlen : S.length < 16) :
      ∃ r : W 8, rad (β8 f g) r = true ∧ r ∉ S := by
    cases h : (worlds 8).all (fun x => !rad (β8 f g) x || S.elem x)
    · obtain ⟨r, _, hr⟩ := all_false_exists _ _ h
      have hrad : rad (β8 f g) r = true := by cases e : rad (β8 f g) r <;> rw [e] at hr <;> simp at hr ⊢
      have hnot : r ∉ S := by
        intro hmem; have he : S.elem r = true := List.elem_eq_true_of_mem hmem
        rw [he, Bool.or_true] at hr; exact Bool.noConfusion hr
      exact ⟨r, hrad, hnot⟩
    · exfalso; rw [List.all_eq_true] at h
      have hle : rr (β8 f g) ≤ (S.length : Int) := by
        have hsum_le : ∀ (L : List (W 8)),
            (∀ x, rad (β8 f g) x = true → x ∈ L) → rr (β8 f g) ≤ (L.length : Int) := by
          intro L; induction L with
          | nil =>
            intro hcov
            have h0 : rr (β8 f g) = 0 := by
              unfold rr; rw [← total_zero 8]; apply congrArg (total 8); funext x
              cases hr : rad (β8 f g) x
              · rfl
              · exact absurd (hcov x hr) (List.not_mem_nil _)
            omega
          | cons y ys ih =>
            intro hcov
            -- `rad x ≤ hits y x + (if x ∈ ys then rad x else 0)`:
            have hle_step : rr (β8 f g) ≤ 1 + total 8 (fun x => if ys.elem x then bind (rad (β8 f g) x) else 0) := by
              rw [← diagonal 8 y, ← total_add]; unfold rr
              apply total_mono 8; intro x; unfold hits Balanced242Plateau.ind
              cases hr : rad (β8 f g) x
              · simp; split <;> omega
              · rcases List.mem_cons.mp (hcov x hr) with rfl | htail
                · simp; split <;> omega
                · have he : ys.elem x = true := List.elem_eq_true_of_mem htail
                  simp [he]; split <;> omega
            -- And `total 8 (if ys.elem x then bind (rad x) else 0) ≤ ys.length` by same induction:
            have hsub : ∀ (M : List (W 8)),
                total 8 (fun x => if M.elem x then (1 : Int) else 0) ≤ (M.length : Int) := by
              intro M; induction M with
              | nil => simp [total_zero]
              | cons z zs ihM =>
                have hpt (x : W 8) : (if (z :: zs).elem x then (1 : Int) else 0) ≤
                    hits z x + (if zs.elem x then (1 : Int) else 0) := by
                  unfold hits
                  by_cases e : z = x
                  · subst e; simp; split <;> omega
                  · have hne : (x == z) = false := beq_false_of_ne (fun h' => e h'.symm)
                    have hne' : x ≠ z := fun h' => e h'.symm
                    simp [List.elem_cons, hne, e, hne']
                have hm := total_mono 8 _ _ hpt
                rw [total_add, diagonal 8 z] at hm
                have hlen_z : ((z :: zs).length : Int) = 1 + (zs.length : Int) := by simp; omega
                omega
            have hrad_le : total 8 (fun x => if ys.elem x then bind (rad (β8 f g) x) else 0) ≤ (ys.length : Int) := by
              have hm := total_mono 8 (fun x => if ys.elem x then bind (rad (β8 f g) x) else 0)
                (fun x => if ys.elem x then (1 : Int) else 0) (fun x => by
                  dsimp only; split
                  · cases rad (β8 f g) x <;> decide
                  · decide)
              exact Int.le_trans hm (hsub ys)
            have hlen_y : ((y :: ys).length : Int) = 1 + (ys.length : Int) := by simp; omega
            omega
        exact hsum_le S (fun x hx => by
          have ha := h x (all_worlds 8 x); rw [hx] at ha; simp at ha
          exact ha)
      omega
  obtain ⟨r0, hr0, hr0_ne⟩ := hex_outside [zero 8] (by decide)
  obtain ⟨r1, hr1, hr1_ne⟩ := hex_outside [zero 8, r0] (by simp)
  obtain ⟨r2, hr2, hr2_ne⟩ := hex_outside [zero 8, r0, r1, add 8 r0 r1] (by simp)
  obtain ⟨r3, hr3, hr3_ne⟩ := hex_outside
    [zero 8, r0, r1, add 8 r0 r1, r2, add 8 r0 r2, add 8 r1 r2, add 8 r0 (add 8 r1 r2)] (by simp)
  have hrad_lin (r : W 4) : rad (β8 f g) (lin4 r0 r1 r2 r3 r) = true := by
    have hrad_add (x y : W 8) (hx : rad (β8 f g) x = true) (hy : rad (β8 f g) y = true) :
        rad (β8 f g) (add 8 x y) = true := by
      unfold rad; rw [Balanced242Rank.all_spec]; intro z
      have h1 := (Balanced242Rank.all_spec (p := fun w => !ell (β8 f g) x w)).mp hx z
      have h2 := (Balanced242Rank.all_spec (p := fun w => !ell (β8 f g) y w)).mp hy z
      have e1 : ell (β8 f g) x z = false := by cases e : ell (β8 f g) x z <;> rw [e] at h1 <;> simp at h1 ⊢
      have e2 : ell (β8 f g) y z = false := by cases e : ell (β8 f g) y z <;> rw [e] at h2 <;> simp at h2 ⊢
      rw [ell_symm, Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) z,
          ell_symm _ z x, ell_symm _ z y, e1, e2]; rfl
    have hrad0 : rad (β8 f g) (zero 8) = true := by
      unfold rad; rw [Balanced242Rank.all_spec]; intro z
      rw [ell_symm, ell_zero]; rfl
    rcases r with ⟨b0, b1, b2, b3, ⟨⟩⟩; dsimp only [lin4]
    apply hrad_add; · cases b0 <;> simp [hr0, hrad0]
    apply hrad_add; · cases b1 <;> simp [hr1, hrad0]
    apply hrad_add; · cases b2 <;> simp [hr2, hrad0]
    cases b3 <;> simp [hr3, hrad0]
  -- `lin4 r0 r1 r2 r3` is INJECTIVE on `W 4` (hence BIJECTIVE onto the 16-element `rad (β8 f g)`!)!
  have hrad_inj (r r' : W 4) (heq : lin4 r0 r1 r2 r3 r = lin4 r0 r1 r2 r3 r') : r = r' := by
    have hz : lin4 r0 r1 r2 r3 (add 4 r r') = zero 8 := by rw [lin4_add, heq, add_self]
    have hzero (t : W 4) (ht : lin4 r0 r1 r2 r3 t = zero 8) : t = zero 4 := by
      rcases t with ⟨b0, b1, b2, b3, ⟨⟩⟩; dsimp only [lin4] at ht
      have hsolve (p q : W 8) (h : add 8 p q = zero 8) : q = p := by
        have h1 := congrArg (add 8 p) h
        rw [← Balanced242Plateau.add_assoc', add_self, add_zero_left, add_zero_right] at h1; exact h1
      cases b3
      · cases b2
        · cases b1
          · cases b0
            · rfl
            · exfalso; simp [add_zero_right] at ht; exact hr0_ne (by simp [ht])
          · cases b0
            · exfalso; simp [add_zero_left, add_zero_right] at ht; exact hr1_ne (by simp [ht])
            · exfalso; simp [add_zero_right] at ht; have h' := hsolve r0 r1 ht; exact hr1_ne (by simp [h'])
        · cases b1
          · cases b0
            · exfalso; simp [add_zero_left, add_zero_right] at ht; exact hr2_ne (by simp [ht])
            · exfalso; simp [add_zero_left, add_zero_right] at ht; have h' := hsolve r0 r2 ht; exact hr2_ne (by simp [h'])
          · cases b0
            · exfalso; simp [add_zero_left, add_zero_right] at ht; have h' := hsolve r1 r2 ht; exact hr2_ne (by simp [h'])
            · exfalso; simp [add_zero_left, add_zero_right] at ht
              rw [← Balanced242Plateau.add_assoc'] at ht; have h' := hsolve (add 8 r0 r1) r2 ht; exact hr2_ne (by simp [h'])
      · exfalso
        cases b2
        · cases b1
          · cases b0
            · simp [add_zero_left, add_zero_right] at ht; exact hr3_ne (by simp [ht])
            · simp [add_zero_left, add_zero_right] at ht; have h' := hsolve r0 r3 ht; exact hr3_ne (by simp [h'])
          · cases b0
            · simp [add_zero_left, add_zero_right] at ht; have h' := hsolve r1 r3 ht; exact hr3_ne (by simp [h'])
            · simp [add_zero_left, add_zero_right] at ht
              rw [← Balanced242Plateau.add_assoc'] at ht; have h' := hsolve (add 8 r0 r1) r3 ht; exact hr3_ne (by simp [h'])
        · cases b1
          · cases b0
            · simp [add_zero_left, add_zero_right] at ht; have h' := hsolve r2 r3 ht; exact hr3_ne (by simp [h'])
            · simp [add_zero_left, add_zero_right] at ht
              rw [← Balanced242Plateau.add_assoc'] at ht; have h' := hsolve (add 8 r0 r2) r3 ht; exact hr3_ne (by simp [h'])
          · cases b0
            · simp [add_zero_left, add_zero_right] at ht
              rw [← Balanced242Plateau.add_assoc'] at ht; have h' := hsolve (add 8 r1 r2) r3 ht; exact hr3_ne (by simp [h'])
            · simp [add_zero_left, add_zero_right] at ht
              rw [← Balanced242Plateau.add_assoc' 8 r1 r2 r3, ← Balanced242Plateau.add_assoc' 8 r0 (add 8 r1 r2) r3] at ht
              have h' := hsolve (add 8 r0 (add 8 r1 r2)) r3 ht; exact hr3_ne (by simp [h'])
    have h0 := hzero (add 4 r r') hz
    have h1 := congrArg (add 4 r) h0
    rw [← Balanced242Plateau.add_assoc', add_self, add_zero_left, add_zero_right] at h1; exact h1.symm
  -- Build the 4 dual vectors `d0, d1, d2, d3` via `readMask 8 (ell ·)`!
  let d0 : W 8 := readMask 8 (ell (β8 f g) v1)
  let d1 : W 8 := readMask 8 (ell (β8 f g) u1)
  let d2 : W 8 := readMask 8 (ell (β8 f g) v2)
  let d3 : W 8 := readMask 8 (ell (β8 f g) u2)
  have hd_spec (a : W 8) :
      dot 8 a d0 = ell (β8 f g) v1 a ∧ dot 8 a d1 = ell (β8 f g) u1 a ∧
      dot 8 a d2 = ell (β8 f g) v2 a ∧ dot 8 a d3 = ell (β8 f g) u2 a := by
    have s (w : W 8) : dot 8 a (readMask 8 (ell (β8 f g) w)) = ell (β8 f g) w a := by
      rw [dot_comm]; exact readMask_spec 8 _ (Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) w) a
    exact ⟨s v1, s u1, s v2, s u2⟩
  refine ⟨u1, v1, u2, v2, r0, r1, r2, r3, d0, d1, d2, d3, ?_, hrad_lin, ?_, ?_, ?_, fun _ _ => Or.inr trivial⟩
  · -- `Zset (lin4 u1 v1 u2 v2 c ⊕ lin4 r0 r1 r2 r3 r) = isSZ c`!
    intro c r
    rw [hZ_rad_inv _ _ (hrad_lin r)]
    have hq := hQ_lin u1 v1 u2 v2 huv1 huv2 h12a h12b h12c h12d c
    rw [qu1, qv1, qu2, qv2] at hq
    dsimp only [Q] at hq; unfold isSZ
    rcases c with ⟨c0, c1, c2, c3, ⟨⟩⟩
    generalize Zset f g (lin4 u1 v1 u2 v2 (c0, (c1, (c2, (c3, ()))))) = bz at hq ⊢
    cases bz <;> cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> simp at hq ⊢
  · -- Unique decomposition `x = lin4 u1 v1 u2 v2 c ⊕ lin4 r0 r1 r2 r3 r`!
    intro x
    let cx : W 4 := (ell (β8 f g) v1 x, (ell (β8 f g) u1 x, (ell (β8 f g) v2 x, (ell (β8 f g) u2 x, ()))))
    -- Show `add 8 x (lin4 u1 v1 u2 v2 cx)` lies in `rad` AND therefore in `range (lin4 r0 r1 r2 r3)`!
    have hlin_ell (c : W 4) :
        ell (β8 f g) v1 (lin4 u1 v1 u2 v2 c) = c.1 ∧
        ell (β8 f g) u1 (lin4 u1 v1 u2 v2 c) = c.2.1 ∧
        ell (β8 f g) v2 (lin4 u1 v1 u2 v2 c) = c.2.2.1 ∧
        ell (β8 f g) u2 (lin4 u1 v1 u2 v2 c) = c.2.2.2.1 := by
      have hl1 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) v1
      have hl2 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) u1
      have hl3 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) v2
      have hl4 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) u2
      have hvu1 : ell (β8 f g) v1 u1 = true := by rw [ell_symm]; exact huv1
      have hvu2 : ell (β8 f g) v2 u2 = true := by rw [ell_symm]; exact huv2
      have hu2u1 : ell (β8 f g) u2 u1 = false := by rw [ell_symm]; exact h12a
      have hu2v1 : ell (β8 f g) u2 v1 = false := by rw [ell_symm]; exact h12c
      have hv2u1 : ell (β8 f g) v2 u1 = false := by rw [ell_symm]; exact h12b
      have hv2v1 : ell (β8 f g) v2 v1 = false := by rw [ell_symm]; exact h12d
      rcases c with ⟨c0, c1, c2, c3, ⟨⟩⟩; dsimp only [lin4]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        (first | rw [hl1, hl1, hl1] | rw [hl2, hl2, hl2] | rw [hl3, hl3, hl3] | rw [hl4, hl4, hl4]) <;>
        (cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;>
         simp [ell_zero, ell_self,
               huv1, hvu1, huv2, hvu2, h12a, h12b, h12c, h12d, hu2u1, hu2v1, hv2u1, hv2v1])
    -- Every `w ∈ rad` has a unique preimage `r : W 4` under `lin4 r0 r1 r2 r3` (since `|W 4| = 16 = rr`)!
    have hrad_surj (w : W 8) (hw : rad (β8 f g) w = true) : ∃ r : W 4, lin4 r0 r1 r2 r3 r = w := by
      cases h : (worlds 4).all (fun r => !decide (lin4 r0 r1 r2 r3 r = w))
      · obtain ⟨r, _, hr⟩ := all_false_exists _ _ h
        exact ⟨r, by by_cases e : lin4 r0 r1 r2 r3 r = w <;> simp [e] at hr ⊢⟩
      · exfalso; rw [List.all_eq_true] at h
        -- Count: `total 4 (fun r => bind (rad (lin4 r0 r1 r2 r3 r))) = 16`, yet `rad` has `w` outside its image → `rr ≥ 17`!
        have h17 : 17 ≤ rr (β8 f g) := by
          have himg : total 8 (fun z => total 4 (fun r => hits (lin4 r0 r1 r2 r3 r) z)) = 16 := by
            have aux : ∀ {m : Nat} (F : W m → W 4 → Int),
                total m (fun z => total 4 (fun r => F z r)) = total 4 (fun r => total m (fun z => F z r)) := by
              intro m; induction m with
              | zero => intro F; rfl
              | succ m ih =>
                intro F
                change total m (fun z => total 4 (fun r => F (false, z) r)) +
                       total m (fun z => total 4 (fun r => F (true, z) r)) =
                       total 4 (fun r => total m (fun z => F (false, z) r) + total m (fun z => F (true, z) r))
                rw [ih, ih, ← total_add]
            rw [aux]
            have h1 (r : W 4) : total 8 (fun z => hits (lin4 r0 r1 r2 r3 r) z) = 1 := diagonal 8 _
            rw [funext h1, total_const]; decide
          have hle (z : W 8) : total 4 (fun r => hits (lin4 r0 r1 r2 r3 r) z) + hits w z ≤ bind (rad (β8 f g) z) := by
            have hhit1 : total 4 (fun r => hits (lin4 r0 r1 r2 r3 r) z) ≤ 1 := by
              cases h2 : (worlds 4).all (fun r => !decide (lin4 r0 r1 r2 r3 r = z))
              · obtain ⟨r0', _, hr0'⟩ := all_false_exists _ _ h2
                have heq : lin4 r0 r1 r2 r3 r0' = z := by
                  by_cases e : lin4 r0 r1 r2 r3 r0' = z <;> simp [e] at hr0' ⊢
                have hpt (r : W 4) : hits (lin4 r0 r1 r2 r3 r) z = hits r0' r := by
                  unfold hits; by_cases e : r0' = r
                  · subst e; simp [heq]
                  · have hne : ¬ lin4 r0 r1 r2 r3 r = z := fun h' => e (hrad_inj _ _ (heq.trans h'.symm))
                    simp [e, hne]
                rw [funext hpt, diagonal 4 r0']; exact Int.le_refl 1
              · rw [List.all_eq_true] at h2
                have hpt (r : W 4) : hits (lin4 r0 r1 r2 r3 r) z = 0 := by
                  have hr' := h2 r (all_worlds 4 r)
                  have hne : ¬ lin4 r0 r1 r2 r3 r = z := fun e => by rw [e, decide_eq_true rfl] at hr'; exact Bool.noConfusion hr'
                  unfold hits; simp [hne]
                rw [funext hpt, total_zero]; decide
            by_cases e : w = z
            · subst e
              have h0 : total 4 (fun r => hits (lin4 r0 r1 r2 r3 r) w) = 0 := by
                rw [← total_zero 4]; apply congrArg (total 4); funext r
                have hr' := h r (all_worlds 4 r)
                have hne : ¬ lin4 r0 r1 r2 r3 r = w := fun e' => by rw [e', decide_eq_true rfl] at hr'; exact Bool.noConfusion hr'
                unfold hits; simp [hne]
              rw [h0]; unfold hits; simp [hw, Balanced242Plateau.ind]
            · unfold hits; simp only [e, if_false, Int.add_zero]
              cases hrz : rad (β8 f g) z
              · have h0 : total 4 (fun r => if lin4 r0 r1 r2 r3 r = z then (1 : Int) else 0) = 0 := by
                  refine Eq.trans ?_ (total_zero 4)
                  apply congrArg (total 4); funext r
                  have hne : ¬ lin4 r0 r1 r2 r3 r = z := fun e' => by
                    have := hrad_lin r; rw [e', hrz] at this; exact Bool.noConfusion this
                  rw [if_neg hne]
                rw [h0]; decide
              · simpa [Balanced242Plateau.ind] using hhit1
          have hm := total_mono 8 _ _ hle
          rw [total_add, himg, diagonal 8 w] at hm; exact hm
        omega
    -- Same proof as `hproj2_rad` shows `add 8 x (lin4 u1 v1 u2 v2 cx) ∈ rad`!
    -- Even easier: `add 8 x (lin4 u1 v1 u2 v2 cx)` is orthogonal to `u1, v1, u2, v2`, and we know
    -- `total 8 (fun z => hits (c_uv z) zero4)` = `rr`? Wait: we ALREADY proved `hproj2_rad` for `(a1, b1, a2, b2)`,
    -- and `(u1, v1, u2, v2)` spans the EXACT SAME 4D symplectic complement as `(a1, b1, a2, b2)`!
    -- Even better: for ANY `y`, `proj_uv y := add 8 y (lin4 u1 v1 u2 v2 (c_uv y))` satisfies `rad (proj_uv y) = true`
    -- by the EXACT same 10-line count!
    have hrad_rem : rad (β8 f g) (add 8 x (lin4 u1 v1 u2 v2 cx)) = true := by
      let proj_uv (y : W 8) : W 8 :=
        add 8 y (lin4 u1 v1 u2 v2 (ell (β8 f g) v1 y, (ell (β8 f g) u1 y, (ell (β8 f g) v2 y, (ell (β8 f g) u2 y, ())))))
      have hbij : total 8 (fun y => bind (rad (β8 f g) (proj_uv y))) = 256 := by
        have hpt (y : W 8) : bind (rad (β8 f g) (proj_uv y)) =
            total 4 (fun c => bind (rad (β8 f g) (add 8 y (lin4 u1 v1 u2 v2 c)))) := by
          let cy : W 4 := (ell (β8 f g) v1 y, (ell (β8 f g) u1 y, (ell (β8 f g) v2 y, (ell (β8 f g) u2 y, ()))))
          have honly (c : W 4) (hne : c ≠ cy) : rad (β8 f g) (add 8 y (lin4 u1 v1 u2 v2 c)) = false := by
            cases hr : rad (β8 f g) (add 8 y (lin4 u1 v1 u2 v2 c))
            · rfl
            · exfalso
              have hl := hlin_ell c
              have h0 (v : W 8) : ell (β8 f g) v (add 8 y (lin4 u1 v1 u2 v2 c)) = false := by
                have := (Balanced242Rank.all_spec (p := fun z => !ell (β8 f g) (add 8 y (lin4 u1 v1 u2 v2 c)) z)).mp hr v
                rw [ell_symm] at this
                cases e : ell (β8 f g) v (add 8 y (lin4 u1 v1 u2 v2 c)) <;> rw [e] at this <;> simp at this ⊢
              have e0 := h0 v1; rw [Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) v1, hl.1] at e0
              have e1 := h0 u1; rw [Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) u1, hl.2.1] at e1
              have e2 := h0 v2; rw [Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) v2, hl.2.2.1] at e2
              have e3 := h0 u2; rw [Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) u2, hl.2.2.2] at e3
              apply hne; rcases c with ⟨c0, c1, c2, c3, ⟨⟩⟩; dsimp only [cy] at e0 e1 e2 e3 ⊢
              have eqb (p q : Bool) (h : xor p q = false) : q = p := by cases p <;> cases q <;> simp at h ⊢
              rw [eqb _ _ e0, eqb _ _ e1, eqb _ _ e2, eqb _ _ e3]
          have hsum_eq : total 4 (fun c => bind (rad (β8 f g) (add 8 y (lin4 u1 v1 u2 v2 c)))) =
              total 4 (fun c => bind (rad (β8 f g) (proj_uv y)) * hits cy c) := by
            apply congrArg (total 4); funext c; unfold hits
            by_cases h : cy = c
            · subst h; simp [proj_uv, cy]
            · rw [honly c (fun e => h e.symm)]; simp [h, Balanced242Plateau.ind]
          rw [hsum_eq, total_scale, diagonal 4 cy, Int.mul_one]
        rw [funext hpt]
        have aux : ∀ {m : Nat} (F : W m → W 4 → Int),
            total m (fun y => total 4 (fun c => F y c)) = total 4 (fun c => total m (fun y => F y c)) := by
          intro m; induction m with
          | zero => intro F; rfl
          | succ m ih =>
            intro F
            change total m (fun y => total 4 (fun c => F (false, y) c)) +
                   total m (fun y => total 4 (fun c => F (true, y) c)) =
                   total 4 (fun c => total m (fun y => F (false, y) c) + total m (fun y => F (true, y) c))
            rw [ih, ih, ← total_add]
        rw [aux]
        have hinner (c : W 4) : total 8 (fun y => bind (rad (β8 f g) (add 8 y (lin4 u1 v1 u2 v2 c)))) = 16 := by
          have hsh := sum_shift 8 (lin4 u1 v1 u2 v2 c) (fun y => bind (rad (β8 f g) y))
          have hc : (fun y => bind (rad (β8 f g) (add 8 y (lin4 u1 v1 u2 v2 c)))) =
              fun y => bind (rad (β8 f g) (add 8 (lin4 u1 v1 u2 v2 c) y)) := funext (fun y => by rw [add_comm])
          rw [hc, hsh]; exact hrr
        rw [funext hinner, total_const]; decide
      have hnn (y : W 8) : 0 ≤ 1 - bind (rad (β8 f g) (proj_uv y)) := by cases rad (β8 f g) (proj_uv y) <;> decide
      have hsum0 : total 8 (fun y => 1 - bind (rad (β8 f g) (proj_uv y))) = 0 := by
        rw [total_sub, total_const, hbij]; decide
      have hp := point_le_total 8 _ hnn x; rw [hsum0] at hp
      cases hr : rad (β8 f g) (proj_uv x)
      · rw [hr] at hp; simp [Balanced242Plateau.ind] at hp
      · rfl
    obtain ⟨rx, hrx⟩ := hrad_surj (add 8 x (lin4 u1 v1 u2 v2 cx)) hrad_rem
    refine ⟨(cx, rx), ?_, ?_⟩
    · rw [hrx, add_comm 8 x (lin4 u1 v1 u2 v2 cx), ← Balanced242Plateau.add_assoc', add_self, add_zero_left]
    · intro ⟨c', r'⟩ heq
      have hrad_ell (v : W 8) : ell (β8 f g) v (lin4 r0 r1 r2 r3 r') = false := by
        have := (Balanced242Rank.all_spec (p := fun z => !ell (β8 f g) (lin4 r0 r1 r2 r3 r') z)).mp (hrad_lin r') v
        rw [ell_symm] at this
        cases e : ell (β8 f g) v (lin4 r0 r1 r2 r3 r') <;> rw [e] at this <;> simp at this ⊢
      have hc'_eq : c' = cx := by
        have h0 : ell (β8 f g) v1 x = c'.1 := by
          rw [heq, Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) v1, (hlin_ell c').1, hrad_ell v1, Bool.xor_false]
        have h1 : ell (β8 f g) u1 x = c'.2.1 := by
          rw [heq, Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) u1, (hlin_ell c').2.1, hrad_ell u1, Bool.xor_false]
        have h2 : ell (β8 f g) v2 x = c'.2.2.1 := by
          rw [heq, Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) v2, (hlin_ell c').2.2.1, hrad_ell v2, Bool.xor_false]
        have h3 : ell (β8 f g) u2 x = c'.2.2.2.1 := by
          rw [heq, Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) u2, (hlin_ell c').2.2.2, hrad_ell u2, Bool.xor_false]
        rcases c' with ⟨c0, c1, c2, c3, ⟨⟩⟩; dsimp only [cx]; rw [h0, h1, h2, h3]
      subst hc'_eq
      have hr_eq : lin4 r0 r1 r2 r3 r' = lin4 r0 r1 r2 r3 rx := by
        rw [hrx, heq, add_comm 8 (lin4 u1 v1 u2 v2 cx) (lin4 r0 r1 r2 r3 r'),
            Balanced242Plateau.add_assoc', add_self, add_zero_right]
      exact Prod.ext rfl (hrad_inj r' rx hr_eq)
  · -- `dot (lin4 u1 v1 u2 v2 c) (lin4 d0 d1 d2 d3 x) = dot 4 c x`!
    intro c x
    have hlin_ell (c : W 4) :
        ell (β8 f g) v1 (lin4 u1 v1 u2 v2 c) = c.1 ∧
        ell (β8 f g) u1 (lin4 u1 v1 u2 v2 c) = c.2.1 ∧
        ell (β8 f g) v2 (lin4 u1 v1 u2 v2 c) = c.2.2.1 ∧
        ell (β8 f g) u2 (lin4 u1 v1 u2 v2 c) = c.2.2.2.1 := by
      have hl1 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) v1
      have hl2 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) u1
      have hl3 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) v2
      have hl4 := Balanced242Plateau.ell_hom (β8 f g) (cube8 f g res) u2
      have hvu1 : ell (β8 f g) v1 u1 = true := by rw [ell_symm]; exact huv1
      have hvu2 : ell (β8 f g) v2 u2 = true := by rw [ell_symm]; exact huv2
      have hu2u1 : ell (β8 f g) u2 u1 = false := by rw [ell_symm]; exact h12a
      have hu2v1 : ell (β8 f g) u2 v1 = false := by rw [ell_symm]; exact h12c
      have hv2u1 : ell (β8 f g) v2 u1 = false := by rw [ell_symm]; exact h12b
      have hv2v1 : ell (β8 f g) v2 v1 = false := by rw [ell_symm]; exact h12d
      rcases c with ⟨c0, c1, c2, c3, ⟨⟩⟩; dsimp only [lin4]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        (first | rw [hl1, hl1, hl1] | rw [hl2, hl2, hl2] | rw [hl3, hl3, hl3] | rw [hl4, hl4, hl4]) <;>
        (cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;>
         simp [ell_zero, ell_self,
               huv1, hvu1, huv2, hvu2, h12a, h12b, h12c, h12d, hu2u1, hu2v1, hv2u1, hv2v1])
    rcases x with ⟨x0, x1, x2, x3, ⟨⟩⟩
    change dot 8 (lin4 u1 v1 u2 v2 c)
      (add 8 (if x0 then d0 else zero 8) (add 8 (if x1 then d1 else zero 8)
        (add 8 (if x2 then d2 else zero 8) (if x3 then d3 else zero 8)))) =
      xor (c.1 && x0) (xor (c.2.1 && x1) (xor (c.2.2.1 && x2) (xor (c.2.2.2.1 && x3) false)))
    rw [dot_right, dot_right, dot_right]
    have s := hd_spec (lin4 u1 v1 u2 v2 c); have hl := hlin_ell c
    cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;>
      simp [dot_zero_right, s.1, s.2.1, s.2.2.1, s.2.2.2, hl.1, hl.2.1, hl.2.2.1, hl.2.2.2]
  · -- `dot (lin4 r0 r1 r2 r3 r) (lin4 d0 d1 d2 d3 x) = false`!
    intro r x
    have hrad_ell (v : W 8) : ell (β8 f g) v (lin4 r0 r1 r2 r3 r) = false := by
      have := (Balanced242Rank.all_spec (p := fun z => !ell (β8 f g) (lin4 r0 r1 r2 r3 r) z)).mp (hrad_lin r) v
      rw [ell_symm] at this
      cases e : ell (β8 f g) v (lin4 r0 r1 r2 r3 r) <;> rw [e] at this <;> simp at this ⊢
    rcases x with ⟨x0, x1, x2, x3, ⟨⟩⟩
    change dot 8 (lin4 r0 r1 r2 r3 r)
      (add 8 (if x0 then d0 else zero 8) (add 8 (if x1 then d1 else zero 8)
        (add 8 (if x2 then d2 else zero 8) (if x3 then d3 else zero 8)))) = false
    rw [dot_right, dot_right, dot_right]
    have s := hd_spec (lin4 r0 r1 r2 r3 r)
    cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;>
      simp [dot_zero_right, s.1, s.2.1, s.2.2.1, s.2.2.2, hrad_ell v1, hrad_ell u1, hrad_ell v2, hrad_ell u2]

/-- Constructive dual basis `(e0, e1, e2, e3)` for the 4 linearly independent vectors `(r0, r1, r2, r3)`
    such that `dot 8 (lin4 r0 r1 r2 r3 r) (lin4 e0 e1 e2 e3 y) = dot 4 r y`!
    Proof: `lin4 r0 r1 r2 r3 : W 4 → W 8` is injective, so for each `j ∈ {0..3}` we pick a vector
    `e_j` orthogonal to the other 3 `r_i` and having `dot e_j r_j = true` (exists because the orthogonal
    complement of 3 vectors has size `≥ 256 / 8 = 32`, while the orthogonal complement of all 4 has
    size `= 256 / 16 = 16`, so `32 - 16 = 16 > 0` vectors have `dot = true` on `r_j`!). -/
private theorem exists_dual_4 (r0 r1 r2 r3 : W 8)
    (hinj : ∀ r r' : W 4, lin4 r0 r1 r2 r3 r = lin4 r0 r1 r2 r3 r' → r = r') :
    ∃ e0 e1 e2 e3 : W 8, ∀ r y : W 4, dot 8 (lin4 r0 r1 r2 r3 r) (lin4 e0 e1 e2 e3 y) = dot 4 r y := by
  have find_one (a b c t : W 8)
      (hnot : ∀ ba bb bc : Bool,
        add 8 (if ba then a else zero 8) (add 8 (if bb then b else zero 8) (if bc then c else zero 8)) ≠ t) :
      ∃ e : W 8, dot 8 a e = false ∧ dot 8 b e = false ∧ dot 8 c e = false ∧ dot 8 t e = true := by
    -- Compute `total 8 (fun e => (1 + chr a e) * (1 + chr b e) * (1 + chr c e) * (1 - chr t e))`!
    -- Expanding gives `16 * 16 = 256` (since the 8 sums `ba*a ⊕ bb*b ⊕ bc*c` are never `t`, and the 7
    -- nonzero sums in `span{a,b,c}` are `0` or positive, Wait: even better, the `1` term gives `+256`
    -- and every `-chr(ba*a ⊕ bb*b ⊕ bc*c ⊕ t)` has nonzero argument so sums to `0`! And every
    -- `+chr(ba*a ⊕ bb*b ⊕ bc*c)` sums to `≥ 0` (`0` or `256`)!! SO THE TOTAL IS `≥ 256 > 0`!!)!
    let F (e : W 8) : Int := (1 + chr a e) * (1 + chr b e) * (1 + chr c e) * (1 - chr t e)
    have hsum_ge : 256 ≤ total 8 F := by
      have hch_add (p q e : W 8) : chr p e * chr q e = chr (add 8 p q) e := by
        have hsym (u : W 8) : chr u e = chr e u := by unfold chr; rw [dot_comm]
        rw [hsym, hsym, hsym, Balanced242Plateau.chr_add]
      have hpt (e : W 8) : F e =
          (1 + chr a e + chr b e + chr c e + chr (add 8 a b) e + chr (add 8 a c) e +
           chr (add 8 b c) e + chr (add 8 a (add 8 b c)) e) -
          (chr t e + chr (add 8 a t) e + chr (add 8 b t) e + chr (add 8 c t) e +
           chr (add 8 (add 8 a b) t) e + chr (add 8 (add 8 a c) t) e +
           chr (add 8 (add 8 b c) t) e + chr (add 8 (add 8 a (add 8 b c)) t) e) := by
        dsimp only [F]
        have h1 : (1 + chr a e) * (1 + chr b e) * (1 + chr c e) =
            1 + chr a e + chr b e + chr c e + chr a e * chr b e + chr a e * chr c e +
            chr b e * chr c e + chr a e * (chr b e * chr c e) := by
          simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, Int.mul_assoc]; omega
        rw [h1, hch_add a b, hch_add a c, hch_add b c, hch_add a (add 8 b c),
            Int.mul_sub, Int.mul_one]
        simp only [Int.add_mul, Int.one_mul, hch_add]
      rw [funext hpt, total_sub]
      simp only [total_add, total_const]
      have hge0 (w : W 8) : 0 ≤ total 8 (chr w) := by
        have h := identity_spectrum 8 w; change total 8 (chr w) = _ at h; rw [h]; split <;> decide
      have hne0 (ba bb bc : Bool) :
          add 8 (add 8 (if ba then a else zero 8) (add 8 (if bb then b else zero 8) (if bc then c else zero 8))) t ≠ zero 8 := by
        intro hz; apply hnot ba bb bc
        have h1 := congrArg (fun z => add 8 z t) hz
        dsimp only at h1
        rw [Balanced242Plateau.add_assoc', add_self, add_zero_right] at h1
        rw [add_zero_left] at h1; exact h1
      have hzero (w : W 8) (hw : w ≠ zero 8) : total 8 (chr w) = 0 := by
        have h := identity_spectrum 8 w; change total 8 (chr w) = _ at h; rw [h]; simp [hw]
      have z0 : total 8 (chr t) = 0 := hzero t (by simpa [add_zero_left] using hne0 false false false)
      have z1 : total 8 (chr (add 8 a t)) = 0 := hzero _ (by simpa [add_zero_left, add_zero_right] using hne0 true false false)
      have z2 : total 8 (chr (add 8 b t)) = 0 := hzero _ (by simpa [add_zero_left, add_zero_right] using hne0 false true false)
      have z3 : total 8 (chr (add 8 c t)) = 0 := hzero _ (by simpa [add_zero_left, add_zero_right] using hne0 false false true)
      have z4 : total 8 (chr (add 8 (add 8 a b) t)) = 0 := hzero _ (by simpa [add_zero_left, add_zero_right] using hne0 true true false)
      have z5 : total 8 (chr (add 8 (add 8 a c) t)) = 0 := hzero _ (by simpa [add_zero_left, add_zero_right] using hne0 true false true)
      have z6 : total 8 (chr (add 8 (add 8 b c) t)) = 0 := hzero _ (by simpa [add_zero_left, add_zero_right] using hne0 false true true)
      have z7 : total 8 (chr (add 8 (add 8 a (add 8 b c)) t)) = 0 := hzero _ (by simpa using hne0 true true true)
      have hm8 : many 8 = 256 := by decide
      have g1 := hge0 a; have g2 := hge0 b; have g3 := hge0 c
      have g4 := hge0 (add 8 a b); have g5 := hge0 (add 8 a c)
      have g6 := hge0 (add 8 b c); have g7 := hge0 (add 8 a (add 8 b c))
      rw [hm8, z0, z1, z2, z3, z4, z5, z6, z7]; omega
    cases hall : (worlds 8).all (fun e => decide (F e = 0))
    · obtain ⟨e, _, he⟩ := all_false_exists _ _ hall
      have hnz : F e ≠ 0 := fun h => by rw [decide_eq_true h] at he; exact Bool.noConfusion he
      dsimp only [F] at hnz; unfold chr at hnz
      refine ⟨e, ?_⟩
      cases ha : dot 8 a e <;> cases hb : dot 8 b e <;> cases hc : dot 8 c e <;> cases ht : dot 8 t e <;>
        rw [ha, hb, hc, ht] at hnz <;> simp [sign] at hnz ⊢
    · exfalso; rw [List.all_eq_true] at hall
      have h0 : total 8 F = 0 := by
        rw [← total_zero 8]; apply congrArg (total 8); funext e
        exact of_decide_eq_true (hall e (all_worlds 8 e))
      omega
  have hneq (p q : W 4) (hne : p ≠ q) : lin4 r0 r1 r2 r3 p ≠ lin4 r0 r1 r2 r3 q :=
    fun e => hne (hinj p q e)
  obtain ⟨e0, he0⟩ := find_one r1 r2 r3 r0 (fun b1 b2 b3 h => by
    apply hneq (false, (b1, (b2, (b3, ())))) (true, (false, (false, (false, ()))))
      (fun e => Bool.noConfusion (congrArg Prod.fst e))
    simpa [lin4, add_zero_left, add_zero_right] using h)
  obtain ⟨e1, he1⟩ := find_one r0 r2 r3 r1 (fun b0 b2 b3 h => by
    apply hneq (b0, (false, (b2, (b3, ())))) (false, (true, (false, (false, ()))))
      (fun e => Bool.noConfusion (congrArg (fun p => p.2.1) e))
    simpa [lin4, add_zero_left, add_zero_right] using h)
  obtain ⟨e2, he2⟩ := find_one r0 r1 r3 r2 (fun b0 b1 b3 h => by
    apply hneq (b0, (b1, (false, (b3, ())))) (false, (false, (true, (false, ()))))
      (fun e => Bool.noConfusion (congrArg (fun p => p.2.2.1) e))
    simpa [lin4, add_zero_left, add_zero_right] using h)
  obtain ⟨e3, he3⟩ := find_one r0 r1 r2 r3 (fun b0 b1 b2 h => by
    apply hneq (b0, (b1, (b2, (false, ())))) (false, (false, (false, (true, ()))))
      (fun e => Bool.noConfusion (congrArg (fun p => p.2.2.2.1) e))
    simpa [lin4, add_zero_left, add_zero_right] using h)
  refine ⟨e0, e1, e2, e3, fun r y => ?_⟩
  rcases r with ⟨r_0, r_1, r_2, r_3, ⟨⟩⟩
  rcases y with ⟨y_0, y_1, y_2, y_3, ⟨⟩⟩
  dsimp only [lin4]
  have dl (a b c : W 8) : dot 8 (add 8 a b) c = xor (dot 8 a c) (dot 8 b c) := by
    rw [dot_comm, dot_right, dot_comm 8 c a, dot_comm 8 c b]
  have hr_dot (w : W 8) :
      dot 8 (add 8 (if r_0 then r0 else zero 8) (add 8 (if r_1 then r1 else zero 8)
        (add 8 (if r_2 then r2 else zero 8) (if r_3 then r3 else zero 8)))) w =
      xor (if r_0 then dot 8 r0 w else false) (xor (if r_1 then dot 8 r1 w else false)
        (xor (if r_2 then dot 8 r2 w else false) (if r_3 then dot 8 r3 w else false))) := by
    rw [dl, dl, dl]; cases r_0 <;> cases r_1 <;> cases r_2 <;> cases r_3 <;> simp [dot_zero]
  rw [hr_dot]
  have he_dot (v : W 8) :
      dot 8 v (add 8 (if y_0 then e0 else zero 8) (add 8 (if y_1 then e1 else zero 8)
        (add 8 (if y_2 then e2 else zero 8) (if y_3 then e3 else zero 8)))) =
      xor (if y_0 then dot 8 v e0 else false) (xor (if y_1 then dot 8 v e1 else false)
        (xor (if y_2 then dot 8 v e2 else false) (if y_3 then dot 8 v e3 else false))) := by
    rw [dot_right, dot_right, dot_right]; cases y_0 <;> cases y_1 <;> cases y_2 <;> cases y_3 <;> simp [dot_zero_right]
  rw [he_dot r0, he_dot r1, he_dot r2, he_dot r3,
      he0.1, he0.2.1, he0.2.2.1, he0.2.2.2,
      he1.1, he1.2.1, he1.2.2.1, he1.2.2.2,
      he2.1, he2.2.1, he2.2.2.1, he2.2.2.2,
      he3.1, he3.2.1, he3.2.2.1, he3.2.2.2]
  change _ = xor (r_0 && y_0) (xor (r_1 && y_1) (xor (r_2 && y_2) (xor (r_3 && y_3) false)))
  cases r_0 <;> cases r_1 <;> cases r_2 <;> cases r_3 <;>
  cases y_0 <;> cases y_1 <;> cases y_2 <;> cases y_3 <;> rfl

set_option maxHeartbeats 800000 in
/-- **Main Theorem (`no_t112`)**: Complete, unconditional, LP-free, covering-radius-free Lean 4
    exclusion of `t = 112` (`agreements f g ≠ 112`)! -/
theorem no_t112 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (hicap : ∀ a, (hi f g a).natAbs ≤ 28)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (ht : agreements f g = 112) : False := by
  -- Step 1: Unconditional reduction to rank 4 (`rr = 16`, `Zc = 96`) and `n0 = 8, n8 = 0`, `Z0` = 3-subspace!
  have ⟨hrr, hZc⟩ := t112_forces_rank4_Z96 f g res hicap dc lores locap ht
  have ⟨hb, hn0_ge1, hn8_ge0⟩ := low_defect_budget f g dc lores locap
  have hn0_ge8 := rank4_Z96_n0_ge8 f g res dc lores locap (by rw [ht]; decide) hrr hZc
  have hn0_8 : n0 f g = 8 := by omega
  have hn8_0 : n8 f g = 0 := by omega
  have hZ0_sub := rank4_Z96_n0_eq8_subspace f g res dc lores locap (by rw [ht]; decide) hrr hZc hn0_8
  -- Pointwise magnitudes of `Vhat = lo / 2` when `n8 = 0`:
  have hVhat_val (a : W 8) :
      (lo f g a = 0 → (lo f g a / 2) * (lo f g a / 2) = 0) ∧
      (Zset f g a = true → lo f g a ≠ 0 → (lo f g a / 2) * (lo f g a / 2) = 64) ∧
      (Zset f g a = false → lo f g a / 2 = 12 ∨ lo f g a / 2 = -12) := by
    have hno8 : (lo f g a).natAbs ≠ 8 := by
      intro h8
      have hp := point_le_total 8 (fun x => if (lo f g x).natAbs = 8 then (1 : Int) else 0)
        (fun x => by dsimp only; split <;> decide) a
      change (if (lo f g a).natAbs = 8 then (1 : Int) else 0) ≤ n8 f g at hp
      rw [h8, if_pos rfl, hn8_0] at hp; omega
    unfold Zset
    rcases lo_vals f g lores locap a with h | h | h | h | h | h | h <;>
      rw [h] at hno8 ⊢ <;> simp at hno8 ⊢
  -- Step 2: Symplectic decomposition of `W 8` into `c ∈ W 4` (`u1, v1, u2, v2`) ⊕ `r ∈ W 4` (`rad`)!
  obtain ⟨u1, v1, u2, v2, r0, r1, r2, r3, d0, d1, d2, d3,
          hZ_isSZ, hrad_lin, hdecomp, hdot_ud, hdot_rd, _⟩ :=
    rank4_Z96_symplectic_decomp f g res dc lores hrr hZc
  have hrad_inj (r r' : W 4) (h : lin4 r0 r1 r2 r3 r = lin4 r0 r1 r2 r3 r') : r = r' := by
    obtain ⟨p, _, hu⟩ := hdecomp (lin4 r0 r1 r2 r3 r)
    have h1 := hu (zero 4, r) (by rw [lin4_zero, add_zero_left])
    have h2 := hu (zero 4, r') (by rw [lin4_zero, add_zero_left, h])
    exact congrArg Prod.snd (h1.trans h2.symm)
  obtain ⟨e0, e1, e2, e3, hdot_re⟩ := exists_dual_4 r0 r1 r2 r3 hrad_inj
  -- Wait: we also know `lin4 d0 d1 d2 d3 x ⊕ lin4 e0 e1 e2 e3 y` is a BIJECTION `W 4 × W 4 → W 8`!
  -- Wait: do we need `dot u_k e_j = 0`? Let's check!
  -- Actually for `x ∈ W 4` (cell position inside `R^⊥`) and `y ∈ W 4` (coset rep `lin4 e0 e1 e2 e3 y`):
  -- Define `v_y (x : W 4) := Vtbl f g (add 8 (lin4 e0 e1 e2 e3 y) (lin4 d0 d1 d2 d3 x))`!
  -- Check its 4-bit Walsh transform `z y c = transform (v_y) c`!
  -- `16 * z y c = ∑_{r : W 4} Vhat(lin4 u c ⊕ lin4 r0 r) * chr (lin4 u c) (lin4 e y) * chr r y`!
  -- WAIT A SECOND!! `chr (lin4 u c) (lin4 e y) = ±1` DEPENDS ON `y`, SO LET `w y c := chr (lin4 u c) (lin4 e y) * z y c`!!
  -- THEN:
  --   1. `w y c ^ 2 = z y c ^ 2` (IDENTICAL SQUARES!!),
  --   2. `transform (fun y => w y c) r = Vhat (lin4 u c ⊕ lin4 r0 r)` (EXACT 4-BIT WALSH TRANSFORM OVER `y : W 4`!!)!
  -- OH!! WHAT A TRICK!! WE DIDN'T EVEN NEED `dot u_k e_j = 0`!!
  let L_u (c : W 4) : W 8 := lin4 u1 v1 u2 v2 c
  let L_r (r : W 4) : W 8 := lin4 r0 r1 r2 r3 r
  let L_d (x : W 4) : W 8 := lin4 d0 d1 d2 d3 x
  let L_e (y : W 4) : W 8 := lin4 e0 e1 e2 e3 y
  -- Prove `(y, x) ↦ L_e y ⊕ L_d x` is a BIJECTION `W 4 × W 4 → W 8` (via injectivity on `total 8`)!
  have hde_inj (y1 y2 x1 x2 : W 4) (heq : add 8 (L_e y1) (L_d x1) = add 8 (L_e y2) (L_d x2)) :
      y1 = y2 ∧ x1 = x2 := by
    have hy : y1 = y2 := by
      have hdot (r : W 4) : dot 4 r y1 = dot 4 r y2 := by
        have h1 := congrArg (dot 8 (L_r r)) heq
        rw [dot_right, dot_right, hdot_rd, hdot_rd, Bool.xor_false, Bool.xor_false, hdot_re, hdot_re] at h1
        exact h1
      have h0 : add 4 y1 y2 = zero 4 := by
        by_cases hz : add 4 y1 y2 = zero 4
        · exact hz
        · exfalso; obtain ⟨r, hr⟩ := exists_dot_true (add 4 y1 y2) hz
          rw [dot_right, hdot r, Bool.xor_self] at hr; exact Bool.noConfusion hr
      exact (add_cancel_left y1 y2 y1 (by rw [add_self]; exact h0)).symm
    subst hy
    have hx_eq : L_d x1 = L_d x2 := add_cancel_left (L_e y1) (L_d x1) (L_d x2) heq
    have hx : x1 = x2 := by
      have hdot (c : W 4) : dot 4 c x1 = dot 4 c x2 := by
        have h1 := congrArg (dot 8 (L_u c)) hx_eq
        rw [hdot_ud, hdot_ud] at h1; exact h1
      have h0 : add 4 x1 x2 = zero 4 := by
        by_cases hz : add 4 x1 x2 = zero 4
        · exact hz
        · exfalso; obtain ⟨c, hc⟩ := exists_dot_true (add 4 x1 x2) hz
          rw [dot_right, hdot c, Bool.xor_self] at hc; exact Bool.noConfusion hc
      exact (add_cancel_left x1 x2 x1 (by rw [add_self]; exact h0)).symm
    exact ⟨rfl, hx⟩
  -- Helper: summing over `W 8` = double sum over `W 4 × W 4` via `L_e y ⊕ L_d x`!
  have hsum_de (F : W 8 → Int) :
      total 8 F = total 4 (fun y => total 4 (fun x => F (add 8 (L_e y) (L_d x)))) := by
    have hpre (z : W 8) :
        total 4 (fun y => total 4 (fun x => hits z (add 8 (L_e y) (L_d x)))) = 1 := by
      have hle (w : W 8) :
          total 4 (fun y => total 4 (fun x => hits w (add 8 (L_e y) (L_d x)))) ≤ 1 := by
        cases h : (worlds 4).all (fun y => (worlds 4).all (fun x => !decide (add 8 (L_e y) (L_d x) = w)))
        · obtain ⟨y0, _, hy0⟩ := all_false_exists _ _ h
          obtain ⟨x0, _, hx0⟩ := all_false_exists _ _ hy0
          have heq : add 8 (L_e y0) (L_d x0) = w := by
            by_cases e : add 8 (L_e y0) (L_d x0) = w <;> simp [e] at hx0 ⊢
          have hpt (y x : W 4) : hits w (add 8 (L_e y) (L_d x)) = hits y0 y * hits x0 x := by
            unfold hits
            by_cases e1 : y0 = y
            · subst e1; by_cases e2 : x0 = x
              · subst e2; simp [heq]
              · have hne : ¬ w = add 8 (L_e y0) (L_d x) := fun h' => e2 (hde_inj _ _ _ _ (heq.trans h')).2
                simp [e2, hne]
            · have hne : ¬ w = add 8 (L_e y) (L_d x) := fun h' => e1 (hde_inj _ _ _ _ (heq.trans h')).1
              simp [e1, hne]
          have h1 : total 4 (fun y => total 4 (fun x => hits w (add 8 (L_e y) (L_d x)))) =
              total 4 (fun y => hits y0 y * total 4 (fun x => hits x0 x)) := by
            apply congrArg (total 4); funext y; rw [← total_scale]; apply congrArg (total 4); funext x; exact hpt y x
          rw [h1]; simp only [diagonal 4 x0, Int.mul_one, diagonal 4 y0]; exact Int.le_refl 1
        · rw [List.all_eq_true] at h
          have hpt (y x : W 4) : hits w (add 8 (L_e y) (L_d x)) = 0 := by
            have hy' := h y (all_worlds 4 y); rw [List.all_eq_true] at hy'
            have hx' := hy' x (all_worlds 4 x)
            have hne : ¬ w = add 8 (L_e y) (L_d x) := fun e => by
              rw [← e, decide_eq_true rfl] at hx'; exact Bool.noConfusion hx'
            unfold hits; simp [hne]
          simp only [hpt, total_zero]; decide
      have hnn (w : W 8) : 0 ≤ 1 - total 4 (fun y => total 4 (fun x => hits w (add 8 (L_e y) (L_d x)))) := by
        have := hle w; omega
      have hsum0 : total 8 (fun w => 1 - total 4 (fun y => total 4 (fun x => hits w (add 8 (L_e y) (L_d x))))) = 0 := by
        rw [total_sub, total_const]
        have hswap1 : ∀ {m : Nat} (G : W m → W 4 → Int),
            total m (fun w => total 4 (fun y => G w y)) = total 4 (fun y => total m (fun w => G w y)) := by
          intro m; induction m with
          | zero => intro G; rfl
          | succ m ih =>
            intro G
            change total m (fun w => total 4 (fun y => G (false, w) y)) +
                   total m (fun w => total 4 (fun y => G (true, w) y)) =
                   total 4 (fun y => total m (fun w => G (false, w) y) + total m (fun w => G (true, w) y))
            rw [ih, ih, ← total_add]
        rw [hswap1]
        have hinner (y : W 4) : total 8 (fun w => total 4 (fun x => hits w (add 8 (L_e y) (L_d x)))) = 16 := by
          rw [hswap1]
          have hx (x : W 4) : total 8 (fun w => hits w (add 8 (L_e y) (L_d x))) = 1 := by
            have hc : (fun w => hits w (add 8 (L_e y) (L_d x))) = hits (add 8 (L_e y) (L_d x)) :=
              funext (fun w => by
                unfold hits; by_cases e : w = add 8 (L_e y) (L_d x)
                · subst e; simp
                · have hne : ¬ add 8 (L_e y) (L_d x) = w := fun h => e h.symm; simp [e, hne])
            rw [hc, diagonal 8]
          rw [funext hx, total_const]; decide
        rw [funext hinner, total_const]; decide
      have hp := point_le_total 8 _ hnn z; rw [hsum0] at hp; have h0 := hnn z; omega
    have h1 : total 8 F = total 8 (fun z => F z * total 4 (fun y => total 4 (fun x => hits z (add 8 (L_e y) (L_d x))))) := by
      apply congrArg (total 8); funext z; rw [hpre z, Int.mul_one]
    rw [h1]
    have hswap1 : ∀ {m : Nat} (G : W m → W 4 → Int),
        total m (fun w => total 4 (fun y => G w y)) = total 4 (fun y => total m (fun w => G w y)) := by
      intro m; induction m with
      | zero => intro G; rfl
      | succ m ih =>
        intro G
        change total m (fun w => total 4 (fun y => G (false, w) y)) +
               total m (fun w => total 4 (fun y => G (true, w) y)) =
               total 4 (fun y => total m (fun w => G (false, w) y) + total m (fun w => G (true, w) y))
        rw [ih, ih, ← total_add]
    have h2 : total 8 (fun z => F z * total 4 (fun y => total 4 (fun x => hits z (add 8 (L_e y) (L_d x))))) =
        total 8 (fun z => total 4 (fun y => total 4 (fun x => F z * hits z (add 8 (L_e y) (L_d x))))) := by
      apply congrArg (total 8); funext z; rw [← total_scale]
      apply congrArg (total 4); funext y; rw [← total_scale]
    rw [h2, hswap1]; apply congrArg (total 4); funext y
    rw [hswap1]; apply congrArg (total 4); funext x
    have hpt (z : W 8) : F z * hits z (add 8 (L_e y) (L_d x)) =
        F (add 8 (L_e y) (L_d x)) * hits (add 8 (L_e y) (L_d x)) z := by
      unfold hits; by_cases e : z = add 8 (L_e y) (L_d x)
      · subst e; simp
      · have hne : ¬ add 8 (L_e y) (L_d x) = z := fun h' => e h'.symm; simp [e, hne]
    rw [funext hpt, total_scale, diagonal 8, Int.mul_one]
  -- Define the 16 ternary cells `v y : W 4 → Int` and their signed transforms `w y c`!
  let v (y x : W 4) : Int := Vtbl f g (add 8 (L_e y) (L_d x))
  let z (y c : W 4) : Int := transform (v y) c
  let w (y c : W 4) : Int := chr (L_u c) (L_e y) * z y c
  let mcell (y : W 4) : Int := total 4 (fun x => v y x * v y x)
  -- Key identity: `transform (fun y => w y c) r = lo f g (L_u c ⊕ L_r r) / 2`!
  have htr_w (c r : W 4) : transform (fun y => w y c) r = lo f g (add 8 (L_u c) (L_r r)) / 2 := by
    have hlo2 : lo f g (add 8 (L_u c) (L_r r)) / 2 = transform (Vtbl f g) (add 8 (L_u c) (L_r r)) := by
      have h := lo_eq_2_transform_V f g (add 8 (L_u c) (L_r r)); omega
    rw [hlo2]; unfold transform; rw [hsum_de]
    apply congrArg (total 4); funext y
    dsimp only [w, z]; unfold transform
    have hsc : (chr (L_u c) (L_e y) * total 4 (fun x => v y x * chr c x)) * chr r y =
        total 4 (fun x => v y x * (chr (L_u c) (L_e y) * chr c x * chr r y)) := by
      rw [Int.mul_right_comm, ← total_scale]; apply congrArg (total 4); funext x; ac_rfl
    rw [hsc]; apply congrArg (total 4); funext x
    dsimp only [v]; congr 1
    -- Check `chr (L_u c) (L_e y) * chr c x * chr r y = chr (L_u c ⊕ L_r r) (L_e y ⊕ L_d x)`!
    have h1 : chr (add 8 (L_u c) (L_r r)) (add 8 (L_e y) (L_d x)) =
        chr (L_u c) (L_e y) * chr (L_u c) (L_d x) * (chr (L_r r) (L_e y) * chr (L_r r) (L_d x)) := by
      have hsym (a b : W 8) : chr a b = chr b a := by unfold chr; rw [dot_comm]
      rw [Balanced242Plateau.chr_add, hsym _ (L_e y), hsym _ (L_d x),
          Balanced242Plateau.chr_add, Balanced242Plateau.chr_add,
          hsym (L_e y), hsym (L_e y), hsym (L_d x), hsym (L_d x)]
      ac_rfl
    have h2 : chr (L_u c) (L_d x) = chr c x := by unfold chr; rw [hdot_ud]
    have h3 : chr (L_r r) (L_e y) = chr r y := by unfold chr; rw [hdot_re]
    have h4 : chr (L_r r) (L_d x) = 1 := by unfold chr; rw [hdot_rd]; rfl
    rw [h1, h2, h3, h4, Int.mul_one]
  -- From `htr_w`: Parseval on `W 4` gives `16 * ∑_y z y c ^ 2 = ∑_r (Vhat (L_u c ⊕ L_r r))^2`!
  have hcoset_energy (c : W 4) :
      16 * total 4 (fun y => z y c * z y c) =
      total 4 (fun r => (lo f g (add 8 (L_u c) (L_r r)) / 2) * (lo f g (add 8 (L_u c) (L_r r)) / 2)) := by
    have hpar := Balanced242Section0320.parseval (fun y => w y c)
    have hm4 : many 4 = 16 := by decide
    rw [hm4] at hpar
    have h1 (y : W 4) : w y c * w y c = z y c * z y c := by
      dsimp only [w]; have hsq : chr (L_u c) (L_e y) * chr (L_u c) (L_e y) = 1 := sign_sq _
      calc (chr (L_u c) (L_e y) * z y c) * (chr (L_u c) (L_e y) * z y c)
          = (chr (L_u c) (L_e y) * chr (L_u c) (L_e y)) * (z y c * z y c) := by ac_rfl
        _ = z y c * z y c := by rw [hsq, Int.one_mul]
    rw [funext (htr_w c), funext h1] at hpar; exact hpar.symm
  -- Total weight sum `∑_y mcell y = 112`!
  have hm_sum : total 4 mcell = 112 := by
    have hV2 : total 8 (fun x => Vtbl f g x * Vtbl f g x) = 112 := by
      rw [← ht]; unfold agreements countPair Vtbl; rw [← total_add]
      apply congrArg (total 8); funext x; cases f x <;> cases g x <;> decide
    rw [hsum_de] at hV2; exact hV2
  -- For EVERY `c ∈ SZc`: `3 ∣ z y c` AND `∑_y z y c ^ 2 = 144`!
  have hz_mod3 (y c : W 4) (hc : isSZ c = false) : z y c % 3 = 0 := by
    have hinv := transform_involution (fun u => w u c) y
    have hm4 : many 4 = 16 := by decide
    rw [hm4, funext (htr_w c)] at hinv
    have hdiv3 : transform (fun r => lo f g (add 8 (L_u c) (L_r r)) / 2) y % 3 = 0 := by
      unfold transform
      have aux : ∀ {m : Nat} (F : W m → Int), (∀ r, F r % 3 = 0) → total m F % 3 = 0 := by
        intro m; induction m with
        | zero => intro F hF; exact hF ()
        | succ m ih =>
          intro F hF
          change (total m (fun a => F (false, a)) + total m (fun a => F (true, a))) % 3 = 0
          have h1 := ih (fun a => F (false, a)) (fun a => hF (false, a))
          have h2 := ih (fun a => F (true, a)) (fun a => hF (true, a)); omega
      apply aux; intro r; dsimp only
      have hZ : Zset f g (add 8 (L_u c) (L_r r)) = false := by rw [hZ_isSZ c r, hc]
      have hval := (hVhat_val (add 8 (L_u c) (L_r r))).2.2 hZ
      rcases hval with h | h <;> rw [h] <;>
        (have hs : chr y r = 1 ∨ chr y r = -1 := sign_vals _; rcases hs with e | e <;> rw [e] <;> decide)
    have hchr : chr (L_u c) (L_e y) = 1 ∨ chr (L_u c) (L_e y) = -1 := sign_vals _
    dsimp only [w] at hinv
    rcases hchr with e | e <;> rw [e] at hinv <;> omega
  have hSZc_tot (c : W 4) (hc : isSZ c = false) : total 4 (fun y => z y c * z y c) = 144 := by
    have he := hcoset_energy c
    have hpt (r : W 4) : (lo f g (add 8 (L_u c) (L_r r)) / 2) * (lo f g (add 8 (L_u c) (L_r r)) / 2) = 144 := by
      have hZ : Zset f g (add 8 (L_u c) (L_r r)) = false := by rw [hZ_isSZ c r, hc]
      rcases (hVhat_val _).2.2 hZ with h | h <;> rw [h] <;> decide
    rw [funext hpt, total_const] at he
    have hm4 : many 4 = 16 := by decide
    rw [hm4] at he; omega
  -- Step 3: Because `Z0` is a linear 3-subspace inside `Z`, every `s ∈ SZ` has
  --         `|Z0 ∩ (L_u s + R)| ∈ {0, 4, 8}`, so `tot[s] = ∑_y z y s ^ 2 ∈ {32, 48, 64}` (`16 ∣ tot[s]`),
  --         and at least 4 cosets `s ∈ SZ` have `tot[s] = 64` (zero-free)!
  let zeroCnt (s : W 4) : Int :=
    total 4 (fun r => if lo f g (add 8 (L_u s) (L_r r)) = 0 then (1 : Int) else 0)
  have hzeroCnt_sum : total 4 (fun s => if isSZ s then zeroCnt s else 0) = 8 := by
    have htot8 : total 8 (fun a => if lo f g a = 0 then (1 : Int) else 0) = 8 := hn0_8
    -- Decompose `total 8` via `(c, r) ↦ L_u c ⊕ L_r r` (bijection `hdecomp`)!
    have hsum_ur (F : W 8 → Int) :
        total 8 F = total 4 (fun c => total 4 (fun r => F (add 8 (L_u c) (L_r r)))) := by
      have hpre (a : W 8) : total 4 (fun c => total 4 (fun r => hits a (add 8 (L_u c) (L_r r)))) = 1 := by
        obtain ⟨⟨c0, r0⟩, ha0, huniq⟩ := hdecomp a
        have hpt (c r : W 4) : hits a (add 8 (L_u c) (L_r r)) = hits c0 c * hits r0 r := by
          unfold hits
          by_cases e1 : c0 = c
          · subst e1; by_cases e2 : r0 = r
            · subst e2; simp [ha0]
            · have hne : ¬ a = add 8 (L_u c0) (L_r r) := fun h' => e2 (congrArg Prod.snd (huniq (c0, r) h')).symm
              simp [e2, hne]
          · have hne : ¬ a = add 8 (L_u c) (L_r r) := fun h' => e1 (congrArg Prod.fst (huniq (c, r) h')).symm
            simp [e1, hne]
        have h1 : total 4 (fun c => total 4 (fun r => hits a (add 8 (L_u c) (L_r r)))) =
            total 4 (fun c => hits c0 c * total 4 (fun r => hits r0 r)) := by
          apply congrArg (total 4); funext c; rw [← total_scale]; apply congrArg (total 4); funext r; exact hpt c r
        rw [h1]; simp only [diagonal 4 r0, Int.mul_one, diagonal 4 c0]
      have h1 : total 8 F = total 8 (fun a => total 4 (fun c => total 4 (fun r => F a * hits a (add 8 (L_u c) (L_r r))))) := by
        apply congrArg (total 8); funext a
        have : total 4 (fun c => total 4 (fun r => F a * hits a (add 8 (L_u c) (L_r r)))) =
            F a * total 4 (fun c => total 4 (fun r => hits a (add 8 (L_u c) (L_r r)))) := by
          rw [← total_scale]; apply congrArg (total 4); funext c; rw [← total_scale]
        rw [this, hpre a, Int.mul_one]
      have hswap1 : ∀ {m : Nat} (G : W m → W 4 → Int),
          total m (fun a => total 4 (fun c => G a c)) = total 4 (fun c => total m (fun a => G a c)) := by
        intro m; induction m with
        | zero => intro G; rfl
        | succ m ih =>
          intro G
          change total m (fun a => total 4 (fun c => G (false, a) c)) +
                 total m (fun a => total 4 (fun c => G (true, a) c)) =
                 total 4 (fun c => total m (fun a => G (false, a) c) + total m (fun a => G (true, a) c))
          rw [ih, ih, ← total_add]
      rw [h1, hswap1]; apply congrArg (total 4); funext c
      rw [hswap1]; apply congrArg (total 4); funext r
      have hpt (a : W 8) : F a * hits a (add 8 (L_u c) (L_r r)) =
          F (add 8 (L_u c) (L_r r)) * hits (add 8 (L_u c) (L_r r)) a := by
        unfold hits; by_cases e : a = add 8 (L_u c) (L_r r)
        · subst e; simp
        · have hne : ¬ add 8 (L_u c) (L_r r) = a := fun h' => e h'.symm; simp [e, hne]
      rw [funext hpt, total_scale, diagonal 8, Int.mul_one]
    rw [hsum_ur] at htot8
    rw [← htot8]; apply congrArg (total 4); funext s
    cases hs : isSZ s
    · simp only [Bool.false_eq_true, if_false]
      refine Eq.trans (total_zero 4).symm ?_
      apply congrArg (total 4); funext r
      have hZ : Zset f g (add 8 (L_u s) (L_r r)) = false := by rw [hZ_isSZ s r, hs]
      have hnz : lo f g (add 8 (L_u s) (L_r r)) ≠ 0 := by
        intro h0; unfold Zset at hZ; rw [h0] at hZ; simp at hZ
      rw [if_neg hnz]
    · simp [zeroCnt]
  have hSZ_tot_eq (s : W 4) (hs : isSZ s = true) :
      total 4 (fun y => z y s * z y s) = 64 - 4 * zeroCnt s := by
    have he := hcoset_energy s
    have hpt (r : W 4) :
        (lo f g (add 8 (L_u s) (L_r r)) / 2) * (lo f g (add 8 (L_u s) (L_r r)) / 2) =
        64 - 64 * (if lo f g (add 8 (L_u s) (L_r r)) = 0 then (1 : Int) else 0) := by
      have hZ : Zset f g (add 8 (L_u s) (L_r r)) = true := by rw [hZ_isSZ s r, hs]
      by_cases h0 : lo f g (add 8 (L_u s) (L_r r)) = 0
      · rw [h0, if_pos rfl]; decide
      · rw [if_neg h0, (hVhat_val _).2.1 hZ h0]; omega
    rw [funext hpt, total_sub, total_const, total_scale] at he
    have hm4 : many 4 = 16 := by decide
    rw [hm4] at he; change 16 * _ = 16 * 64 - 64 * zeroCnt s at he; omega
  -- Prove: AT MOST ONE nonzero `s ∈ SZ` has `zeroCnt s > 0`, AND for every `s ∈ SZ` with `zeroCnt s > 0`,
  -- `zeroCnt s = zeroCnt (zero 4)` (by translating the coset `Z0 ∩ (L_u s + R)` to `Z0 ∩ R`!),
  -- hence `zeroCnt (zero 4) = 8` (and all other 5 `zeroCnt s = 0`) OR `zeroCnt (zero 4) = 4` and ONE `s1 ≠ 0` has `zeroCnt s1 = 4`!
  have hzeroCnt_same (s : W 4) (hs : 1 ≤ zeroCnt s) : zeroCnt s = zeroCnt (zero 4) := by
    -- Pick one `r_star` with `lo (L_u s ⊕ L_r r_star) = 0`; then `r ↦ r ⊕ r_star` maps `Z0 ∩ (L_u s + R)` bijectively to `Z0 ∩ R`!
    have hex_r : ∃ r_s : W 4, lo f g (add 8 (L_u s) (L_r r_s)) = 0 := by
      cases h : (worlds 4).all (fun r => !decide (lo f g (add 8 (L_u s) (L_r r)) = 0))
      · obtain ⟨rs, _, hrs⟩ := all_false_exists _ _ h
        exact ⟨rs, by by_cases e : lo f g (add 8 (L_u s) (L_r rs)) = 0 <;> simp [e] at hrs ⊢⟩
      · exfalso; rw [List.all_eq_true] at h
        have h0 : zeroCnt s = 0 := by
          dsimp only [zeroCnt]; refine Eq.trans ?_ (total_zero 4)
          apply congrArg (total 4); funext r
          have hr' := h r (all_worlds 4 r)
          have hne : lo f g (add 8 (L_u s) (L_r r)) ≠ 0 := fun e => by rw [e, decide_eq_true rfl] at hr'; exact Bool.noConfusion hr'
          rw [if_neg hne]
        omega
    obtain ⟨rs, hrs⟩ := hex_r
    dsimp only [zeroCnt]
    rw [← sum_shift 4 rs (fun r => if lo f g (add 8 (L_u (zero 4)) (L_r r)) = 0 then (1 : Int) else 0)]
    apply congrArg (total 4); funext r
    have hiff : lo f g (add 8 (L_u s) (L_r r)) = 0 ↔ lo f g (add 8 (L_u (zero 4)) (L_r (add 4 rs r))) = 0 := by
      have heq : add 8 (L_u (zero 4)) (L_r (add 4 rs r)) =
          add 8 (add 8 (L_u s) (L_r rs)) (add 8 (L_u s) (L_r r)) := by
        dsimp only [L_u, L_r]; rw [lin4_zero, add_zero_left, lin4_add]
        rw [Balanced242Plateau.add_assoc', ← Balanced242Plateau.add_assoc' 8 (lin4 r0 r1 r2 r3 rs) (lin4 u1 v1 u2 v2 s),
            add_comm 8 (lin4 r0 r1 r2 r3 rs) (lin4 u1 v1 u2 v2 s),
            Balanced242Plateau.add_assoc' 8 (lin4 u1 v1 u2 v2 s),
            ← Balanced242Plateau.add_assoc', add_self, add_zero_left]
      constructor
      · intro h; rw [heq]; exact hZ0_sub _ _ hrs h
      · intro h
        have h2 := hZ0_sub _ _ hrs h
        rw [heq, ← Balanced242Plateau.add_assoc', add_self, add_zero_left] at h2; exact h2
    by_cases h1 : lo f g (add 8 (L_u s) (L_r r)) = 0
    · simp [h1, hiff.mp h1]
    · have h2 : ¬ lo f g (add 8 (L_u (zero 4)) (L_r (add 4 rs r))) = 0 := fun e => h1 (hiff.mpr e)
      simp [h1, h2]
  have hzeroCnt_atmost1 (s1 s2 : W 4) (h1 : isSZ s1 = true) (h2 : isSZ s2 = true)
      (hn1 : s1 ≠ zero 4) (hn2 : s2 ≠ zero 4) (hne : s1 ≠ s2)
      (hp1 : 1 ≤ zeroCnt s1) (hp2 : 1 ≤ zeroCnt s2) : False := by
    have get_pt (s : W 4) (hp : 1 ≤ zeroCnt s) : ∃ r : W 4, lo f g (add 8 (L_u s) (L_r r)) = 0 := by
      cases h : (worlds 4).all (fun r => !decide (lo f g (add 8 (L_u s) (L_r r)) = 0))
      · obtain ⟨rs, _, hrs⟩ := all_false_exists _ _ h
        exact ⟨rs, by by_cases e : lo f g (add 8 (L_u s) (L_r rs)) = 0 <;> simp [e] at hrs ⊢⟩
      · exfalso; rw [List.all_eq_true] at h
        have h0 : zeroCnt s = 0 := by
          dsimp only [zeroCnt]; refine Eq.trans ?_ (total_zero 4)
          apply congrArg (total 4); funext r
          have hr' := h r (all_worlds 4 r)
          have hne' : lo f g (add 8 (L_u s) (L_r r)) ≠ 0 := fun e => by rw [e, decide_eq_true rfl] at hr'; exact Bool.noConfusion hr'
          rw [if_neg hne']
        omega
    obtain ⟨ra, hra⟩ := get_pt s1 hp1
    obtain ⟨rb, hrb⟩ := get_pt s2 hp2
    have hsum := hZ0_sub _ _ hra hrb
    have heq : add 8 (add 8 (L_u s1) (L_r ra)) (add 8 (L_u s2) (L_r rb)) =
        add 8 (L_u (add 4 s1 s2)) (L_r (add 4 ra rb)) := by
      dsimp only [L_u, L_r]; rw [lin4_add, lin4_add]
      rw [Balanced242Plateau.add_assoc', ← Balanced242Plateau.add_assoc' 8 (lin4 r0 r1 r2 r3 ra),
          add_comm 8 (lin4 r0 r1 r2 r3 ra) (lin4 u1 v1 u2 v2 s2),
          Balanced242Plateau.add_assoc' 8 (lin4 u1 v1 u2 v2 s2), ← Balanced242Plateau.add_assoc']
    rw [heq] at hsum
    have hZtrue : Zset f g (add 8 (L_u (add 4 s1 s2)) (L_r (add 4 ra rb))) = true := by
      unfold Zset; rw [hsum]; decide
    rw [hZ_isSZ, isSZ_sum_nonzero s1 s2 h1 h2 hn1 hn2 hne] at hZtrue
    exact Bool.noConfusion hZtrue
  have hzero0_ge1 : 1 ≤ zeroCnt (zero 4) := by
    have hp := point_le_total 4 (fun r => if lo f g (add 8 (L_u (zero 4)) (L_r r)) = 0 then (1 : Int) else 0)
      (fun r => by dsimp only; split <;> decide) (zero 4)
    have h0 : add 8 (L_u (zero 4)) (L_r (zero 4)) = zero 8 := by dsimp only [L_u, L_r]; rw [lin4_zero, lin4_zero, add_zero_left]
    rw [h0, dc, if_pos rfl] at hp; exact hp
  have hzeroCnt_nn (s : W 4) : 0 ≤ zeroCnt s := total_nonneg _ (fun r => by split <;> decide)
  -- Therefore EVERY `s ∈ SZ` has `zeroCnt s ∈ {0, 4, 8}` (so `16 ∣ tot[s]` and `tot[s] ≤ 64`),
  -- AND at least 4 cosets in `SZ` have `zeroCnt s = 0` (`tot[s] = 64`)!
  have hSZ_mod16 (s : W 4) (hs : isSZ s = true) :
      (zeroCnt s = 0 ∨ zeroCnt s = 4 ∨ zeroCnt s = 8) ∧
      total 4 (fun y => z y s * z y s) % 16 = 0 ∧
      total 4 (fun y => z y s * z y s) ≤ 64 := by
    have hcnt : total 4 (fun a => if isSZ a && decide (1 ≤ zeroCnt a) then (1 : Int) else 0) ≤ 2 := by
      -- At most `{zero 4}` plus at most 1 nonzero `s1 ∈ SZ`!
      cases hex : (worlds 4).all (fun a => !(isSZ a && decide (a ≠ zero 4) && decide (1 ≤ zeroCnt a)))
      · obtain ⟨s1, _, hs1⟩ := all_false_exists _ _ hex
        have hs1_SZ : isSZ s1 = true := by cases e : isSZ s1 <;> rw [e] at hs1 <;> simp at hs1 ⊢
        have hs1_ne : s1 ≠ zero 4 := by by_cases e : s1 = zero 4 <;> simp [e] at hs1 ⊢
        have hs1_pos : 1 ≤ zeroCnt s1 := by by_cases e : 1 ≤ zeroCnt s1 <;> simp [e] at hs1 ⊢
        have hle (a : W 4) : (if isSZ a && decide (1 ≤ zeroCnt a) then (1 : Int) else 0) ≤
            hits (zero 4) a + hits s1 a := by
          unfold hits
          by_cases e0 : zero 4 = a
          · subst e0; simp; split <;> omega
          · by_cases e1 : s1 = a
            · subst e1; simp [e0]; split <;> omega
            · simp only [e0, e1, if_false, Int.add_zero]
              cases ha : isSZ a
              · simp
              · by_cases hp : 1 ≤ zeroCnt a
                · exact False.elim (hzeroCnt_atmost1 s1 a hs1_SZ ha hs1_ne (fun h => e0 h.symm) e1 hs1_pos hp)
                · simp [hp]
        have hm := total_mono 4 _ _ hle
        rw [total_add, diagonal 4 (zero 4), diagonal 4 s1] at hm; exact hm
      · rw [List.all_eq_true] at hex
        have hle (a : W 4) : (if isSZ a && decide (1 ≤ zeroCnt a) then (1 : Int) else 0) ≤ hits (zero 4) a := by
          have ha := hex a (all_worlds 4 a); unfold hits
          by_cases e0 : zero 4 = a
          · subst e0; simp; split <;> omega
          · have hne : a ≠ zero 4 := fun h => e0 h.symm
            simp only [e0, if_false]
            cases hsz : isSZ a
            · simp
            · by_cases hp : 1 ≤ zeroCnt a
              · rw [hsz, decide_eq_true hne, decide_eq_true hp] at ha; simp at ha
              · simp [hp]
        have hm := total_mono 4 _ _ hle; rw [diagonal 4 (zero 4)] at hm; omega
    have hmul : total 4 (fun a => if isSZ a && decide (1 ≤ zeroCnt a) then (1 : Int) else 0) * zeroCnt (zero 4) = 8 := by
      have hcomm : total 4 (fun a => (if isSZ a && decide (1 ≤ zeroCnt a) then (1 : Int) else 0) * zeroCnt (zero 4)) =
          total 4 (fun a => if isSZ a && decide (1 ≤ zeroCnt a) then (1 : Int) else 0) * zeroCnt (zero 4) := by
        rw [Int.mul_comm, ← total_scale]; apply congrArg (total 4); funext a; exact Int.mul_comm _ _
      rw [← hcomm, ← hzeroCnt_sum]; apply congrArg (total 4); funext a
      cases ha : isSZ a
      · simp
      · by_cases hp : 1 ≤ zeroCnt a
        · simp [hp, hzeroCnt_same a hp, hzero0_ge1]
        · have h0 : zeroCnt a = 0 := by have := hzeroCnt_nn a; omega
          simp [hp, h0]
    have hpos_cnt : 1 ≤ total 4 (fun a => if isSZ a && decide (1 ≤ zeroCnt a) then (1 : Int) else 0) := by
      have hp := point_le_total 4 (fun a => if isSZ a && decide (1 ≤ zeroCnt a) then (1 : Int) else 0)
        (fun a => by dsimp only; split <;> decide) (zero 4)
      have hsz0 : isSZ (zero 4) = true := rfl
      rw [hsz0, decide_eq_true hzero0_ge1] at hp; simpa using hp
    have hcnt12 : total 4 (fun a => if isSZ a && decide (1 ≤ zeroCnt a) then (1 : Int) else 0) = 1 ∨
                  total 4 (fun a => if isSZ a && decide (1 ≤ zeroCnt a) then (1 : Int) else 0) = 2 := by omega
    have hz0_val : zeroCnt (zero 4) = 4 ∨ zeroCnt (zero 4) = 8 := by
      rcases hcnt12 with h1 | h1 <;> rw [h1] at hmul <;> omega
    have hzs_val : zeroCnt s = 0 ∨ zeroCnt s = 4 ∨ zeroCnt s = 8 := by
      by_cases hp : 1 ≤ zeroCnt s
      · rw [hzeroCnt_same s hp]; rcases hz0_val with h | h
        · right; left; exact h
        · right; right; exact h
      · left; have := hzeroCnt_nn s; omega
    have hte := hSZ_tot_eq s hs
    exact ⟨hzs_val, by omega, by omega⟩
  have hzero_free_ge4 :
      4 ≤ total 4 (fun s => if isSZ s && decide (zeroCnt s = 0) then (1 : Int) else 0) := by
    -- Out of the 6 points of `SZ`, at most 2 have `1 ≤ zeroCnt s`!
    have hsz6 : total 4 (fun s => bind (isSZ s)) = 6 := by decide
    have hpos_le2 : total 4 (fun s => if isSZ s && decide (1 ≤ zeroCnt s) then (1 : Int) else 0) ≤ 2 := by
      cases hex : (worlds 4).all (fun a => !(isSZ a && decide (a ≠ zero 4) && decide (1 ≤ zeroCnt a)))
      · obtain ⟨s1, _, hs1⟩ := all_false_exists _ _ hex
        have hs1_SZ : isSZ s1 = true := by cases e : isSZ s1 <;> rw [e] at hs1 <;> simp at hs1 ⊢
        have hs1_ne : s1 ≠ zero 4 := by by_cases e : s1 = zero 4 <;> simp [e] at hs1 ⊢
        have hs1_pos : 1 ≤ zeroCnt s1 := by by_cases e : 1 ≤ zeroCnt s1 <;> simp [e] at hs1 ⊢
        have hle (a : W 4) : (if isSZ a && decide (1 ≤ zeroCnt a) then (1 : Int) else 0) ≤
            hits (zero 4) a + hits s1 a := by
          unfold hits
          by_cases e0 : zero 4 = a
          · subst e0; simp; split <;> omega
          · by_cases e1 : s1 = a
            · subst e1; simp [e0]; split <;> omega
            · simp only [e0, e1, if_false, Int.add_zero]
              cases ha : isSZ a
              · simp
              · by_cases hp : 1 ≤ zeroCnt a
                · exact False.elim (hzeroCnt_atmost1 s1 a hs1_SZ ha hs1_ne (fun h => e0 h.symm) e1 hs1_pos hp)
                · simp [hp]
        have hm := total_mono 4 _ _ hle; rw [total_add, diagonal 4, diagonal 4] at hm; exact hm
      · rw [List.all_eq_true] at hex
        have hle (a : W 4) : (if isSZ a && decide (1 ≤ zeroCnt a) then (1 : Int) else 0) ≤ hits (zero 4) a := by
          have ha := hex a (all_worlds 4 a); unfold hits
          by_cases e0 : zero 4 = a
          · subst e0; simp; split <;> omega
          · have hne : a ≠ zero 4 := fun h => e0 h.symm
            simp only [e0, if_false]
            cases hsz : isSZ a
            · simp
            · by_cases hp : 1 ≤ zeroCnt a
              · rw [hsz, decide_eq_true hne, decide_eq_true hp] at ha; simp at ha
              · simp [hp]
        have hm := total_mono 4 _ _ hle; rw [diagonal 4] at hm; omega
    have hpart : total 4 (fun s => if isSZ s && decide (zeroCnt s = 0) then (1 : Int) else 0) +
                 total 4 (fun s => if isSZ s && decide (1 ≤ zeroCnt s) then (1 : Int) else 0) = 6 := by
      rw [← total_add, ← hsz6]; apply congrArg (total 4); funext s
      have hnn := hzeroCnt_nn s
      cases isSZ s
      · simp [Balanced242Plateau.ind]
      · by_cases h0 : zeroCnt s = 0
        · have h1 : ¬ 1 ≤ zeroCnt s := by omega
          simp [h0, h1, Balanced242Plateau.ind]
        · have h1 : 1 ≤ zeroCnt s := by omega
          simp [h0, h1, Balanced242Plateau.ind]
    omega
  -- Step 4: Apply the 729-cell kernel table to EVERY cell `v y` (`y : W 4`)!
  have hcell_ok (y : W 4) :
      let m := mcell y
      let eSZc := total 4 (fun c => if !isSZ c then z y c * z y c else 0)
      (m % 2 = 1 → 11 ≤ m ∧ eSZc = 90 ∧ ∀ c, isSZ c = false → z y c * z y c = 9) ∧
      (m % 2 = 0 →
        (m = 0 ∨ m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12 ∨ m = 16) ∧
        (∀ c, isSZ c = false → z y c * z y c = 0 ∨ z y c * z y c = 36 ∨ z y c * z y c = 144) ∧
        (m = 0 → eSZc = 0 ∧ ∀ s, isSZ s = true → z y s * z y s = 0) ∧
        (m = 6 → eSZc = 0 ∧ ∀ s, isSZ s = true → z y s * z y s = 16) ∧
        (m = 8 → eSZc = 0 ∧ (∀ s, isSZ s = true → z y s * z y s = 0 ∨ z y s * z y s = 64) ∧
                 total 4 (fun s => if isSZ s && decide (z y s * z y s = 64) then (1 : Int) else 0) = 2) ∧
        (m = 10 → eSZc = 144 ∧ (∀ s, isSZ s = true → z y s * z y s = 0 ∨ z y s * z y s = 4) ∧
                  total 4 (fun s => if isSZ s && decide (z y s * z y s = 4) then (1 : Int) else 0) = 4 ∧
                  ∀ s1 s2, isSZ s1 = true → isSZ s2 = true → s1 ≠ s2 → z y s1 = 0 → z y s2 = 0 →
                    z y (pickC s1 s2) * z y (pickC s1 s2) = 36) ∧
        (m = 12 → eSZc = 144 ∧ (∀ s, isSZ s = true → z y s * z y s = 0 ∨ z y s * z y s = 16) ∧
                  total 4 (fun s => if isSZ s && decide (z y s * z y s = 16) then (1 : Int) else 0) = 3) ∧
        (m = 16 → eSZc = 0 ∧ (∀ s, isSZ s = true → z y s * z y s = 0 ∨ z y s * z y s = 256) ∧
                  total 4 (fun s => if isSZ s && decide (z y s * z y s = 256) then (1 : Int) else 0) = 1)) := by
    have htern (x : W 4) : v y x = -1 ∨ v y x = 0 ∨ v y x = 1 := by
      dsimp only [v]; unfold Vtbl; cases f _ <;> cases g _ <;> decide
    exact cell4_spec (v y) htern (fun c hc => hz_mod3 y c hc)
  -- Step 5: Total `eSZc` sum across all 16 cells = `10 * 144 = 1440`, forcing `r = 0` (ALL 16 cells EVEN)!
  have heSZc_tot : total 4 (fun y => total 4 (fun c => if !isSZ c then z y c * z y c else 0)) = 1440 := by
    rw [swap]
    have hinner (c : W 4) : total 4 (fun y => if !isSZ c then z y c * z y c else 0) =
        if !isSZ c then 144 else 0 := by
      cases hc : isSZ c
      · simp only [Bool.not_false, if_true]; exact hSZc_tot c hc
      · simp only [Bool.not_true, Bool.false_eq_true, if_false, total_zero]
    rw [funext hinner]; decide
  -- Count odd cells `n_odd`, and even cells `n0c, n6c, n8c, n10c, n12c, n16c`!
  let n_odd : Int := total 4 (fun y => if mcell y % 2 = 1 then (1 : Int) else 0)
  let n0c   : Int := total 4 (fun y => if mcell y = 0 then (1 : Int) else 0)
  let n6c   : Int := total 4 (fun y => if mcell y = 6 then (1 : Int) else 0)
  let n8c   : Int := total 4 (fun y => if mcell y = 8 then (1 : Int) else 0)
  let n10c  : Int := total 4 (fun y => if mcell y = 10 then (1 : Int) else 0)
  let n12c  : Int := total 4 (fun y => if mcell y = 12 then (1 : Int) else 0)
  let n16c  : Int := total 4 (fun y => if mcell y = 16 then (1 : Int) else 0)
  -- First exclude `mcell y = 16` immediately (would give `z y s ^ 2 = 256 > 64 ≥ tot[s]`!)!
  have hno_m16 (y : W 4) : mcell y ≠ 16 := by
    intro hm16
    have hc := (hcell_ok y).2 (by rw [hm16]; decide)
    have ⟨_, _, hcnt1⟩ := hc.2.2.2.2.2.2.2 hm16
    cases h : (worlds 4).all (fun s => !(isSZ s && decide (z y s * z y s = 256)))
    · obtain ⟨s, _, hs⟩ := all_false_exists _ _ h
      have hsZ : isSZ s = true := by cases e : isSZ s <;> rw [e] at hs <;> simp at hs ⊢
      have h256 : z y s * z y s = 256 := by by_cases e : z y s * z y s = 256 <;> simp [e] at hs ⊢
      have hp := point_le_total 4 (fun u => z u s * z u s) (fun u => by
        have : 0 ≤ z u s ∨ z u s ≤ 0 := by omega
        rcases this with h' | h'
        · exact Int.mul_nonneg h' h'
        · exact Int.mul_nonneg_of_nonpos_of_nonpos h' h') y
      have hle64 := (hSZ_mod16 s hsZ).2.2
      omega
    · rw [List.all_eq_true] at h
      have h0 : total 4 (fun s => if isSZ s && decide (z y s * z y s = 256) then (1 : Int) else 0) = 0 := by
        refine Eq.trans ?_ (total_zero 4)
        apply congrArg (total 4); funext s
        have ha := h s (all_worlds 4 s)
        cases e : isSZ s && decide (z y s * z y s = 256) <;> simp [e] at ha ⊢
      omega
  -- Prove `n_odd = 0`!
  have hn_odd_0 : n_odd = 0 := by
    -- Pick ONE `c0 ∈ SZc` (`(false, false, true, true, ())`): mod 36 gives `9 * n_odd ≡ 144 ≡ 0 (mod 36)`, so `4 ∣ n_odd`!
    let c0 : W 4 := (false, (false, (true, (true, ()))))
    have hc0 : isSZ c0 = false := rfl
    have hdiv36 : (total 4 (fun y => z y c0 * z y c0) - 9 * n_odd) % 36 = 0 := by
      have hpt (y : W 4) : (z y c0 * z y c0 - 9 * (if mcell y % 2 = 1 then (1 : Int) else 0)) % 36 = 0 := by
        have hm_nn : 0 ≤ mcell y := total_nonneg _ (fun x => by
          have : 0 ≤ v y x ∨ v y x ≤ 0 := by omega
          rcases this with h | h; exact Int.mul_nonneg h h; exact Int.mul_nonneg_of_nonpos_of_nonpos h h)
        by_cases hodd : mcell y % 2 = 1
        · rw [if_pos hodd, ((hcell_ok y).1 hodd).2.2 c0 hc0]; decide
        · rw [if_neg hodd]; have hev : mcell y % 2 = 0 := by omega
          rcases ((hcell_ok y).2 hev).2.1 c0 hc0 with h | h | h <;> rw [h] <;> decide
      have aux : ∀ {m : Nat} (F : W m → Int), (∀ y, F y % 36 = 0) → total m F % 36 = 0 := by
        intro m; induction m with
        | zero => intro F hF; exact hF ()
        | succ m ih =>
          intro F hF
          change (total m (fun a => F (false, a)) + total m (fun a => F (true, a))) % 36 = 0
          have h1 := ih (fun a => F (false, a)) (fun a => hF (false, a))
          have h2 := ih (fun a => F (true, a)) (fun a => hF (true, a)); omega
      have h := aux _ hpt; rw [total_sub, total_scale] at h; exact h
    rw [hSZc_tot c0 hc0] at hdiv36
    -- Also `heSZc_tot = 90 * n_odd + 144 * (n10c + n12c) = 1440`!
    have heSZc_eq : 90 * n_odd + 144 * (n10c + n12c) = 1440 := by
      rw [← heSZc_tot]
      dsimp only [n_odd, n10c, n12c]
      rw [← total_add, ← total_scale, ← total_scale, ← total_add]
      apply congrArg (total 4); funext y
      have hm_nn : 0 ≤ mcell y := total_nonneg _ (fun x => by
        have : 0 ≤ v y x ∨ v y x ≤ 0 := by omega
        rcases this with h | h; exact Int.mul_nonneg h h; exact Int.mul_nonneg_of_nonpos_of_nonpos h h)
      by_cases hodd : mcell y % 2 = 1
      · have hne10 : mcell y ≠ 10 := by omega
        have hne12 : mcell y ≠ 12 := by omega
        rw [if_pos hodd, if_neg hne10, if_neg hne12, ((hcell_ok y).1 hodd).2.1]; omega
      · have hev : mcell y % 2 = 0 := by omega
        have hc := (hcell_ok y).2 hev
        rcases hc.1 with h | h | h | h | h | h
        · rw [if_neg hodd, (hc.2.2.1 h).1, h]; decide
        · rw [if_neg hodd, (hc.2.2.2.1 h).1, h]; decide
        · rw [if_neg hodd, (hc.2.2.2.2.1 h).1, h]; decide
        · rw [if_neg hodd, (hc.2.2.2.2.2.1 h).1, h]; decide
        · rw [if_neg hodd, (hc.2.2.2.2.2.2.1 h).1, h]; decide
        · exact absurd h (hno_m16 y)
    -- And `11 * n_odd + 10 * (n10c + n12c) ≤ 112`!
    have hm_lb : 11 * n_odd + 10 * (n10c + n12c) ≤ 112 := by
      rw [← hm_sum]; dsimp only [n_odd, n10c, n12c]
      rw [← total_add, ← total_scale, ← total_scale, ← total_add]
      apply total_mono 4; intro y
      have hm_nn : 0 ≤ mcell y := total_nonneg _ (fun x => by
        have : 0 ≤ v y x ∨ v y x ≤ 0 := by omega
        rcases this with h | h; exact Int.mul_nonneg h h; exact Int.mul_nonneg_of_nonpos_of_nonpos h h)
      by_cases hodd : mcell y % 2 = 1
      · have h11 := ((hcell_ok y).1 hodd).1
        have hne10 : mcell y ≠ 10 := by omega
        have hne12 : mcell y ≠ 12 := by omega
        rw [if_pos hodd, if_neg hne10, if_neg hne12]; omega
      · rw [if_neg hodd]
        by_cases h10 : mcell y = 10
        · rw [if_pos h10, if_neg (by omega)]; omega
        · by_cases h12 : mcell y = 12
          · rw [if_neg h10, if_pos h12]; omega
          · rw [if_neg h10, if_neg h12]; omega
    have hnn_odd : 0 ≤ n_odd := total_nonneg _ (fun _ => by split <;> decide)
    have hnn_10 : 0 ≤ n10c := total_nonneg _ (fun _ => by split <;> decide)
    have hnn_12 : 0 ≤ n12c := total_nonneg _ (fun _ => by split <;> decide)
    omega
  -- Every single cell is EVEN and `mcell y ∈ {0, 6, 8, 10, 12}`!
  have hall_even (y : W 4) : mcell y = 0 ∨ mcell y = 6 ∨ mcell y = 8 ∨ mcell y = 10 ∨ mcell y = 12 := by
    have hm_nn : 0 ≤ mcell y := total_nonneg _ (fun x => by
      have : 0 ≤ v y x ∨ v y x ≤ 0 := by omega
      rcases this with h | h; exact Int.mul_nonneg h h; exact Int.mul_nonneg_of_nonpos_of_nonpos h h)
    have hev : mcell y % 2 = 0 := by
      by_cases hodd : mcell y % 2 = 1
      · exfalso
        have hp := point_le_total 4 (fun u => if mcell u % 2 = 1 then (1 : Int) else 0)
          (fun _ => by dsimp only; split <;> decide) y
        change (if mcell y % 2 = 1 then (1 : Int) else 0) ≤ n_odd at hp
        rw [if_pos hodd, hn_odd_0] at hp; omega
      · omega
    rcases ((hcell_ok y).2 hev).1 with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact absurd h (hno_m16 y)
  -- Exact count equations: `n0c + n6c + n8c + n10c + n12c = 16`, `n10c + n12c = 10`, `6*n6c + 8*n8c + 10*n10c + 12*n12c = 112`!
  have hcnt16 : n0c + n6c + n8c + n10c + n12c = 16 := by
    dsimp only [n0c, n6c, n8c, n10c, n12c]
    rw [← total_add, ← total_add, ← total_add, ← total_add]
    have hpt (y : W 4) :
        ((((if mcell y = 0 then (1 : Int) else 0) + (if mcell y = 6 then 1 else 0)) +
           (if mcell y = 8 then 1 else 0)) + (if mcell y = 10 then 1 else 0)) +
          (if mcell y = 12 then 1 else 0) = 1 := by
      rcases hall_even y with h | h | h | h | h <;> rw [h] <;> decide
    rw [funext hpt, total_const]; decide
  have h10_12 : n10c + n12c = 10 := by
    have heSZc_eq : 144 * (n10c + n12c) = 1440 := by
      rw [← heSZc_tot]; dsimp only [n10c, n12c]; rw [← total_add, ← total_scale]
      apply congrArg (total 4); funext y
      rcases hall_even y with h | h | h | h | h
      · rw [(((hcell_ok y).2 (by rw [h]; decide)).2.2.1 h).1, h]; decide
      · rw [(((hcell_ok y).2 (by rw [h]; decide)).2.2.2.1 h).1, h]; decide
      · rw [(((hcell_ok y).2 (by rw [h]; decide)).2.2.2.2.1 h).1, h]; decide
      · rw [(((hcell_ok y).2 (by rw [h]; decide)).2.2.2.2.2.1 h).1, h]; decide
      · rw [(((hcell_ok y).2 (by rw [h]; decide)).2.2.2.2.2.2.1 h).1, h]; decide
    omega
  have hm_eq_lin : 6 * n6c + 8 * n8c + 10 * n10c + 12 * n12c = 112 := by
    rw [← hm_sum]; dsimp only [n6c, n8c, n10c, n12c]
    rw [← total_scale, ← total_scale, ← total_scale, ← total_scale,
        ← total_add, ← total_add, ← total_add]
    apply congrArg (total 4); funext y
    rcases hall_even y with h | h | h | h | h <;> rw [h] <;> decide
  have hnn0 : 0 ≤ n0c := total_nonneg _ (fun _ => by split <;> decide)
  have hnn6 : 0 ≤ n6c := total_nonneg _ (fun _ => by split <;> decide)
  have hnn8 : 0 ≤ n8c := total_nonneg _ (fun _ => by split <;> decide)
  have hnn10 : 0 ≤ n10c := total_nonneg _ (fun _ => by split <;> decide)
  have hnn12 : 0 ≤ n12c := total_nonneg _ (fun _ => by split <;> decide)
  -- Universal mod-16 lemma: for EVERY `s ∈ SZ`, the count of `m = 10` cells hitting `s` (`z y s ^ 2 = 4`) is DIVISIBLE BY 4!
  let hits10 (s : W 4) : Int :=
    total 4 (fun y => if mcell y = 10 && decide (z y s * z y s = 4) then (1 : Int) else 0)
  have hhits10_div4 (s : W 4) (hs : isSZ s = true) : hits10 s % 4 = 0 := by
    have hmod16 := (hSZ_mod16 s hs).2.1
    have hdiff : (total 4 (fun y => z y s * z y s) - 4 * hits10 s) % 16 = 0 := by
      dsimp only [hits10]; rw [← total_scale, ← total_sub]
      have aux : ∀ {m : Nat} (F : W m → Int), (∀ y, F y % 16 = 0) → total m F % 16 = 0 := by
        intro m; induction m with
        | zero => intro F hF; exact hF ()
        | succ m ih =>
          intro F hF
          change (total m (fun a => F (false, a)) + total m (fun a => F (true, a))) % 16 = 0
          have h1 := ih (fun a => F (false, a)) (fun a => hF (false, a))
          have h2 := ih (fun a => F (true, a)) (fun a => hF (true, a)); omega
      apply aux; intro y
      rcases hall_even y with h | h | h | h | h
      · have hz := (((hcell_ok y).2 (by rw [h]; decide)).2.2.1 h).2 s hs; rw [hz, h]; decide
      · have hz := (((hcell_ok y).2 (by rw [h]; decide)).2.2.2.1 h).2 s hs; rw [hz, h]; decide
      · rcases ((((hcell_ok y).2 (by rw [h]; decide)).2.2.2.2.1 h).2.1 s hs) with hz | hz <;> rw [hz, h] <;> decide
      · rcases ((((hcell_ok y).2 (by rw [h]; decide)).2.2.2.2.2.1 h).2.1 s hs) with hz | hz <;> rw [hz, h] <;> decide
      · rcases ((((hcell_ok y).2 (by rw [h]; decide)).2.2.2.2.2.2.1 h).2.1 s hs) with hz | hz <;> rw [hz, h] <;> decide
    omega
  have hhits10_sum : total 4 (fun s => if isSZ s then hits10 s else 0) = 4 * n10c := by
    have hpt (s : W 4) : (if isSZ s then hits10 s else 0) =
        total 4 (fun y => if isSZ s && decide (mcell y = 10) && decide (z y s * z y s = 4) then (1 : Int) else 0) := by
      cases hs : isSZ s
      · simp [total_zero]
      · simp [hits10]
    rw [funext hpt, swap]; dsimp only [n10c]; rw [← total_scale]
    apply congrArg (total 4); funext y
    by_cases h10 : mcell y = 10
    · rw [if_pos h10, Int.mul_one]
      have h4 := (((hcell_ok y).2 (by rw [h10]; decide)).2.2.2.2.2.1 h10).2.2.1
      refine Eq.trans ?_ h4
      apply congrArg (total 4); funext s; simp [h10, Bool.and_true]
    · rw [if_neg h10, Int.mul_zero]
      refine Eq.trans ?_ (total_zero 4)
      apply congrArg (total 4); funext s; simp [h10, Bool.and_false]
  have hhits10_le (s : W 4) : 0 ≤ hits10 s ∧ hits10 s ≤ n10c := by
    constructor
    · exact total_nonneg _ (fun _ => by split <;> decide)
    · apply total_mono 4; intro y
      by_cases h10 : mcell y = 10
      · simp [h10]; split <;> omega
      · simp [h10]
  -- EXACT 4-WAY SPLIT: `(n12c, n10c, n8c, n6c) ∈ {(3,7,0,1), (2,8,1,0), (6,4,0,0), (0,10,0,2)}`!
  have hcases : (n12c = 3 ∧ n10c = 7 ∧ n8c = 0 ∧ n6c = 1) ∨
                (n12c = 2 ∧ n10c = 8 ∧ n8c = 1 ∧ n6c = 0) ∨
                (n12c = 6 ∧ n10c = 4 ∧ n8c = 0 ∧ n6c = 0) ∨
                (n12c = 0 ∧ n10c = 10 ∧ n8c = 0 ∧ n6c = 2) := by
    have h8v : n8c = 0 ∨ n8c = 1 := by omega
    rcases h8v with h8 | h8
    · have h6v : n6c = 0 ∨ n6c = 1 ∨ n6c = 2 := by omega
      rcases h6v with h6 | h6 | h6
      · right; right; left; omega
      · left; omega
      · right; right; right; omega
    · right; left; omega
  rcases hcases with ⟨hn12, hn10, hn8, hn6⟩ | ⟨hn12, hn10, hn8, hn6⟩ |
                     ⟨hn12, hn10, hn8, hn6⟩ | ⟨hn12, hn10, hn8, hn6⟩
  · -- ======================== CASE `k = 3`: `28 ≤ 24` IN ONE LINE! ========================
    have hle24 : total 4 (fun s => if isSZ s then hits10 s else 0) ≤ 24 := by
      have hpt (s : W 4) : (if isSZ s then hits10 s else 0) ≤ 4 * bind (isSZ s) := by
        cases hs : isSZ s
        · simp [Balanced242Plateau.ind]
        · simp only [if_true, Balanced242Plateau.ind]
          have hd4 := hhits10_div4 s hs; have ⟨h0, hle⟩ := hhits10_le s; omega
      have hm := total_mono 4 _ _ hpt; rw [total_scale] at hm
      have h6 : total 4 (fun s => bind (isSZ s)) = 6 := by decide
      rw [h6] at hm; omega
    omega
  · -- ======================== CASE `k = 2`: `288 ≤ 144` IN TWO LINES! ========================
    -- Pick the unique `m = 8` cell `y8`, and its TWO saturated cosets `s1 ≠ s2` in `SZ` (`z y8 s_i ^ 2 = 64`)!
    have hex_y8 : ∃ y8 : W 4, mcell y8 = 8 := by
      cases h : (worlds 4).all (fun y => !decide (mcell y = 8))
      · obtain ⟨y8, _, hy8⟩ := all_false_exists _ _ h
        exact ⟨y8, by by_cases e : mcell y8 = 8 <;> simp [e] at hy8 ⊢⟩
      · exfalso; rw [List.all_eq_true] at h
        have h0 : n8c = 0 := by
          dsimp only [n8c]; refine Eq.trans ?_ (total_zero 4)
          apply congrArg (total 4); funext y
          have hy' := h y (all_worlds 4 y)
          have hne : mcell y ≠ 8 := fun e => by rw [e, decide_eq_true rfl] at hy'; exact Bool.noConfusion hy'
          rw [if_neg hne]
        omega
    obtain ⟨y8, hy8⟩ := hex_y8
    have hc8 := (((hcell_ok y8).2 (by rw [hy8]; decide)).2.2.2.2.1 hy8).2.2
    -- Extract two distinct `s1, s2 ∈ SZ` with `z y8 s1 ^ 2 = 64` and `z y8 s2 ^ 2 = 64`!
    let P8 (s : W 4) : Bool := isSZ s && decide (z y8 s * z y8 s = 64)
    have hc8' : total 4 (fun s => if P8 s then (1 : Int) else 0) = 2 := hc8
    have hex_s1 : ∃ s1 : W 4, P8 s1 = true := by
      cases h : (worlds 4).all (fun s => !P8 s)
      · obtain ⟨s1, _, hs1⟩ := all_false_exists _ _ h
        exact ⟨s1, by cases e : P8 s1 <;> rw [e] at hs1 <;> simp at hs1 ⊢⟩
      · exfalso; rw [List.all_eq_true] at h
        have h0 : total 4 (fun s => if P8 s then (1 : Int) else 0) = 0 := by
          refine Eq.trans ?_ (total_zero 4)
          apply congrArg (total 4); funext s
          have ha := h s (all_worlds 4 s); cases e : P8 s <;> simp [e] at ha ⊢
        omega
    obtain ⟨s1, hs1⟩ := hex_s1
    have hex_s2 : ∃ s2 : W 4, s2 ≠ s1 ∧ P8 s2 = true := by
      cases h : (worlds 4).all (fun s => decide (s = s1) || !P8 s)
      · obtain ⟨s2, _, hs2⟩ := all_false_exists _ _ h
        have hne : s2 ≠ s1 := by intro e; subst e; simp at hs2
        have hp : P8 s2 = true := by cases e : P8 s2 <;> rw [e] at hs2 <;> simp [hne] at hs2 ⊢
        exact ⟨s2, hne, hp⟩
      · exfalso; rw [List.all_eq_true] at h
        have hle1 : total 4 (fun s => if P8 s then (1 : Int) else 0) ≤ 1 := by
          have hm := total_mono 4 (fun s => if P8 s then (1 : Int) else 0) (hits s1) (fun s => by
            have ha := h s (all_worlds 4 s); unfold hits
            by_cases e : s1 = s
            · subst e; simp; split <;> omega
            · have hne : s ≠ s1 := fun h' => e h'.symm
              rw [decide_eq_false hne, Bool.false_or] at ha
              cases ep : P8 s <;> simp [e, ep] at ha ⊢)
          rw [diagonal 4 s1] at hm; exact hm
        omega
    obtain ⟨s2, hs2_ne, hs2⟩ := hex_s2
    have hs1_SZ : isSZ s1 = true := by dsimp only [P8] at hs1; cases e : isSZ s1 <;> rw [e] at hs1 <;> simp at hs1 ⊢
    have hs2_SZ : isSZ s2 = true := by dsimp only [P8] at hs2; cases e : isSZ s2 <;> rw [e] at hs2 <;> simp at hs2 ⊢
    have hz8_s1 : z y8 s1 * z y8 s1 = 64 := by dsimp only [P8] at hs1; by_cases e : z y8 s1 * z y8 s1 = 64 <;> simp [e] at hs1 ⊢
    have hz8_s2 : z y8 s2 * z y8 s2 = 64 := by dsimp only [P8] at hs2; by_cases e : z y8 s2 * z y8 s2 = 64 <;> simp [e] at hs2 ⊢
    -- For ANY `y ≠ y8`, `z y s1 = 0` AND `z y s2 = 0` (since `tot[s_i] ≤ 64 = z y8 s_i ^ 2`!)!
    have hzero_other (s : W 4) (hsZ : isSZ s = true) (h64 : z y8 s * z y8 s = 64)
        (y : W 4) (hy_ne : y ≠ y8) : z y s = 0 := by
      have hge2 : z y8 s * z y8 s + z y s * z y s ≤ total 4 (fun u => z u s * z u s) := by
        have hle (u : W 4) : (z y8 s * z y8 s) * hits y8 u + (z y s * z y s) * hits y u ≤ z u s * z u s := by
          unfold hits
          by_cases e1 : y8 = u
          · subst e1; simp [hy_ne]
          · by_cases e2 : y = u
            · subst e2; simp [e1]
            · simp only [e1, e2, if_false, Int.mul_zero, Int.add_zero]
              have : 0 ≤ z u s ∨ z u s ≤ 0 := by omega
              rcases this with h' | h'; exact Int.mul_nonneg h' h'; exact Int.mul_nonneg_of_nonpos_of_nonpos h' h'
        have hm := total_mono 4 _ _ hle
        rw [total_add, total_scale, total_scale, diagonal 4 y8, diagonal 4 y] at hm; omega
      have hle64 := (hSZ_mod16 s hsZ).2.2
      have hsq0 : z y s * z y s = 0 := by
        have : 0 ≤ z y s * z y s := by
          have : 0 ≤ z y s ∨ z y s ≤ 0 := by omega
          rcases this with h' | h'; exact Int.mul_nonneg h' h'; exact Int.mul_nonneg_of_nonpos_of_nonpos h' h'
        omega
      by_cases h0 : z y s = 0
      · exact h0
      · exfalso
        have : z y s * z y s ≥ 1 := by
          have : 1 ≤ z y s ∨ z y s ≤ -1 := by omega
          rcases this with h' | h'
          · exact Int.mul_le_mul h' h' (by decide) (by omega)
          · have h1 : 1 ≤ -z y s := by omega
            have h2 := Int.mul_le_mul h1 h1 (by decide) (by omega)
            have h3 : (-z y s) * (-z y s) = z y s * z y s := Int.neg_mul_neg _ _
            omega
        omega
    -- Therefore EVERY `m = 10` cell has `z y s1 = 0 ∧ z y s2 = 0`, so `z y (pickC s1 s2) ^ 2 = 36`, giving `8 * 36 = 288 ≤ 144`!
    let cw := pickC s1 s2
    have hcw : isSZ cw = false := pickC_not_SZ s1 s2 hs1_SZ hs2_SZ (fun e => hs2_ne e.symm)
    have h288 : 36 * n10c ≤ total 4 (fun y => z y cw * z y cw) := by
      dsimp only [n10c]; rw [← total_scale]
      apply total_mono 4; intro y
      by_cases h10 : mcell y = 10
      · rw [if_pos h10, Int.mul_one]
        have hy_ne : y ≠ y8 := by intro e; rw [e, hy8] at h10; omega
        have hz1 := hzero_other s1 hs1_SZ hz8_s1 y hy_ne
        have hz2 := hzero_other s2 hs2_SZ hz8_s2 y hy_ne
        have h36 := (((hcell_ok y).2 (by rw [h10]; decide)).2.2.2.2.2.1 h10).2.2.2
          s1 s2 hs1_SZ hs2_SZ (fun e => hs2_ne e.symm) hz1 hz2
        dsimp only [cw]; omega
      · rw [if_neg h10, Int.mul_zero]
        have : 0 ≤ z y cw ∨ z y cw ≤ 0 := by omega
        rcases this with h' | h'; exact Int.mul_nonneg h' h'; exact Int.mul_nonneg_of_nonpos_of_nonpos h' h'
    rw [hSZc_tot cw hcw] at h288; omega
  · -- ======================== CASE `k = 6`: 3-LINE CUBIC IDENTITY! ========================
    -- Every `s ∈ SZ` has `hits10 s ∈ {0, 4}`, and `∑_{s ∈ SZ} hits10 s = 4 * 4 = 16`, so EXACTLY 4 cosets in `SZ`
    -- have `hits10 s = 4`! Since at least 4 of the 6 cosets in `SZ` have `zeroCnt s = 0`, by pigeonhole (`4 + 4 > 6`)
    -- there exists `s* ∈ SZ` with `zeroCnt s* = 0` (`tot[s*] = 64`) AND `hits10 s* = 4`!
    have hex_s : ∃ s : W 4, isSZ s = true ∧ zeroCnt s = 0 ∧ hits10 s = 4 := by
      cases h : (worlds 4).all (fun s => !(isSZ s && decide (zeroCnt s = 0) && decide (hits10 s = 4)))
      · obtain ⟨s, _, hs⟩ := all_false_exists _ _ h
        have hsZ : isSZ s = true := by cases e : isSZ s <;> rw [e] at hs <;> simp at hs ⊢
        have hz0 : zeroCnt s = 0 := by by_cases e : zeroCnt s = 0 <;> simp [e] at hs ⊢
        have hh4 : hits10 s = 4 := by by_cases e : hits10 s = 4 <;> simp [e] at hs ⊢
        exact ⟨s, hsZ, hz0, hh4⟩
      · exfalso; rw [List.all_eq_true] at h
        -- Count: `#{isSZ ∧ hits10 = 4} = 4` and `#{isSZ ∧ zeroCnt = 0} ≥ 4`, disjoint inside 6-element `SZ` → `8 ≤ 6`!
        have hcnt_h4 : total 4 (fun s => if isSZ s && decide (hits10 s = 4) then (1 : Int) else 0) = 4 := by
          have h4eq : 4 * total 4 (fun s => if isSZ s && decide (hits10 s = 4) then (1 : Int) else 0) =
              total 4 (fun s => if isSZ s then hits10 s else 0) := by
            rw [← total_scale]; apply congrArg (total 4); funext s
            cases hs : isSZ s
            · simp
            · have hd4 := hhits10_div4 s hs; have ⟨h0, hle⟩ := hhits10_le s
              by_cases e : hits10 s = 4 <;> simp [e] <;> omega
          rw [hhits10_sum, hn10] at h4eq; omega
        have hle6 : total 4 (fun s => if isSZ s && decide (zeroCnt s = 0) then (1 : Int) else 0) +
                    total 4 (fun s => if isSZ s && decide (hits10 s = 4) then (1 : Int) else 0) ≤ 6 := by
          have h6 : total 4 (fun s => bind (isSZ s)) = 6 := by decide
          rw [← total_add, ← h6]; apply total_mono 4; intro s
          have ha := h s (all_worlds 4 s)
          cases hs : isSZ s
          · simp [Balanced242Plateau.ind]
          · by_cases hz : zeroCnt s = 0
            · by_cases hh : hits10 s = 4
              · rw [hs, decide_eq_true hz, decide_eq_true hh] at ha; simp at ha
              · simp [hz, hh, Balanced242Plateau.ind]
            · by_cases hh : hits10 s = 4 <;> simp [hz, hh, Balanced242Plateau.ind]
        omega
    obtain ⟨s, hsZ, hzs0, hhs4⟩ := hex_s
    -- On this `s`: ALL 16 `Vhat(L_u s ⊕ L_r r) = ±8`, `w y s` takes `±2` on the 4 `m=10` cells (`gA`),
    -- `±4` on EXACTLY 3 `m=12` cells (`t1, t2, t3`), and `0` on the remaining 9 cells (`6` `m=0` + `3` `m=12`)!
    have hVhat_pm8 (r : W 4) : lo f g (add 8 (L_u s) (L_r r)) / 2 = 8 ∨ lo f g (add 8 (L_u s) (L_r r)) / 2 = -8 := by
      have hnz : lo f g (add 8 (L_u s) (L_r r)) ≠ 0 := by
        intro h0
        have hp := point_le_total 4 (fun a => if lo f g (add 8 (L_u s) (L_r a)) = 0 then (1 : Int) else 0)
          (fun _ => by dsimp only; split <;> decide) r
        change (if lo f g (add 8 (L_u s) (L_r r)) = 0 then (1 : Int) else 0) ≤ zeroCnt s at hp
        rw [if_pos h0, hzs0] at hp; omega
      have hZ : Zset f g (add 8 (L_u s) (L_r r)) = true := by rw [hZ_isSZ s r, hsZ]
      have h64 := (hVhat_val _).2.1 hZ hnz
      exact sq_cases (lo f g (add 8 (L_u s) (L_r r)) / 2) 8 h64
    -- Every `y` has `w y s ∈ {-4, -2, 0, 2, 4}` (specifically: `m=0 → 0`, `m=10 → ±2`, `m=12 → 0 or ±4`)!
    have hw_sq (y : W 4) : w y s * w y s = z y s * z y s := by
      dsimp only [w]; have h1 : chr (L_u s) (L_e y) * chr (L_u s) (L_e y) = 1 := sign_sq _
      calc (chr (L_u s) (L_e y) * z y s) * (chr (L_u s) (L_e y) * z y s)
          = (chr (L_u s) (L_e y) * chr (L_u s) (L_e y)) * (z y s * z y s) := by ac_rfl
        _ = z y s * z y s := by rw [h1, Int.one_mul]
    have hno68 (y : W 4) : mcell y = 0 ∨ mcell y = 10 ∨ mcell y = 12 := by
      rcases hall_even y with h | h | h | h | h
      · exact Or.inl h
      · exfalso; have hp := point_le_total 4 (fun u => if mcell u = 6 then (1 : Int) else 0) (fun _ => by dsimp only; split <;> decide) y
        change (if mcell y = 6 then (1 : Int) else 0) ≤ n6c at hp; rw [if_pos h, hn6] at hp; omega
      · exfalso; have hp := point_le_total 4 (fun u => if mcell u = 8 then (1 : Int) else 0) (fun _ => by dsimp only; split <;> decide) y
        change (if mcell y = 8 then (1 : Int) else 0) ≤ n8c at hp; rw [if_pos h, hn8] at hp; omega
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    -- Every `m = 10` cell has `w y s * w y s = 4` (since `hits10 s = 4 = n10c`!)!
    have hm10_hit (y : W 4) (h10 : mcell y = 10) : w y s = 2 ∨ w y s = -2 := by
      have h4 : z y s * z y s = 4 := by
        have hle (u : W 4) : 0 ≤ (if mcell u = 10 then (1 : Int) else 0) -
            (if mcell u = 10 && decide (z u s * z u s = 4) then (1 : Int) else 0) := by
          by_cases e : mcell u = 10 <;> simp [e]; split <;> omega
        have hsum : total 4 (fun u => (if mcell u = 10 then (1 : Int) else 0) -
            (if mcell u = 10 && decide (z u s * z u s = 4) then (1 : Int) else 0)) = 0 := by
          rw [total_sub]; change n10c - hits10 s = 0; omega
        have hp := point_le_total 4 _ hle y; rw [hsum, if_pos h10] at hp
        by_cases h4' : z y s * z y s = 4
        · exact h4'
        · exfalso; simp [h10, h4'] at hp
      rw [← hw_sq y] at h4; exact sq_cases (w y s) 2 h4
    -- Exactly THREE `m = 12` cells have `w y s = ±4` (since `4*4 + 16*nT = 64 → nT = 3`)!
    let isT (y : W 4) : Bool := decide (w y s * w y s = 16)
    have hT_cnt : total 4 (fun y => bind (isT y)) = 3 := by
      have htot64 : total 4 (fun y => w y s * w y s) = 64 := by
        have h := hSZ_tot_eq s hsZ; rw [hzs0] at h
        simpa only [hw_sq] using h
      have hpt (y : W 4) : w y s * w y s = 4 * (if mcell y = 10 then (1 : Int) else 0) + 16 * bind (isT y) := by
        rcases hno68 y with h | h | h
        · have hz := (((hcell_ok y).2 (by rw [h]; decide)).2.2.1 h).2 s hsZ
          rw [hw_sq y, hz]; dsimp only [isT]; rw [hw_sq y, hz, h]; decide
        · rcases hm10_hit y h with e | e <;> (dsimp only [isT]; rw [e, h]; decide)
        · rcases ((((hcell_ok y).2 (by rw [h]; decide)).2.2.2.2.2.2.1 h).2.1 s hsZ) with hz | hz <;>
            (dsimp only [isT]; rw [hw_sq y, hz, h]; decide)
      rw [funext hpt, total_add, total_scale, total_scale] at htot64
      change 4 * n10c + 16 * total 4 (fun y => bind (isT y)) = 64 at htot64; omega
    -- Extract the 3 points `t1, t2, t3` of `isT`!
    have hex_3 (P : W 4 → Bool) (h3 : total 4 (fun y => bind (P y)) = 3) :
        ∃ t1 t2 t3 : W 4, t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 ∧
          ∀ y, bind (P y) = hits t1 y + hits t2 y + hits t3 y := by
      have get1 (Q : W 4 → Bool) (hpos : 1 ≤ total 4 (fun y => bind (Q y))) : ∃ a : W 4, Q a = true := by
        cases h : (worlds 4).all (fun y => !Q y)
        · obtain ⟨a, _, ha⟩ := all_false_exists _ _ h
          exact ⟨a, by cases e : Q a <;> rw [e] at ha <;> simp at ha ⊢⟩
        · exfalso; rw [List.all_eq_true] at h
          have h0 : total 4 (fun y => bind (Q y)) = 0 := by
            rw [← total_zero 4]; apply congrArg (total 4); funext y
            have hy := h y (all_worlds 4 y); cases e : Q y <;> rw [e] at hy <;> simp [Balanced242Plateau.ind] at hy ⊢
          omega
      obtain ⟨t1, ht1⟩ := get1 P (by omega)
      let P1 (y : W 4) : Bool := P y && !decide (y = t1)
      have hP1 : total 4 (fun y => bind (P1 y)) = 2 := by
        have hpt (y : W 4) : bind (P1 y) = bind (P y) - hits t1 y := by
          dsimp only [P1]; unfold hits; by_cases e : t1 = y
          · subst e; simp [ht1, Balanced242Plateau.ind]
          · have hne : y ≠ t1 := fun h' => e h'.symm; simp [e, hne]
        rw [funext hpt, total_sub, diagonal 4 t1]; omega
      obtain ⟨t2, ht2'⟩ := get1 P1 (by omega)
      have ht2 : P t2 = true := by dsimp only [P1] at ht2'; cases e : P t2 <;> rw [e] at ht2' <;> simp at ht2' ⊢
      have h12 : t1 ≠ t2 := by dsimp only [P1] at ht2'; intro e; subst e; simp at ht2'
      let P2 (y : W 4) : Bool := P1 y && !decide (y = t2)
      have hP2 : total 4 (fun y => bind (P2 y)) = 1 := by
        have hpt (y : W 4) : bind (P2 y) = bind (P1 y) - hits t2 y := by
          dsimp only [P2]; unfold hits; by_cases e : t2 = y
          · subst e; simp [ht2', Balanced242Plateau.ind]
          · have hne : y ≠ t2 := fun h' => e h'.symm; simp [e, hne]
        rw [funext hpt, total_sub, diagonal 4 t2]; omega
      obtain ⟨t3, ht3'⟩ := get1 P2 (by omega)
      have ht3 : P t3 = true := by
        dsimp only [P2, P1] at ht3'; cases e : P t3 <;> rw [e] at ht3' <;> simp at ht3' ⊢
      have h13 : t1 ≠ t3 := by dsimp only [P2, P1] at ht3'; intro e; subst e; simp at ht3'
      have h23 : t2 ≠ t3 := by dsimp only [P2] at ht3'; intro e; subst e; simp at ht3'
      refine ⟨t1, t2, t3, h12, h13, h23, fun y => ?_⟩
      have hge (u : W 4) : 0 ≤ bind (P u) - (hits t1 u + hits t2 u + hits t3 u) := by
        unfold hits
        by_cases e1 : t1 = u
        · subst e1; simp [ht1, h12.symm, h13.symm, Balanced242Plateau.ind]
        · by_cases e2 : t2 = u
          · subst e2; simp [ht2, e1, h23.symm, Balanced242Plateau.ind]
          · by_cases e3 : t3 = u
            · subst e3; simp [ht3, e1, e2, Balanced242Plateau.ind]
            · simp [e1, e2, e3]; exact Balanced242Plateau.ind_nonneg _
      have hs : total 4 (fun u => bind (P u) - (hits t1 u + hits t2 u + hits t3 u)) = 0 := by
        rw [total_sub, total_add, total_add, diagonal 4 t1, diagonal 4 t2, diagonal 4 t3, h3]; omega
      have hp := point_le_total 4 _ hge y; rw [hs] at hp; have h0 := hge y; omega
    obtain ⟨t1, t2, t3, h12, h13, h23, hT_mem⟩ := hex_3 isT hT_cnt
    -- Split `w y s = 2 * gA y + 4 * gT y` and invoke our 3-line cubic lemma `no_4twos_3fours_walsh8`!
    let gA (y : W 4) : Int := if mcell y = 10 then w y s / 2 else 0
    let e1 : Int := w t1 s / 4
    let e2 : Int := w t2 s / 4
    let e3 : Int := w t3 s / 4
    have he_pm (t : W 4) (hTt : isT t = true) : w t s / 4 = 1 ∨ w t s / 4 = -1 := by
      have h16 : w t s * w t s = 16 := of_decide_eq_true hTt
      rcases sq_cases (w t s) 4 h16 with e | e <;> rw [e] <;> decide
    have hTt1 : isT t1 = true := by
      have h := hT_mem t1; unfold hits at h; simp [h12.symm, h13.symm] at h
      cases e : isT t1 <;> rw [e] at h <;> simp [Balanced242Plateau.ind] at h ⊢
    have hTt2 : isT t2 = true := by
      have h := hT_mem t2; unfold hits at h; simp [h12, h23.symm] at h
      cases e : isT t2 <;> rw [e] at h <;> simp [Balanced242Plateau.ind] at h ⊢
    have hTt3 : isT t3 = true := by
      have h := hT_mem t3; unfold hits at h; simp [h13, h23] at h
      cases e : isT t3 <;> rw [e] at h <;> simp [Balanced242Plateau.ind] at h ⊢
    apply no_4twos_3fours_walsh8 gA t1 t2 t3 e1 e2 e3 (he_pm t1 hTt1) (he_pm t2 hTt2) (he_pm t3 hTt3)
    · intro y; dsimp only [gA]
      by_cases h10 : mcell y = 10
      · rw [if_pos h10]; rcases hm10_hit y h10 with e | e <;> rw [e] <;> decide
      · rw [if_neg h10]; right; left; rfl
    · have hpt (y : W 4) : gA y * gA y = if mcell y = 10 then (1 : Int) else 0 := by
        dsimp only [gA]; by_cases h10 : mcell y = 10
        · rw [if_pos h10, if_pos h10]; rcases hm10_hit y h10 with e | e <;> rw [e] <;> decide
        · rw [if_neg h10, if_neg h10]; rfl
      rw [funext hpt]; exact hn10
    · intro r; dsimp only
      have htr := htr_w s r
      have hsplit (y : W 4) : w y s = 2 * gA y + 4 * (e1 * hits t1 y + e2 * hits t2 y + e3 * hits t3 y) := by
        have ht := hT_mem y
        rcases hno68 y with h | h | h
        · have hz := (((hcell_ok y).2 (by rw [h]; decide)).2.2.1 h).2 s hsZ
          have hw0 : w y s = 0 := by
            have h0 : w y s * w y s = 0 := by rw [hw_sq y, hz]
            rcases sq_cases (w y s) 0 h0 with e | e <;> exact e
          have hT0 : isT y = false := by dsimp only [isT]; rw [hw0]; decide
          rw [hT0] at ht; simp [Balanced242Plateau.ind] at ht
          have hh0 : hits t1 y = 0 ∧ hits t2 y = 0 ∧ hits t3 y = 0 := by
            have h1 : 0 ≤ hits t1 y := by unfold hits; split <;> decide
            have h2 : 0 ≤ hits t2 y := by unfold hits; split <;> decide
            have h3 : 0 ≤ hits t3 y := by unfold hits; split <;> decide
            omega
          dsimp only [gA]; rw [hw0, h, hh0.1, hh0.2.1, hh0.2.2]; simp
        · rcases hm10_hit y h with e | e
          · have hT0 : isT y = false := by dsimp only [isT]; rw [e]; decide
            rw [hT0] at ht; simp [Balanced242Plateau.ind] at ht
            have hh0 : hits t1 y = 0 ∧ hits t2 y = 0 ∧ hits t3 y = 0 := by
              have h1 : 0 ≤ hits t1 y := by unfold hits; split <;> decide
              have h2 : 0 ≤ hits t2 y := by unfold hits; split <;> decide
              have h3 : 0 ≤ hits t3 y := by unfold hits; split <;> decide
              omega
            dsimp only [gA]; rw [h, if_pos rfl, e, hh0.1, hh0.2.1, hh0.2.2]; simp
          · have hT0 : isT y = false := by dsimp only [isT]; rw [e]; decide
            rw [hT0] at ht; simp [Balanced242Plateau.ind] at ht
            have hh0 : hits t1 y = 0 ∧ hits t2 y = 0 ∧ hits t3 y = 0 := by
              have h1 : 0 ≤ hits t1 y := by unfold hits; split <;> decide
              have h2 : 0 ≤ hits t2 y := by unfold hits; split <;> decide
              have h3 : 0 ≤ hits t3 y := by unfold hits; split <;> decide
              omega
            dsimp only [gA]; rw [h, if_pos rfl, e, hh0.1, hh0.2.1, hh0.2.2]; simp
        · dsimp only [gA]; rw [h, if_neg (by decide)]
          rcases ((((hcell_ok y).2 (by rw [h]; decide)).2.2.2.2.2.2.1 h).2.1 s hsZ) with hz | hz
          · have hw0 : w y s = 0 := by
              have h0 : w y s * w y s = 0 := by rw [hw_sq y, hz]
              rcases sq_cases (w y s) 0 h0 with e | e <;> exact e
            have hT0 : isT y = false := by dsimp only [isT]; rw [hw0]; decide
            rw [hT0] at ht; simp [Balanced242Plateau.ind] at ht
            have hh0 : hits t1 y = 0 ∧ hits t2 y = 0 ∧ hits t3 y = 0 := by
              have h1 : 0 ≤ hits t1 y := by unfold hits; split <;> decide
              have h2 : 0 ≤ hits t2 y := by unfold hits; split <;> decide
              have h3 : 0 ≤ hits t3 y := by unfold hits; split <;> decide
              omega
            rw [hw0, hh0.1, hh0.2.1, hh0.2.2]; simp
          · have hT1 : isT y = true := by dsimp only [isT]; rw [hw_sq y, hz]; decide
            rw [hT1] at ht; simp [Balanced242Plateau.ind] at ht
            have hw4 : w y s = 4 ∨ w y s = -4 := sq_cases (w y s) 4 (by rw [hw_sq y, hz]; rfl)
            unfold hits at ht ⊢
            by_cases k1 : t1 = y
            · subst k1; simp only [if_true, h12.symm, h13.symm, if_false, Int.mul_one, Int.mul_zero, Int.add_zero]
              dsimp only [e1]; rcases hw4 with e | e <;> rw [e] <;> decide
            · by_cases k2 : t2 = y
              · subst k2; simp only [k1, if_true, h23.symm, if_false, Int.mul_one, Int.mul_zero, Int.zero_add, Int.add_zero]
                dsimp only [e2]; rcases hw4 with e | e <;> rw [e] <;> decide
              · by_cases k3 : t3 = y
                · subst k3; simp only [k1, k2, if_true, if_false, Int.mul_one, Int.mul_zero, Int.zero_add]
                  dsimp only [e3]; rcases hw4 with e | e <;> rw [e] <;> decide
                · simp [k1, k2, k3] at ht
      have htr_split : transform (fun y => w y s) r =
          2 * transform gA r + 4 * (e1 * chr t1 r + e2 * chr t2 r + e3 * chr t3 r) := by
        unfold transform
        have hpt (y : W 4) : w y s * chr r y =
            2 * (gA y * chr r y) + 4 * (e1 * chr t1 r * hits t1 y + e2 * chr t2 r * hits t2 y + e3 * chr t3 r * hits t3 y) := by
          rw [hsplit y, Int.add_mul, Int.mul_assoc, Int.mul_assoc]
          congr 1; congr 1
          have hc (t : W 4) (c : Int) : c * hits t y * chr r y = c * chr t r * hits t y := by
            unfold hits; by_cases e : t = y
            · subst e
              have hsym : chr r t = chr t r := by unfold chr; rw [dot_comm]
              simp [hsym]
            · simp [e]
          rw [Int.add_mul, Int.add_mul, hc t1 e1, hc t2 e2, hc t3 e3]
        rw [funext hpt, total_add, total_scale, total_scale, total_add, total_add,
            total_scale, total_scale, total_scale, diagonal 4 t1, diagonal 4 t2, diagonal 4 t3]
        omega
      rw [htr_split] at htr
      rcases hVhat_pm8 r with h | h
      · rw [h] at htr; left; omega
      · rw [h] at htr; right; omega
  · -- ======================== CASE `k = 0`: `0 = 96` 4-PAIR WALSH CONTRADICTION! ========================
    -- `n6c = 2`, `n10c = 10`, `n0c = 4`, `n8c = n12c = 0`!
    have hno812 (y : W 4) : mcell y = 0 ∨ mcell y = 6 ∨ mcell y = 10 := by
      rcases hall_even y with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exfalso; have hp := point_le_total 4 (fun u => if mcell u = 8 then (1 : Int) else 0) (fun _ => by dsimp only; split <;> decide) y
        change (if mcell y = 8 then (1 : Int) else 0) ≤ n8c at hp; rw [if_pos h, hn8] at hp; omega
      · exact Or.inr (Or.inr h)
      · exfalso; have hp := point_le_total 4 (fun u => if mcell u = 12 then (1 : Int) else 0) (fun _ => by dsimp only; split <;> decide) y
        change (if mcell y = 12 then (1 : Int) else 0) ≤ n12c at hp; rw [if_pos h, hn12] at hp; omega
    -- Extract the TWO `m = 6` cells `y1 ≠ y2`, and put `d := add 4 y1 y2 ≠ zero 4`!
    have hex_y12 : ∃ y1 y2 : W 4, y1 ≠ y2 ∧
        ∀ y, (if mcell y = 6 then (1 : Int) else 0) = hits y1 y + hits y2 y := by
      have hex1 : ∃ y1 : W 4, mcell y1 = 6 := by
        cases h : (worlds 4).all (fun y => !decide (mcell y = 6))
        · obtain ⟨y1, _, hy1⟩ := all_false_exists _ _ h
          exact ⟨y1, by by_cases e : mcell y1 = 6 <;> simp [e] at hy1 ⊢⟩
        · exfalso; rw [List.all_eq_true] at h
          have h0 : n6c = 0 := by
            dsimp only [n6c]; refine Eq.trans ?_ (total_zero 4)
            apply congrArg (total 4); funext y
            have hy := h y (all_worlds 4 y)
            have hne : mcell y ≠ 6 := fun e => by rw [e, decide_eq_true rfl] at hy; exact Bool.noConfusion hy
            rw [if_neg hne]
          omega
      obtain ⟨y1, hy1⟩ := hex1
      have hex2 : ∃ y2 : W 4, y2 ≠ y1 ∧ mcell y2 = 6 := by
        cases h : (worlds 4).all (fun y => decide (y = y1) || !decide (mcell y = 6))
        · obtain ⟨y2, _, hy2⟩ := all_false_exists _ _ h
          have hne : y2 ≠ y1 := by intro e; subst e; simp at hy2
          have hm6 : mcell y2 = 6 := by by_cases e : mcell y2 = 6 <;> simp [e, hne] at hy2 ⊢
          exact ⟨y2, hne, hm6⟩
        · exfalso; rw [List.all_eq_true] at h
          have hle1 : n6c ≤ 1 := by
            have hm := total_mono 4 (fun y => if mcell y = 6 then (1 : Int) else 0) (hits y1) (fun y => by
              have hy := h y (all_worlds 4 y); unfold hits
              by_cases e : y1 = y
              · subst e; simp; split <;> omega
              · have hne : y ≠ y1 := fun h' => e h'.symm
                rw [decide_eq_false hne, Bool.false_or] at hy
                have hne6 : mcell y ≠ 6 := fun h' => by rw [h', decide_eq_true rfl] at hy; exact Bool.noConfusion hy
                dsimp only; rw [if_neg hne6, if_neg e]; decide)
            rw [diagonal 4 y1] at hm; exact hm
          omega
      obtain ⟨y2, hy2_ne, hy2⟩ := hex2
      refine ⟨y1, y2, hy2_ne.symm, fun y => ?_⟩
      have hge (u : W 4) : 0 ≤ (if mcell u = 6 then (1 : Int) else 0) - (hits y1 u + hits y2 u) := by
        unfold hits
        by_cases e1 : y1 = u
        · subst e1; simp [hy1, hy2_ne]
        · by_cases e2 : y2 = u
          · subst e2; simp [hy2, e1]
          · simp [e1, e2]; split <;> decide
      have hs : total 4 (fun u => (if mcell u = 6 then (1 : Int) else 0) - (hits y1 u + hits y2 u)) = 0 := by
        rw [total_sub, total_add, diagonal 4 y1, diagonal 4 y2]; change n6c - (1 + 1) = 0; omega
      have hp := point_le_total 4 _ hge y; rw [hs] at hp; have h0 := hge y; omega
    obtain ⟨y1, y2, hy12, hm6_mem⟩ := hex_y12
    let d : W 4 := add 4 y1 y2
    have hd_ne : d ≠ zero 4 := by
      intro hz; apply hy12; have h := congrArg (add 4 y1) hz
      rw [← Balanced242Plateau.add_assoc', add_self, add_zero_left, add_zero_right] at h; exact h.symm
    -- Key analysis for ANY zero-free coset `s ∈ SZ` (`zeroCnt s = 0`, so `tot[s] = 64`):
    --   1. `hits10 s = 8` (missing EXACTLY 2 cells of `X_10`),
    --   2. `w y s` on `X_10` satisfies `w (y ⊕ d) s = eps_s * w y s` (`eps_s = -sign1 * sign2 ∈ {±1}`),
    --      so `supp_s = {y : mcell y = 10 ∧ w y s ≠ 0}` is closed under `y ↦ add 4 y d`!
    --   3. For ANY 4 points `x1..x4` forming the 4 `d`-pairs of `supp_s`, `x1 ⊕ x2 ⊕ x3 ⊕ x4 ∈ {0, d}`!
    have hzf_props (s : W 4) (hsZ : isSZ s = true) (hz0 : zeroCnt s = 0) :
        hits10 s = 8 ∧
        (∃ eps : Int, (eps = 1 ∨ eps = -1) ∧
          (∀ y : W 4, (if mcell y = 10 then w y s else 0) = eps * (if mcell (add 4 y d) = 10 then w (add 4 y d) s else 0)) ∧
          (∀ r : W 4, chr d r = eps →
            transform (fun y => if mcell y = 10 then w y s else 0) r = 8 ∨
            transform (fun y => if mcell y = 10 then w y s else 0) r = -8)) := by
      have hw_sq (y : W 4) : w y s * w y s = z y s * z y s := by
        dsimp only [w]; have h1 : chr (L_u s) (L_e y) * chr (L_u s) (L_e y) = 1 := sign_sq _
        calc (chr (L_u s) (L_e y) * z y s) * (chr (L_u s) (L_e y) * z y s)
            = (chr (L_u s) (L_e y) * chr (L_u s) (L_e y)) * (z y s * z y s) := by ac_rfl
          _ = z y s * z y s := by rw [h1, Int.one_mul]
      have htot64 : total 4 (fun y => w y s * w y s) = 64 := by
        have h := hSZ_tot_eq s hsZ; rw [hz0] at h; simpa only [hw_sq] using h
      have hhits8 : hits10 s = 8 := by
        have hpt (y : W 4) : w y s * w y s = 16 * (if mcell y = 6 then (1 : Int) else 0) +
            4 * (if mcell y = 10 && decide (z y s * z y s = 4) then (1 : Int) else 0) := by
          rcases hno812 y with h | h | h
          · have hz := (((hcell_ok y).2 (by rw [h]; decide)).2.2.1 h).2 s hsZ; rw [hw_sq y, hz, h]; decide
          · have hz := (((hcell_ok y).2 (by rw [h]; decide)).2.2.2.1 h).2 s hsZ; rw [hw_sq y, hz, h]; decide
          · rcases ((((hcell_ok y).2 (by rw [h]; decide)).2.2.2.2.2.1 h).2.1 s hsZ) with hz | hz <;>
              rw [hw_sq y, hz, h] <;> decide
        rw [funext hpt, total_add, total_scale, total_scale] at htot64
        change 16 * n6c + 4 * hits10 s = 64 at htot64; omega
      -- Split `w y s = h6 y + h10 y` where `h6` is `±4` on `{y1, y2}` and `h10` is `if mcell y = 10 then w y s else 0`!
      let h10 (y : W 4) : Int := if mcell y = 10 then w y s else 0
      have hm6_y1 : mcell y1 = 6 := by
        have h := hm6_mem y1; unfold hits at h; simp [hy12.symm] at h; by_cases e : mcell y1 = 6 <;> simp [e] at h ⊢
      have hm6_y2 : mcell y2 = 6 := by
        have h := hm6_mem y2; unfold hits at h; simp [hy12] at h; by_cases e : mcell y2 = 6 <;> simp [e] at h ⊢
      have hw_y1 : w y1 s = 4 ∨ w y1 s = -4 := by
        have hz := (((hcell_ok y1).2 (by rw [hm6_y1]; decide)).2.2.2.1 hm6_y1).2 s hsZ
        rw [← hw_sq y1] at hz; exact sq_cases _ 4 hz
      have hw_y2 : w y2 s = 4 ∨ w y2 s = -4 := by
        have hz := (((hcell_ok y2).2 (by rw [hm6_y2]; decide)).2.2.2.1 hm6_y2).2 s hsZ
        rw [← hw_sq y2] at hz; exact sq_cases _ 4 hz
      let s_1 : Int := w y1 s / 4
      let s_2 : Int := w y2 s / 4
      have hs1_pm : s_1 = 1 ∨ s_1 = -1 := by dsimp only [s_1]; rcases hw_y1 with e | e <;> rw [e] <;> decide
      have hs2_pm : s_2 = 1 ∨ s_2 = -1 := by dsimp only [s_2]; rcases hw_y2 with e | e <;> rw [e] <;> decide
      let eps : Int := -(s_1 * s_2)
      have heps_pm : eps = 1 ∨ eps = -1 := by dsimp only [eps]; rcases hs1_pm with a | a <;> rcases hs2_pm with b | b <;> rw [a, b] <;> decide
      -- On `r : W 4`: `transform (w · s) r = 4 * (s_1 * chr y1 r + s_2 * chr y2 r) + transform h10 r = ±8`!
      have hVhat_pm8 (r : W 4) : lo f g (add 8 (L_u s) (L_r r)) / 2 = 8 ∨ lo f g (add 8 (L_u s) (L_r r)) / 2 = -8 := by
        have hnz : lo f g (add 8 (L_u s) (L_r r)) ≠ 0 := by
          intro h0
          have hp := point_le_total 4 (fun a => if lo f g (add 8 (L_u s) (L_r a)) = 0 then (1 : Int) else 0)
            (fun _ => by dsimp only; split <;> decide) r
          change (if lo f g (add 8 (L_u s) (L_r r)) = 0 then (1 : Int) else 0) ≤ zeroCnt s at hp
          rw [if_pos h0, hz0] at hp; omega
        have hZ : Zset f g (add 8 (L_u s) (L_r r)) = true := by rw [hZ_isSZ s r, hsZ]
        exact sq_cases _ 8 ((hVhat_val _).2.1 hZ hnz)
      have htr_sum (r : W 4) :
          4 * (s_1 * chr y1 r + s_2 * chr y2 r) + transform h10 r = 8 ∨
          4 * (s_1 * chr y1 r + s_2 * chr y2 r) + transform h10 r = -8 := by
        have h := htr_w s r
        have hsplit (y : W 4) : w y s = 4 * (s_1 * hits y1 y + s_2 * hits y2 y) + h10 y := by
          have hm := hm6_mem y
          rcases hno812 y with hm0 | hm6 | hm10
          · have hz := (((hcell_ok y).2 (by rw [hm0]; decide)).2.2.1 hm0).2 s hsZ
            have hw0 : w y s = 0 := by rcases sq_cases (w y s) 0 (by rw [hw_sq y, hz]; rfl) with e | e <;> exact e
            rw [if_neg (by omega)] at hm
            have hh0 : hits y1 y = 0 ∧ hits y2 y = 0 := by
              have h1 : 0 ≤ hits y1 y := by unfold hits; split <;> decide
              have h2 : 0 ≤ hits y2 y := by unfold hits; split <;> decide
              omega
            dsimp only [h10]; rw [hw0, hm0, hh0.1, hh0.2]; simp
          · rw [if_pos hm6] at hm; dsimp only [h10]; rw [hm6, if_neg (by decide)]
            unfold hits at hm ⊢
            by_cases e1 : y1 = y
            · subst e1; simp only [if_true, hy12.symm, if_false, Int.mul_one, Int.mul_zero, Int.add_zero]
              dsimp only [s_1]; rcases hw_y1 with e | e <;> rw [e] <;> decide
            · by_cases e2 : y2 = y
              · subst e2; simp only [e1, if_true, if_false, Int.mul_one, Int.mul_zero, Int.zero_add, Int.add_zero]
                dsimp only [s_2]; rcases hw_y2 with e | e <;> rw [e] <;> decide
              · simp [e1, e2] at hm
          · rw [if_neg (by omega)] at hm
            have hh0 : hits y1 y = 0 ∧ hits y2 y = 0 := by
              have h1 : 0 ≤ hits y1 y := by unfold hits; split <;> decide
              have h2 : 0 ≤ hits y2 y := by unfold hits; split <;> decide
              omega
            dsimp only [h10]; rw [hm10, if_pos rfl, hh0.1, hh0.2]; omega
        have heq : transform (fun y => w y s) r = 4 * (s_1 * chr y1 r + s_2 * chr y2 r) + transform h10 r := by
          unfold transform
          have hpt (y : W 4) : w y s * chr r y =
              4 * (s_1 * chr y1 r * hits y1 y + s_2 * chr y2 r * hits y2 y) + h10 y * chr r y := by
            rw [hsplit y, Int.add_mul, Int.mul_assoc]; congr 1; congr 1
            have hc (t : W 4) (c : Int) : c * hits t y * chr r y = c * chr t r * hits t y := by
              unfold hits; by_cases e : t = y
              · subst e
                have hsym : chr r t = chr t r := by unfold chr; rw [dot_comm]
                simp [hsym]
              · simp [e]
            rw [Int.add_mul, hc y1 s_1, hc y2 s_2]
          rw [funext hpt, total_add, total_scale, total_add, total_scale, total_scale, diagonal 4 y1, diagonal 4 y2]
          omega
        rw [heq] at h; rcases hVhat_pm8 r with e | e
        · rw [e] at h; exact Or.inl h
        · rw [e] at h; exact Or.inr h
      -- When `chr d r = eps`: `s_1 * chr y1 r + s_2 * chr y2 r = 0`, so `transform h10 r = ±8`!
      have htr_on_eps (r : W 4) (hr : chr d r = eps) : transform h10 r = 8 ∨ transform h10 r = -8 := by
        have hch : chr d r = chr y1 r * chr y2 r := by
          dsimp only [d]; have hsym (u : W 4) : chr u r = chr r u := by unfold chr; rw [dot_comm]
          rw [hsym, hsym y1, hsym y2, Balanced242Plateau.chr_add]
        have h0 : s_1 * chr y1 r + s_2 * chr y2 r = 0 := by
          rw [hch] at hr; dsimp only [eps] at hr
          have c1 : chr y1 r = 1 ∨ chr y1 r = -1 := sign_vals _
          have c2 : chr y2 r = 1 ∨ chr y2 r = -1 := sign_vals _
          rcases hs1_pm with a | a <;> rcases hs2_pm with b | b <;>
          rcases c1 with c | c <;> rcases c2 with e | e <;> rw [a, b, c, e] at hr ⊢ <;> omega
        have hs := htr_sum r; rw [h0] at hs; simpa using hs
      -- Parseval on `h10`: `∑_r (transform h10 r)^2 = 16 * (8 * 4) = 512`, and the 8 `chr d r = eps` terms
      -- ALREADY sum to `8 * 64 = 512`! Hence `transform h10 r = 0` for ALL `r` with `chr d r = -eps`!
      have htr_off_eps (r : W 4) (hr : chr d r ≠ eps) : transform h10 r = 0 := by
        have hpar := Balanced242Section0320.parseval h10
        have hm4 : many 4 = 16 := by decide
        rw [hm4] at hpar
        have hsum_h10 : total 4 (fun y => h10 y * h10 y) = 32 := by
          have hpt (y : W 4) : h10 y * h10 y = 4 * (if mcell y = 10 && decide (z y s * z y s = 4) then (1 : Int) else 0) := by
            dsimp only [h10]; by_cases h10y : mcell y = 10
            · rw [if_pos h10y, hw_sq y]
              rcases ((((hcell_ok y).2 (by rw [h10y]; decide)).2.2.2.2.2.1 h10y).2.1 s hsZ) with hz | hz <;>
                rw [hz, h10y] <;> decide
            · rw [if_neg h10y]; simp [h10y]
          rw [funext hpt, total_scale]; change 4 * hits10 s = 32; omega
        rw [hsum_h10] at hpar
        have hcnt_eps : total 4 (fun a => if chr d a = eps then (1 : Int) else 0) = 8 := by
          have hpt (a : W 4) : 2 * (if chr d a = eps then (1 : Int) else 0) = 1 + eps * chr d a := by
            have hc : chr d a = 1 ∨ chr d a = -1 := sign_vals _
            rcases heps_pm with e | e <;> rcases hc with c | c <;> rw [e, c] <;> decide
          have hs := congrArg (total 4) (funext hpt)
          rw [total_scale, total_add, total_const, total_scale, hm4] at hs
          have hi : total 4 (chr d) = 0 := by
            have h := identity_spectrum 4 d; change total 4 (chr d) = _ at h; rw [h]; simp [hd_ne]
          rw [hi] at hs; omega
        have hge (a : W 4) : 0 ≤ transform h10 a * transform h10 a - 64 * (if chr d a = eps then (1 : Int) else 0) := by
          by_cases e : chr d a = eps
          · rw [if_pos e]; rcases htr_on_eps a e with h | h <;> rw [h] <;> decide
          · rw [if_neg e, Int.mul_zero, Int.sub_zero]
            have : 0 ≤ transform h10 a ∨ transform h10 a ≤ 0 := by omega
            rcases this with h' | h'; exact Int.mul_nonneg h' h'; exact Int.mul_nonneg_of_nonpos_of_nonpos h' h'
        have hs0 : total 4 (fun a => transform h10 a * transform h10 a - 64 * (if chr d a = eps then (1 : Int) else 0)) = 0 := by
          rw [total_sub, total_scale, hpar, hcnt_eps]; decide
        have hp := point_le_total 4 _ hge r; rw [hs0, if_neg hr, Int.mul_zero, Int.sub_zero] at hp
        have h0 := hge r; rw [if_neg hr, Int.mul_zero, Int.sub_zero] at h0
        rcases sq_cases (transform h10 r) 0 (by omega) with e | e <;> exact e
      -- By Walsh inversion on `h10`: since `transform h10 r = 0` whenever `chr d r ≠ eps`,
      -- `h10 (y ⊕ d) = eps * h10 y` for EVERY `y : W 4`!
      have hshift_h10 (y : W 4) : h10 y = eps * h10 (add 4 y d) := by
        have hinv1 := transform_involution h10 y
        have hinv2 := transform_involution h10 (add 4 y d)
        have hm4 : many 4 = 16 := by decide
        rw [hm4] at hinv1 hinv2
        have heq : transform (transform h10) y = eps * transform (transform h10) (add 4 y d) := by
          change total 4 (fun r => transform h10 r * chr y r) =
                 eps * total 4 (fun r => transform h10 r * chr (add 4 y d) r)
          rw [← total_scale]; apply congrArg (total 4); funext r
          by_cases he : chr d r = eps
          · have hch : chr (add 4 y d) r = chr y r * eps := by
              have hsym (u : W 4) : chr u r = chr r u := by unfold chr; rw [dot_comm]
              rw [hsym, hsym y, Balanced242Plateau.chr_add, ← hsym d, he]
            rw [hch]
            rcases heps_pm with e | e <;> rw [e] <;> simp [Int.mul_assoc] <;> omega
          · rw [htr_off_eps r he]; simp
        rw [hinv1, hinv2] at heq; rcases heps_pm with e | e <;> rw [e] at heq ⊢ <;> omega
      exact ⟨hhits8, eps, heps_pm, hshift_h10, htr_on_eps⟩
    -- NOW: `X_10 = {y : mcell y = 10}` is CLOSED under `y ↦ add 4 y d`!
    -- Proof: pick ANY `y` with `mcell y = 10`. Since `y` has only 2 zeros in `SZ` (and ≥ 4 cosets in `SZ` are zero-free!),
    -- there is a zero-free `s ∈ SZ` with `w y s ≠ 0`; then `hshift_h10` gives `h10 (y ⊕ d) = eps * w y s ≠ 0`, so `mcell (y ⊕ d) = 10`!
    have hX10_closed (y : W 4) (h10 : mcell y = 10) : mcell (add 4 y d) = 10 := by
      -- Find a zero-free `s ∈ SZ` with `z y s * z y s = 4`!
      have hex_s : ∃ s : W 4, isSZ s = true ∧ zeroCnt s = 0 ∧ z y s * z y s = 4 := by
        cases h : (worlds 4).all (fun s => !(isSZ s && decide (zeroCnt s = 0) && decide (z y s * z y s = 4)))
        · obtain ⟨s, _, hs⟩ := all_false_exists _ _ h
          have hsZ : isSZ s = true := by cases e : isSZ s <;> rw [e] at hs <;> simp at hs ⊢
          have hz0 : zeroCnt s = 0 := by by_cases e : zeroCnt s = 0 <;> simp [e] at hs ⊢
          have h4 : z y s * z y s = 4 := by by_cases e : z y s * z y s = 4 <;> simp [e] at hs ⊢
          exact ⟨s, hsZ, hz0, h4⟩
        · exfalso; rw [List.all_eq_true] at h
          -- `4` cosets in `SZ` have `z y s^2 = 4`, and `≥ 4` cosets in `SZ` have `zeroCnt s = 0`, disjoint inside 6 → `8 ≤ 6`!
          have h4 := (((hcell_ok y).2 (by rw [h10]; decide)).2.2.2.2.2.1 h10).2.2.1
          have hle6 : total 4 (fun s => if isSZ s && decide (zeroCnt s = 0) then (1 : Int) else 0) +
                      total 4 (fun s => if isSZ s && decide (z y s * z y s = 4) then (1 : Int) else 0) ≤ 6 := by
            have h6 : total 4 (fun s => bind (isSZ s)) = 6 := by decide
            rw [← total_add, ← h6]; apply total_mono 4; intro s
            have ha := h s (all_worlds 4 s)
            cases hs : isSZ s
            · simp [Balanced242Plateau.ind]
            · by_cases hz : zeroCnt s = 0
              · by_cases h4' : z y s * z y s = 4
                · rw [hs, decide_eq_true hz, decide_eq_true h4'] at ha; simp at ha
                · simp [hz, h4', Balanced242Plateau.ind]
              · by_cases h4' : z y s * z y s = 4 <;> simp [hz, h4', Balanced242Plateau.ind]
          omega
      obtain ⟨s, hsZ, hz0, h4⟩ := hex_s
      obtain ⟨_, eps, heps, hsh, _⟩ := hzf_props s hsZ hz0
      have h1 := hsh y; rw [if_pos h10] at h1
      have hnz : w y s ≠ 0 := by
        intro hw0
        have : z y s * z y s = 0 := by
          dsimp only [w] at hw0
          have hc : chr (L_u s) (L_e y) = 1 ∨ chr (L_u s) (L_e y) = -1 := sign_vals _
          have hz0' : z y s = 0 := by rcases hc with e | e <;> rw [e] at hw0 <;> omega
          rw [hz0']; rfl
        omega
      by_cases h10d : mcell (add 4 y d) = 10
      · exact h10d
      · exfalso; rw [if_neg h10d, Int.mul_zero] at h1; exact hnz h1
    -- Pick the 5 distinct `d`-pairs of `X_10` (`p0, p1, p2, p3, p4 : W 4` with `p_i ⊕ p_j ∉ {0, d}`),
    -- and find TWO zero-free cosets `sa ≠ sb` whose missing `d`-pairs inside `X_10` are DISTINCT (`P_sa ≠ P_sb`)!
    -- Wait: for ANY zero-free `s ∈ SZ`, define its missing set `Miss s y := (mcell y = 10) ∧ (z y s = 0)`.
    -- Its size is `n10c - hits10 s = 10 - 8 = 2`, AND it is closed under `y ↦ y ⊕ d`, so `Miss s = {y_s, y_s ⊕ d}`!
    have hmiss_pair (s : W 4) (hsZ : isSZ s = true) (hz0 : zeroCnt s = 0) :
        ∃ ys : W 4, mcell ys = 10 ∧ z ys s = 0 ∧
          ∀ y, (mcell y = 10 ∧ z y s = 0) ↔ (y = ys ∨ y = add 4 ys d) := by
      obtain ⟨hh8, eps, heps, hsh, _⟩ := hzf_props s hsZ hz0
      let M (y : W 4) : Bool := decide (mcell y = 10) && decide (z y s = 0)
      have hM_cnt : total 4 (fun y => bind (M y)) = 2 := by
        have hpt (y : W 4) : bind (M y) = (if mcell y = 10 then (1 : Int) else 0) -
            (if mcell y = 10 && decide (z y s * z y s = 4) then (1 : Int) else 0) := by
          dsimp only [M]; by_cases h10 : mcell y = 10
          · rcases ((((hcell_ok y).2 (by rw [h10]; decide)).2.2.2.2.2.1 h10).2.1 s hsZ) with hz | hz
            · have hz0' : z y s = 0 := by rcases sq_cases (z y s) 0 hz with e | e <;> exact e
              rw [hz, hz0']; simp [h10, Balanced242Plateau.ind]
            · have hnz' : z y s ≠ 0 := by intro e; rw [e] at hz; omega
              rw [hz]; simp [h10, hnz', Balanced242Plateau.ind]
          · simp [h10, Balanced242Plateau.ind]
        rw [funext hpt, total_sub]; change n10c - hits10 s = 2; omega
      have hex_ys : ∃ ys : W 4, M ys = true := by
        cases h : (worlds 4).all (fun y => !M y)
        · obtain ⟨ys, _, hys⟩ := all_false_exists _ _ h
          exact ⟨ys, by cases e : M ys <;> rw [e] at hys <;> simp at hys ⊢⟩
        · exfalso; rw [List.all_eq_true] at h
          have h0 : total 4 (fun y => bind (M y)) = 0 := by
            rw [← total_zero 4]; apply congrArg (total 4); funext y
            have hy := h y (all_worlds 4 y); cases e : M y <;> rw [e] at hy <;> simp [Balanced242Plateau.ind] at hy ⊢
          omega
      obtain ⟨ys, hys⟩ := hex_ys
      have hys10 : mcell ys = 10 := by dsimp only [M] at hys; by_cases e : mcell ys = 10 <;> simp [e] at hys ⊢
      have hysz0 : z ys s = 0 := by dsimp only [M] at hys; by_cases e : z ys s = 0 <;> simp [e] at hys ⊢
      have hysd10 : mcell (add 4 ys d) = 10 := hX10_closed ys hys10
      have hysdz0 : z (add 4 ys d) s = 0 := by
        have h1 := hsh ys; rw [if_pos hys10, if_pos hysd10] at h1
        dsimp only [w] at h1; rw [hysz0, Int.mul_zero] at h1
        have hc : chr (L_u s) (L_e (add 4 ys d)) = 1 ∨ chr (L_u s) (L_e (add 4 ys d)) = -1 := sign_vals _
        rcases heps with a | a <;> rcases hc with b | b <;> rw [a, b] at h1 <;> omega
      have hne_d : ys ≠ add 4 ys d := by
        intro e; apply hd_ne
        have h1 := congrArg (add 4 ys) e
        rw [add_self, ← Balanced242Plateau.add_assoc', add_self, add_zero_left] at h1; exact h1.symm
      have hM_eq (y : W 4) : bind (M y) = hits ys y + hits (add 4 ys d) y := by
        have hge (u : W 4) : 0 ≤ bind (M u) - (hits ys u + hits (add 4 ys d) u) := by
          unfold hits; by_cases e1 : ys = u
          · subst e1; simp [hys, hne_d.symm, Balanced242Plateau.ind]
          · by_cases e2 : add 4 ys d = u
            · subst e2; have hMd : M (add 4 ys d) = true := by simp [M, hysd10, hysdz0]
              simp [hMd, e1, Balanced242Plateau.ind]
            · simp [e1, e2]; exact Balanced242Plateau.ind_nonneg _
        have hsum : total 4 (fun u => bind (M u) - (hits ys u + hits (add 4 ys d) u)) = 0 := by
          rw [total_sub, total_add, diagonal 4 ys, diagonal 4 (add 4 ys d), hM_cnt]; omega
        have hp := point_le_total 4 _ hge y; rw [hsum] at hp; have h0 := hge y; omega
      refine ⟨ys, hys10, hysz0, fun y => ?_⟩
      have h := hM_eq y
      constructor
      · intro ⟨h1, h2⟩
        have hM1 : M y = true := by simp [M, h1, h2]
        rw [hM1] at h; simp only [Balanced242Plateau.ind, if_true] at h
        unfold hits at h; by_cases e1 : ys = y
        · exact Or.inl e1.symm
        · by_cases e2 : add 4 ys d = y
          · exact Or.inr e2.symm
          · simp [e1, e2] at h
      · intro hor; rcases hor with rfl | rfl
        · exact ⟨hys10, hysz0⟩
        · exact ⟨hysd10, hysdz0⟩
    -- Pick TWO zero-free cosets `sa, sb ∈ SZ` whose missing pairs `P_sa ≠ P_sb` are DISJOINT!
    -- Proof: pick ONE zero-free `sa` and its missing point `ya`. Since `ya` has `mcell ya = 10`,
    -- `ya` has `z ya s = 0` on ONLY 2 cosets of `SZ`, so among the ≥ 4 zero-free cosets of `SZ`,
    -- at least `4 - 2 = 2` zero-free cosets `sb` have `z ya sb ≠ 0`!
    -- For ANY such `sb`: `ya ∉ P_sb`, hence `ya ⊕ yb ∉ {0, d}`!!
    have hex_sa : ∃ sa : W 4, isSZ sa = true ∧ zeroCnt sa = 0 := by
      cases h : (worlds 4).all (fun s => !(isSZ s && decide (zeroCnt s = 0)))
      · obtain ⟨sa, _, hsa⟩ := all_false_exists _ _ h
        exact ⟨sa, by cases e : isSZ sa <;> rw [e] at hsa <;> simp at hsa ⊢,
                   by by_cases e : zeroCnt sa = 0 <;> simp [e] at hsa ⊢⟩
      · exfalso; rw [List.all_eq_true] at h
        have h0 : total 4 (fun s => if isSZ s && decide (zeroCnt s = 0) then (1 : Int) else 0) = 0 := by
          refine Eq.trans ?_ (total_zero 4)
          apply congrArg (total 4); funext s
          have hs := h s (all_worlds 4 s); cases e : isSZ s && decide (zeroCnt s = 0) <;> simp [e] at hs ⊢
        omega
    obtain ⟨sa, hsa_SZ, hsa_z0⟩ := hex_sa
    obtain ⟨ya, hya10, hyaz_sa, hya_miss⟩ := hmiss_pair sa hsa_SZ hsa_z0
    have hex_sb : ∃ sb : W 4, isSZ sb = true ∧ zeroCnt sb = 0 ∧ z ya sb ≠ 0 := by
      cases h : (worlds 4).all (fun s => !(isSZ s && decide (zeroCnt s = 0) && decide (z ya s ≠ 0)))
      · obtain ⟨sb, _, hsb⟩ := all_false_exists _ _ h
        exact ⟨sb, by cases e : isSZ sb <;> rw [e] at hsb <;> simp at hsb ⊢,
                   by by_cases e : zeroCnt sb = 0 <;> simp [e] at hsb ⊢,
                   by by_cases e : z ya sb = 0 <;> simp [e] at hsb ⊢⟩
      · exfalso; rw [List.all_eq_true] at h
        -- Every zero-free `s ∈ SZ` (≥ 4 of them!) has `z ya s = 0`, contradicting `#{isSZ ∧ z ya s^2 = 4} = 4` inside 6!
        have h4 := (((hcell_ok ya).2 (by rw [hya10]; decide)).2.2.2.2.2.1 hya10).2.2.1
        have hle6 : total 4 (fun s => if isSZ s && decide (zeroCnt s = 0) then (1 : Int) else 0) +
                    total 4 (fun s => if isSZ s && decide (z ya s * z ya s = 4) then (1 : Int) else 0) ≤ 6 := by
          have h6 : total 4 (fun s => bind (isSZ s)) = 6 := by decide
          rw [← total_add, ← h6]; apply total_mono 4; intro s
          have hs := h s (all_worlds 4 s)
          cases hsz : isSZ s
          · simp [Balanced242Plateau.ind]
          · by_cases hz : zeroCnt s = 0
            · by_cases h4' : z ya s * z ya s = 4
              · have hnz : z ya s ≠ 0 := by intro e; rw [e] at h4'; omega
                rw [hsz, decide_eq_true hz, decide_eq_true hnz] at hs; simp at hs
              · simp [hz, h4', Balanced242Plateau.ind]
            · by_cases h4' : z ya s * z ya s = 4 <;> simp [hz, h4', Balanced242Plateau.ind]
        omega
    obtain ⟨sb, hsb_SZ, hsb_z0, hyanz_sb⟩ := hex_sb
    obtain ⟨yb, hyb10, hybz_sb, hyb_miss⟩ := hmiss_pair sb hsb_SZ hsb_z0
    -- Notice `ya` and `yb` are in DISJOINT `d`-pairs: `add 4 ya yb ∉ {zero 4, d}`!
    have hyab_disj : add 4 ya yb ≠ zero 4 ∧ add 4 ya yb ≠ d := by
      constructor
      · intro hz; apply hyanz_sb
        have heq : ya = yb := (add_cancel_left ya yb ya (by rw [add_self]; exact hz)).symm
        rw [heq]; exact hybz_sb
      · intro hed; apply hyanz_sb
        have heq : ya = add 4 yb d := by
          rw [← hed, add_comm 4 ya yb, ← Balanced242Plateau.add_assoc', add_self, add_zero_left]
        exact ((hyb_miss ya).mpr (Or.inr heq)).2
    -- Extract the remaining THREE `d`-pairs `x1, x2, x3` of `X_10 \ ({ya, ya⊕d} ∪ {yb, yb⊕d})` (size `10 - 4 = 6`)!
    have add_cancel_r (a b c : W 4) (h : add 4 a c = add 4 b c) : a = b := by
      rw [add_comm 4 a c, add_comm 4 b c] at h; exact add_cancel_left c a b h
    let Rem (y : W 4) : Bool :=
      decide (mcell y = 10) && !decide (y = ya) && !decide (y = add 4 ya d) &&
      !decide (y = yb) && !decide (y = add 4 yb d)
    have hRem_cnt : total 4 (fun y => bind (Rem y)) = 6 := by
      have hne_ad : ya ≠ add 4 ya d := by
        intro e; apply hd_ne; have h := congrArg (add 4 ya) e
        rw [add_self, ← Balanced242Plateau.add_assoc', add_self, add_zero_left] at h; exact h.symm
      have hne_bd : yb ≠ add 4 yb d := by
        intro e; apply hd_ne; have h := congrArg (add 4 yb) e
        rw [add_self, ← Balanced242Plateau.add_assoc', add_self, add_zero_left] at h; exact h.symm
      have hne_ab : ya ≠ yb := fun e => hyab_disj.1 (by rw [e, add_self])
      have hne_abd : ya ≠ add 4 yb d := fun e => hyab_disj.2 (by rw [e, add_comm 4 yb d, Balanced242Plateau.add_assoc', add_self, add_zero_right] )
      have hne_adb : add 4 ya d ≠ yb := fun e => hyab_disj.2 (by rw [← e, ← Balanced242Plateau.add_assoc', add_self, add_zero_left])
      have hne_adbd : add 4 ya d ≠ add 4 yb d := fun e => hne_ab (add_cancel_r ya yb d e)
      have hpt (y : W 4) : bind (Rem y) = (if mcell y = 10 then (1 : Int) else 0) -
          (hits ya y + hits (add 4 ya d) y + hits yb y + hits (add 4 yb d) y) := by
        dsimp only [Rem]; unfold hits
        by_cases e1 : ya = y
        · subst e1; simp [hya10, hne_ad.symm, hne_ab.symm, hne_abd.symm, Balanced242Plateau.ind]
        · by_cases e2 : add 4 ya d = y
          · subst e2; simp [hX10_closed ya hya10, e1, hne_ad, hne_adb.symm, hne_adbd.symm, Balanced242Plateau.ind]
          · by_cases e3 : yb = y
            · subst e3; simp [hyb10, e1, e2, hne_ab, hne_adb, hne_bd.symm, Balanced242Plateau.ind]
            · by_cases e4 : add 4 yb d = y
              · subst e4; simp [hX10_closed yb hyb10, e1, e2, e3, hne_abd, hne_adbd, hne_bd, Balanced242Plateau.ind]
              · have f1 : y ≠ ya := fun h => e1 h.symm
                have f2 : y ≠ add 4 ya d := fun h => e2 h.symm
                have f3 : y ≠ yb := fun h => e3 h.symm
                have f4 : y ≠ add 4 yb d := fun h => e4 h.symm
                by_cases h10 : mcell y = 10 <;> simp [h10, e1, e2, e3, e4, f1, f2, f3, f4, Balanced242Plateau.ind]
      rw [funext hpt, total_sub, total_add, total_add, total_add,
          diagonal 4 ya, diagonal 4 (add 4 ya d), diagonal 4 yb, diagonal 4 (add 4 yb d)]
      change n10c - (1 + 1 + 1 + 1) = 6; omega
    have hRem_closed (y : W 4) (hr : Rem y = true) : Rem (add 4 y d) = true := by
      dsimp only [Rem] at hr ⊢
      have h10 : mcell y = 10 := by by_cases e : mcell y = 10 <;> simp [e] at hr ⊢
      have h10d := hX10_closed y h10
      have n1 : y ≠ ya := by intro e; subst e; simp at hr
      have n2 : y ≠ add 4 ya d := by intro e; subst e; simp at hr
      have n3 : y ≠ yb := by intro e; subst e; simp at hr
      have n4 : y ≠ add 4 yb d := by intro e; subst e; simp at hr
      have f1 : add 4 y d ≠ ya := fun e => n2 (by rw [← e, Balanced242Plateau.add_assoc', add_self, add_zero_right])
      have f2 : add 4 y d ≠ add 4 ya d := fun e => n1 (add_cancel_r y ya d e)
      have f3 : add 4 y d ≠ yb := fun e => n4 (by rw [← e, Balanced242Plateau.add_assoc', add_self, add_zero_right])
      have f4 : add 4 y d ≠ add 4 yb d := fun e => n3 (add_cancel_r y yb d e)
      simp [h10d, f1, f2, f3, f4]
    -- Peel 3 `d`-pairs `x1, x2, x3` from `Rem` (size 6 → 4 → 2 → 0)!
    have peel_pair (P : W 4 → Bool) (k : Int) (hk : 2 ≤ k)
        (hcnt : total 4 (fun y => bind (P y)) = k) (hclosed : ∀ y, P y = true → P (add 4 y d) = true) :
        ∃ x : W 4, P x = true ∧
          let P' (y : W 4) := P y && !decide (y = x) && !decide (y = add 4 x d)
          total 4 (fun y => bind (P' y)) = k - 2 ∧ (∀ y, P' y = true → P' (add 4 y d) = true) := by
      have hex : ∃ x : W 4, P x = true := by
        cases h : (worlds 4).all (fun y => !P y)
        · obtain ⟨x, _, hx⟩ := all_false_exists _ _ h
          exact ⟨x, by cases e : P x <;> rw [e] at hx <;> simp at hx ⊢⟩
        · exfalso; rw [List.all_eq_true] at h
          have h0 : total 4 (fun y => bind (P y)) = 0 := by
            rw [← total_zero 4]; apply congrArg (total 4); funext y
            have hy := h y (all_worlds 4 y); cases e : P y <;> rw [e] at hy <;> simp [Balanced242Plateau.ind] at hy ⊢
          omega
      obtain ⟨x, hx⟩ := hex
      have hxd := hclosed x hx
      have hne : x ≠ add 4 x d := by
        intro e; apply hd_ne; have h := congrArg (add 4 x) e
        rw [add_self, ← Balanced242Plateau.add_assoc', add_self, add_zero_left] at h; exact h.symm
      refine ⟨x, hx, ?_, ?_⟩
      · have hpt (y : W 4) : bind (P y && !decide (y = x) && !decide (y = add 4 x d)) =
            bind (P y) - (hits x y + hits (add 4 x d) y) := by
          unfold hits; by_cases e1 : x = y
          · subst e1; simp [hx, hne.symm, Balanced242Plateau.ind]
          · by_cases e2 : add 4 x d = y
            · subst e2; simp [hxd, e1, hne, Balanced242Plateau.ind]
            · have f1 : y ≠ x := fun h => e1 h.symm
              have f2 : y ≠ add 4 x d := fun h => e2 h.symm
              simp [e1, e2, f1, f2]
        rw [funext hpt, total_sub, total_add, diagonal 4 x, diagonal 4 (add 4 x d), hcnt]; omega
      · intro y hy
        have hP : P y = true := by cases e : P y <;> simp [e] at hy ⊢
        have n1 : y ≠ x := by intro e; subst e; simp at hy
        have n2 : y ≠ add 4 x d := by intro e; subst e; simp at hy
        have f1 : add 4 y d ≠ x := fun e => n2 (by rw [← e, Balanced242Plateau.add_assoc', add_self, add_zero_right])
        have f2 : add 4 y d ≠ add 4 x d := fun e => n1 (add_cancel_r y x d e)
        simp [hclosed y hP, f1, f2]
    obtain ⟨x1, hx1, hR1_cnt, hR1_cl⟩ := peel_pair Rem 6 (by decide) hRem_cnt hRem_closed
    obtain ⟨x2, hx2, hR2_cnt, hR2_cl⟩ := peel_pair _ 4 (by decide) hR1_cnt hR1_cl
    obtain ⟨x3, hx3, hR3_cnt, _⟩ := peel_pair _ 2 (by decide) hR2_cnt hR2_cl
    -- Helper: applying `four_dpairs_xor_in_0d` to ANY zero-free `s` whose support in `X_10` is 4 `d`-pairs `{p0, x1, x2, x3}`!
    have h4xor_of_supp (s p0 : W 4) (hsZ : isSZ s = true) (hz0 : zeroCnt s = 0)
        (hp0_m : mcell p0 = 10) (hx1_m : mcell x1 = 10) (hx2_m : mcell x2 = 10) (hx3_m : mcell x3 = 10)
        (hdisj01 : add 4 p0 x1 ≠ zero 4 ∧ add 4 p0 x1 ≠ d)
        (hdisj02 : add 4 p0 x2 ≠ zero 4 ∧ add 4 p0 x2 ≠ d)
        (hdisj03 : add 4 p0 x3 ≠ zero 4 ∧ add 4 p0 x3 ≠ d)
        (hdisj12 : add 4 x1 x2 ≠ zero 4 ∧ add 4 x1 x2 ≠ d)
        (hdisj13 : add 4 x1 x3 ≠ zero 4 ∧ add 4 x1 x3 ≠ d)
        (hdisj23 : add 4 x2 x3 ≠ zero 4 ∧ add 4 x2 x3 ≠ d)
        (hsupp : ∀ y, (mcell y = 10 ∧ z y s ≠ 0) ↔
          y = p0 ∨ y = add 4 p0 d ∨ y = x1 ∨ y = add 4 x1 d ∨
          y = x2 ∨ y = add 4 x2 d ∨ y = x3 ∨ y = add 4 x3 d) :
        add 4 (add 4 p0 x1) (add 4 x2 x3) = zero 4 ∨ add 4 (add 4 p0 x1) (add 4 x2 x3) = d := by
      obtain ⟨_, eps, heps, hsh, htr_eps⟩ := hzf_props s hsZ hz0
      let h10 (y : W 4) : Int := if mcell y = 10 then w y s else 0
      have hw_pm2 (u : W 4) (hu : mcell u = 10 ∧ z u s ≠ 0) : w u s / 2 = 1 ∨ w u s / 2 = -1 := by
        have h4 : z u s * z u s = 4 := by
          rcases ((((hcell_ok u).2 (by rw [hu.1]; decide)).2.2.2.2.2.1 hu.1).2.1 s hsZ) with h | h
          · exfalso; rcases sq_cases (z u s) 0 h with e | e <;> exact hu.2 e
          · exact h
        have hw4 : w u s * w u s = 4 := by
          dsimp only [w]; have h1 : chr (L_u s) (L_e u) * chr (L_u s) (L_e u) = 1 := sign_sq _
          calc (chr (L_u s) (L_e u) * z u s) * (chr (L_u s) (L_e u) * z u s)
              = (chr (L_u s) (L_e u) * chr (L_u s) (L_e u)) * (z u s * z u s) := by ac_rfl
            _ = 4 := by rw [h1, Int.one_mul, h4]
        rcases sq_cases (w u s) 2 hw4 with e | e <;> rw [e] <;> decide
      have hp0_s : mcell p0 = 10 ∧ z p0 s ≠ 0 := (hsupp p0).mpr (Or.inl rfl)
      have hx1_s : mcell x1 = 10 ∧ z x1 s ≠ 0 := (hsupp x1).mpr (Or.inr (Or.inr (Or.inl rfl)))
      have hx2_s : mcell x2 = 10 ∧ z x2 s ≠ 0 := (hsupp x2).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have hx3_s : mcell x3 = 10 ∧ z x3 s ≠ 0 := (hsupp x3).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      let s0 := w p0 s / 2; let s1 := w x1 s / 2; let s2 := w x2 s / 2; let s3 := w x3 s / 2
      apply four_dpairs_xor_in_0d d p0 x1 x2 x3 eps s0 s1 s2 s3 hd_ne heps
        (hw_pm2 p0 hp0_s) (hw_pm2 x1 hx1_s) (hw_pm2 x2 hx2_s) (hw_pm2 x3 hx3_s)
        hdisj01 hdisj02 hdisj03 hdisj12 hdisj13 hdisj23
      intro r hr
      -- On `chr d r = eps`, `transform h10 r = 4 * (s0 chr p0 r + s1 chr x1 r + s2 chr x2 r + s3 chr x3 r) = ±8`!
      have hne_pair (a b : W 4) (h : add 4 a b ≠ zero 4 ∧ add 4 a b ≠ d) :
          a ≠ b ∧ a ≠ add 4 b d ∧ add 4 a d ≠ b ∧ add 4 a d ≠ add 4 b d := by
        refine ⟨fun e => h.1 (by rw [e, add_self]),
                fun e => h.2 (by rw [e, add_comm 4 b d, Balanced242Plateau.add_assoc', add_self, add_zero_right]),
                fun e => h.2 (by rw [← e, ← Balanced242Plateau.add_assoc', add_self, add_zero_left]),
                fun e => h.1 (by rw [add_cancel_r a b d e, add_self])⟩
      have hne_d (a : W 4) : a ≠ add 4 a d := fun e => hd_ne (by
        have h := congrArg (add 4 a) e
        rw [add_self, ← Balanced242Plateau.add_assoc', add_self, add_zero_left] at h; exact h.symm)
      have hpair_val (u : W 4) (hu : mcell u = 10 ∧ z u s ≠ 0) :
          w u s = 2 * (w u s / 2) ∧ w (add 4 u d) s = 2 * eps * (w u s / 2) := by
        have h1 := hsh u; rw [if_pos hu.1, if_pos (hX10_closed u hu.1)] at h1
        rcases hw_pm2 u hu with e | e
        · have hw2 : w u s = 2 := by
            have h4 : w u s * w u s = 4 := by
              dsimp only [w]; have h1' : chr (L_u s) (L_e u) * chr (L_u s) (L_e u) = 1 := sign_sq _
              rcases ((((hcell_ok u).2 (by rw [hu.1]; decide)).2.2.2.2.2.1 hu.1).2.1 s hsZ) with h | h
              · exfalso; rcases sq_cases (z u s) 0 h with ez | ez <;> exact hu.2 ez
              · calc (chr (L_u s) (L_e u) * z u s) * (chr (L_u s) (L_e u) * z u s)
                    = (chr (L_u s) (L_e u) * chr (L_u s) (L_e u)) * (z u s * z u s) := by ac_rfl
                  _ = 4 := by rw [h1', Int.one_mul, h]
            rcases sq_cases (w u s) 2 h4 with ew | ew <;> rw [ew] at e ⊢ <;> omega
          rcases heps with ep | ep <;> rw [ep] at h1 ⊢ <;> omega
        · have hwm2 : w u s = -2 := by
            have h4 : w u s * w u s = 4 := by
              dsimp only [w]; have h1' : chr (L_u s) (L_e u) * chr (L_u s) (L_e u) = 1 := sign_sq _
              rcases ((((hcell_ok u).2 (by rw [hu.1]; decide)).2.2.2.2.2.1 hu.1).2.1 s hsZ) with h | h
              · exfalso; rcases sq_cases (z u s) 0 h with ez | ez <;> exact hu.2 ez
              · calc (chr (L_u s) (L_e u) * z u s) * (chr (L_u s) (L_e u) * z u s)
                    = (chr (L_u s) (L_e u) * chr (L_u s) (L_e u)) * (z u s * z u s) := by ac_rfl
                  _ = 4 := by rw [h1', Int.one_mul, h]
            rcases sq_cases (w u s) 2 h4 with ew | ew <;> rw [ew] at e ⊢ <;> omega
          rcases heps with ep | ep <;> rw [ep] at h1 ⊢ <;> omega
      have htr_eq : transform h10 r = 4 * (s0 * chr p0 r + s1 * chr x1 r + s2 * chr x2 r + s3 * chr x3 r) := by
        have hpair_term (u : W 4) (hu : mcell u = 10 ∧ z u s ≠ 0) :
            w u s * chr r u + w (add 4 u d) s * chr r (add 4 u d) = 4 * ((w u s / 2) * chr u r) := by
          have ⟨ha, hb⟩ := hpair_val u hu
          have hch : chr r (add 4 u d) = chr r u * eps := by
            rw [Balanced242Plateau.chr_add, show chr r d = chr d r by unfold chr; rw [dot_comm], hr]
          have hsym : chr r u = chr u r := by unfold chr; rw [dot_comm]
          rw [ha, hb, hch, hsym]
          rcases heps with ep | ep <;> rw [ep] <;> simp [Int.mul_assoc] <;> omega
        have hpt (y : W 4) : h10 y * chr r y =
            w p0 s * chr r p0 * hits p0 y + w (add 4 p0 d) s * chr r (add 4 p0 d) * hits (add 4 p0 d) y +
            w x1 s * chr r x1 * hits x1 y + w (add 4 x1 d) s * chr r (add 4 x1 d) * hits (add 4 x1 d) y +
            w x2 s * chr r x2 * hits x2 y + w (add 4 x2 d) s * chr r (add 4 x2 d) * hits (add 4 x2 d) y +
            w x3 s * chr r x3 * hits x3 y + w (add 4 x3 d) s * chr r (add 4 x3 d) * hits (add 4 x3 d) y := by
          have q01 := hne_pair p0 x1 hdisj01; have q02 := hne_pair p0 x2 hdisj02; have q03 := hne_pair p0 x3 hdisj03
          have q12 := hne_pair x1 x2 hdisj12; have q13 := hne_pair x1 x3 hdisj13; have q23 := hne_pair x2 x3 hdisj23
          unfold hits; dsimp only [h10]
          by_cases e0 : p0 = y
          · subst e0; simp [hp0_m, hne_d p0, q01.1, q01.2.1, q02.1, q02.2.1, q03.1, q03.2.1,
              (hne_d p0).symm, q01.1.symm, q01.2.1.symm, q02.1.symm, q02.2.1.symm, q03.1.symm, q03.2.1.symm]
          · by_cases e0d : add 4 p0 d = y
            · subst e0d; simp [hX10_closed p0 hp0_m, e0, q01.2.2.1, q01.2.2.2, q02.2.2.1, q02.2.2.2, q03.2.2.1, q03.2.2.2,
                q01.2.2.1.symm, q01.2.2.2.symm, q02.2.2.1.symm, q02.2.2.2.symm, q03.2.2.1.symm, q03.2.2.2.symm]
            · by_cases e1 : x1 = y
              · subst e1; simp [hx1_m, e0, e0d, hne_d x1, (hne_d x1).symm, q12.1, q12.2.1, q13.1, q13.2.1,
                  q12.1.symm, q12.2.1.symm, q13.1.symm, q13.2.1.symm]
              · by_cases e1d : add 4 x1 d = y
                · subst e1d; simp [hX10_closed x1 hx1_m, e0, e0d, e1, q12.2.2.1, q12.2.2.2, q13.2.2.1, q13.2.2.2,
                    q12.2.2.1.symm, q12.2.2.2.symm, q13.2.2.1.symm, q13.2.2.2.symm]
                · by_cases e2 : x2 = y
                  · subst e2; simp [hx2_m, e0, e0d, e1, e1d, hne_d x2, (hne_d x2).symm, q23.1, q23.2.1, q23.1.symm, q23.2.1.symm]
                  · by_cases e2d : add 4 x2 d = y
                    · subst e2d; simp [hX10_closed x2 hx2_m, e0, e0d, e1, e1d, e2, q23.2.2.1, q23.2.2.2, q23.2.2.1.symm, q23.2.2.2.symm]
                    · by_cases e3 : x3 = y
                      · subst e3; simp [hx3_m, e0, e0d, e1, e1d, e2, e2d, hne_d x3, (hne_d x3).symm]
                      · by_cases e3d : add 4 x3 d = y
                        · subst e3d; simp [hX10_closed x3 hx3_m, e0, e0d, e1, e1d, e2, e2d, e3]
                        · simp only [e0, e0d, e1, e1d, e2, e2d, e3, e3d, if_false, Int.mul_zero, Int.add_zero]
                          by_cases h10y : mcell y = 10
                          · rw [if_pos h10y]
                            have hz0y : z y s = 0 := by
                              by_cases hz : z y s = 0
                              · exact hz
                              · exfalso
                                rcases (hsupp y).mp ⟨h10y, hz⟩ with h | h | h | h | h | h | h | h
                                · exact e0 h.symm
                                · exact e0d h.symm
                                · exact e1 h.symm
                                · exact e1d h.symm
                                · exact e2 h.symm
                                · exact e2d h.symm
                                · exact e3 h.symm
                                · exact e3d h.symm
                            dsimp only [w]; rw [hz0y]; simp
                          · rw [if_neg h10y]; simp
        unfold transform; rw [funext hpt]
        simp only [total_add, total_scale, diagonal 4, Int.mul_one]
        have t0 := hpair_term p0 hp0_s; have t1 := hpair_term x1 hx1_s
        have t2 := hpair_term x2 hx2_s; have t3 := hpair_term x3 hx3_s
        dsimp only [s0, s1, s2, s3]; omega
      rcases htr_eps r hr with h8 | hm8
      · rw [htr_eq] at h8; have h2 : s0 * chr p0 r + s1 * chr x1 r + s2 * chr x2 r + s3 * chr x3 r = 2 := by omega
        rw [h2]; decide
      · rw [htr_eq] at hm8; have hm2 : s0 * chr p0 r + s1 * chr x1 r + s2 * chr x2 r + s3 * chr x3 r = -2 := by omega
        rw [hm2]; decide
    -- Verify the disjointness and support partition for BOTH `sa` (missing `ya`, keeping `yb, x1, x2, x3`)
    -- AND `sb` (missing `yb`, keeping `ya, x1, x2, x3`)!
    have hx1_rem : Rem x1 = true := hx1
    have hx2_rem : Rem x2 = true := by cases e : Rem x2 <;> rw [e] at hx2 <;> simp at hx2 ⊢
    have hx3_rem : Rem x3 = true := by cases e : Rem x3 <;> rw [e] at hx3 <;> simp at hx3 ⊢
    have hrem_m10 (u : W 4) (hr : Rem u = true) : mcell u = 10 := by
      dsimp only [Rem] at hr; by_cases e : mcell u = 10 <;> simp [e] at hr ⊢
    have hrem_disj (u : W 4) (hr : Rem u = true) :
        (add 4 ya u ≠ zero 4 ∧ add 4 ya u ≠ d) ∧ (add 4 yb u ≠ zero 4 ∧ add 4 yb u ≠ d) := by
      dsimp only [Rem] at hr
      have n1 : u ≠ ya := by intro e; subst e; simp at hr
      have n2 : u ≠ add 4 ya d := by intro e; subst e; simp at hr
      have n3 : u ≠ yb := by intro e; subst e; simp at hr
      have n4 : u ≠ add 4 yb d := by intro e; subst e; simp at hr
      refine ⟨⟨fun e => n1 (add_cancel_left ya u ya (by rw [add_self]; exact e)),
               fun e => n2 (by rw [← e, ← Balanced242Plateau.add_assoc', add_self, add_zero_left])⟩,
              ⟨fun e => n3 (add_cancel_left yb u yb (by rw [add_self]; exact e)),
               fun e => n4 (by rw [← e, ← Balanced242Plateau.add_assoc', add_self, add_zero_left])⟩⟩
    have h12_disj : add 4 x1 x2 ≠ zero 4 ∧ add 4 x1 x2 ≠ d := by
      have n1 : x2 ≠ x1 := by intro e; subst e; simp at hx2
      have n2 : x2 ≠ add 4 x1 d := by intro e; subst e; simp at hx2
      exact ⟨fun e => n1 (add_cancel_left x1 x2 x1 (by rw [add_self]; exact e)),
             fun e => n2 (by rw [← e, ← Balanced242Plateau.add_assoc', add_self, add_zero_left])⟩
    have h13_disj : add 4 x1 x3 ≠ zero 4 ∧ add 4 x1 x3 ≠ d := by
      have n1 : x3 ≠ x1 := by intro e; subst e; simp at hx3
      have n2 : x3 ≠ add 4 x1 d := by intro e; subst e; simp at hx3
      exact ⟨fun e => n1 (add_cancel_left x1 x3 x1 (by rw [add_self]; exact e)),
             fun e => n2 (by rw [← e, ← Balanced242Plateau.add_assoc', add_self, add_zero_left])⟩
    have h23_disj : add 4 x2 x3 ≠ zero 4 ∧ add 4 x2 x3 ≠ d := by
      have n1 : x3 ≠ x2 := by intro e; subst e; simp at hx3
      have n2 : x3 ≠ add 4 x2 d := by intro e; subst e; simp at hx3
      exact ⟨fun e => n1 (add_cancel_left x2 x3 x2 (by rw [add_self]; exact e)),
             fun e => n2 (by rw [← e, ← Balanced242Plateau.add_assoc', add_self, add_zero_left])⟩
    -- Every `y` with `mcell y = 10` lies in `{ya, ya⊕d, yb, yb⊕d, x1, x1⊕d, x2, x2⊕d, x3, x3⊕d}` (since `hR3_cnt = 0`!)!
    have hX10_all (y : W 4) (h10 : mcell y = 10) :
        y = ya ∨ y = add 4 ya d ∨ y = yb ∨ y = add 4 yb d ∨
        y = x1 ∨ y = add 4 x1 d ∨ y = x2 ∨ y = add 4 x2 d ∨ y = x3 ∨ y = add 4 x3 d := by
      let R3 (u : W 4) : Bool :=
        Rem u && !decide (u = x1) && !decide (u = add 4 x1 d) &&
        !decide (u = x2) && !decide (u = add 4 x2 d) &&
        !decide (u = x3) && !decide (u = add 4 x3 d)
      have h0 : R3 y = false := by
        have hp := point_le_total 4 (fun u => bind (R3 u)) (fun _ => Balanced242Plateau.ind_nonneg _) y
        have hR3_0 : total 4 (fun u => bind (R3 u)) = 0 := by simpa [R3] using hR3_cnt
        rw [hR3_0] at hp
        cases e : R3 y
        · rfl
        · rw [e] at hp; simp [Balanced242Plateau.ind] at hp
      dsimp only [R3, Rem] at h0
      by_cases e1 : y = ya; · exact Or.inl e1
      by_cases e2 : y = add 4 ya d; · exact Or.inr (Or.inl e2)
      by_cases e3 : y = yb; · exact Or.inr (Or.inr (Or.inl e3))
      by_cases e4 : y = add 4 yb d; · exact Or.inr (Or.inr (Or.inr (Or.inl e4)))
      by_cases e5 : y = x1; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e5))))
      by_cases e6 : y = add 4 x1 d; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e6)))))
      by_cases e7 : y = x2; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e7))))))
      by_cases e8 : y = add 4 x2 d; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e8)))))))
      by_cases e9 : y = x3; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e9))))))))
      by_cases e10 : y = add 4 x3 d; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e10))))))))
      simp [h10, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10] at h0
    have hxor_a : add 4 (add 4 yb x1) (add 4 x2 x3) = zero 4 ∨ add 4 (add 4 yb x1) (add 4 x2 x3) = d := by
      apply h4xor_of_supp sa yb hsa_SZ hsa_z0 hyb10 (hrem_m10 x1 hx1_rem) (hrem_m10 x2 hx2_rem) (hrem_m10 x3 hx3_rem)
        (hrem_disj x1 hx1_rem).2 (hrem_disj x2 hx2_rem).2 (hrem_disj x3 hx3_rem).2 h12_disj h13_disj h23_disj
      intro y; constructor
      · intro ⟨h10, hnz⟩
        rcases hX10_all y h10 with h | h | h | h | h | h | h | h | h | h
        · rw [h] at hnz; exact absurd ((hya_miss ya).mpr (Or.inl rfl)).2 hnz
        · rw [h] at hnz; exact absurd ((hya_miss (add 4 ya d)).mpr (Or.inr rfl)).2 hnz
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
      · intro hor
        have hnot_ya (u : W 4) (h : add 4 ya u ≠ zero 4 ∧ add 4 ya u ≠ d) (hm : mcell u = 10) :
            (mcell u = 10 ∧ z u sa ≠ 0) ∧ (mcell (add 4 u d) = 10 ∧ z (add 4 u d) sa ≠ 0) := by
          refine ⟨⟨hm, fun hz => ?_⟩, ⟨hX10_closed u hm, fun hz => ?_⟩⟩
          · rcases (hya_miss u).mp ⟨hm, hz⟩ with e | e
            · exact h.1 (by rw [e, add_self])
            · exact h.2 (by rw [e, ← Balanced242Plateau.add_assoc', add_self, add_zero_left])
          · rcases (hya_miss (add 4 u d)).mp ⟨hX10_closed u hm, hz⟩ with e | e
            · exact h.2 (by rw [← e, add_comm 4 u d, Balanced242Plateau.add_assoc', add_self, add_zero_right])
            · exact h.1 (by rw [add_cancel_r u ya d e, add_self])
        rcases hor with h | h | h | h | h | h | h | h
        · rw [h]; exact (hnot_ya yb hyab_disj hyb10).1
        · rw [h]; exact (hnot_ya yb hyab_disj hyb10).2
        · rw [h]; exact (hnot_ya x1 (hrem_disj x1 hx1_rem).1 (hrem_m10 x1 hx1_rem)).1
        · rw [h]; exact (hnot_ya x1 (hrem_disj x1 hx1_rem).1 (hrem_m10 x1 hx1_rem)).2
        · rw [h]; exact (hnot_ya x2 (hrem_disj x2 hx2_rem).1 (hrem_m10 x2 hx2_rem)).1
        · rw [h]; exact (hnot_ya x2 (hrem_disj x2 hx2_rem).1 (hrem_m10 x2 hx2_rem)).2
        · rw [h]; exact (hnot_ya x3 (hrem_disj x3 hx3_rem).1 (hrem_m10 x3 hx3_rem)).1
        · rw [h]; exact (hnot_ya x3 (hrem_disj x3 hx3_rem).1 (hrem_m10 x3 hx3_rem)).2
    have hxor_b : add 4 (add 4 ya x1) (add 4 x2 x3) = zero 4 ∨ add 4 (add 4 ya x1) (add 4 x2 x3) = d := by
      have hyba_disj : add 4 yb ya ≠ zero 4 ∧ add 4 yb ya ≠ d := by rw [add_comm 4 yb ya]; exact hyab_disj
      apply h4xor_of_supp sb ya hsb_SZ hsb_z0 hya10 (hrem_m10 x1 hx1_rem) (hrem_m10 x2 hx2_rem) (hrem_m10 x3 hx3_rem)
        (hrem_disj x1 hx1_rem).1 (hrem_disj x2 hx2_rem).1 (hrem_disj x3 hx3_rem).1 h12_disj h13_disj h23_disj
      intro y; constructor
      · intro ⟨h10, hnz⟩
        rcases hX10_all y h10 with h | h | h | h | h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · rw [h] at hnz; exact absurd ((hyb_miss yb).mpr (Or.inl rfl)).2 hnz
        · rw [h] at hnz; exact absurd ((hyb_miss (add 4 yb d)).mpr (Or.inr rfl)).2 hnz
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
      · intro hor
        have hnot_yb (u : W 4) (h : add 4 yb u ≠ zero 4 ∧ add 4 yb u ≠ d) (hm : mcell u = 10) :
            (mcell u = 10 ∧ z u sb ≠ 0) ∧ (mcell (add 4 u d) = 10 ∧ z (add 4 u d) sb ≠ 0) := by
          refine ⟨⟨hm, fun hz => ?_⟩, ⟨hX10_closed u hm, fun hz => ?_⟩⟩
          · rcases (hyb_miss u).mp ⟨hm, hz⟩ with e | e
            · exact h.1 (by rw [e, add_self])
            · exact h.2 (by rw [e, ← Balanced242Plateau.add_assoc', add_self, add_zero_left])
          · rcases (hyb_miss (add 4 u d)).mp ⟨hX10_closed u hm, hz⟩ with e | e
            · exact h.2 (by rw [← e, add_comm 4 u d, Balanced242Plateau.add_assoc', add_self, add_zero_right])
            · exact h.1 (by rw [add_cancel_r u yb d e, add_self])
        rcases hor with h | h | h | h | h | h | h | h
        · rw [h]; exact (hnot_yb ya hyba_disj hya10).1
        · rw [h]; exact (hnot_yb ya hyba_disj hya10).2
        · rw [h]; exact (hnot_yb x1 (hrem_disj x1 hx1_rem).2 (hrem_m10 x1 hx1_rem)).1
        · rw [h]; exact (hnot_yb x1 (hrem_disj x1 hx1_rem).2 (hrem_m10 x1 hx1_rem)).2
        · rw [h]; exact (hnot_yb x2 (hrem_disj x2 hx2_rem).2 (hrem_m10 x2 hx2_rem)).1
        · rw [h]; exact (hnot_yb x2 (hrem_disj x2 hx2_rem).2 (hrem_m10 x2 hx2_rem)).2
        · rw [h]; exact (hnot_yb x3 (hrem_disj x3 hx3_rem).2 (hrem_m10 x3 hx3_rem)).1
        · rw [h]; exact (hnot_yb x3 (hrem_disj x3 hx3_rem).2 (hrem_m10 x3 hx3_rem)).2
    -- XOR `hxor_a` and `hxor_b`: `add 4 ya yb ∈ {zero 4, d}`, CONTRADICTING `hyab_disj`!!
    have hxor_ab : add 4 ya yb = add 4 (add 4 (add 4 ya x1) (add 4 x2 x3)) (add 4 (add 4 yb x1) (add 4 x2 x3)) := by
      have hcomm (p q r s : W 4) : add 4 (add 4 p q) (add 4 r s) = add 4 (add 4 p r) (add 4 q s) := by
        rw [Balanced242Plateau.add_assoc', ← Balanced242Plateau.add_assoc' 4 q r s,
            add_comm 4 q r, Balanced242Plateau.add_assoc' 4 r q s, ← Balanced242Plateau.add_assoc']
      rw [hcomm, add_self, add_zero_right, hcomm, add_self, add_zero_right]
    rcases hxor_b with hb0 | hbd <;> rcases hxor_a with ha0 | had
    · rw [hb0, ha0, add_zero_left] at hxor_ab; exact hyab_disj.1 hxor_ab
    · rw [hb0, had, add_zero_left] at hxor_ab; exact hyab_disj.2 hxor_ab
    · rw [hbd, ha0, add_zero_right] at hxor_ab; exact hyab_disj.2 hxor_ab
    · rw [hbd, had, add_self] at hxor_ab; exact hyab_disj.1 hxor_ab

end Balanced242T112

#print axioms Balanced242T112.rank4_Z96_n0_ge8
#print axioms Balanced242T112.rank4_Z96_n0_eq8_subspace
#print axioms Balanced242T112.no_t112
