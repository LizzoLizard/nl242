/-
  Exact global rank-8 parity theorem:

    r = 8  ↔  (pa f g + pc f g) % 2 = 1,

  where `r` is the global phase polar rank (`cntGood f g = 2 ^ r`) and `k = pa + pc` counts
  the high masks with `|hi f g a| ∈ {4, 12}`.

  Proof:
    * By `phase_identity`, `sum_x U(x) * transform q8 x = 32 * (2t - 232 - k)`.
    * For r ∈ {0, 2, 4}, `transform q8 x ∈ {0, ±M}` with `64 ∣ M`, so `64 ∣ LHS`, hence `k % 2 = 0`.
    * For r = 6 (`M = 32`, `rr = 4`), `S_good` + `swap` gives
      `4 * sum_{good} U = q8(0) * sum_{rad} q8(d) * transform U d ≡ 4 * 2 ≡ 0 (mod 8)`,
      so `sum_{good} U` is even, hence `64 ∣ 32 * sum (U * σ)`, hence `k % 2 = 0`.
    * For r = 8 (`M = 16`), by symplectic induction (`bent_parity m`) on `W (2*m)`,
      any `U : W (2*m) → Int` with `transform U a % 4 = 2` everywhere and bent phase
      `transform q x = 2^m * σ x` satisfies `sum_x U(x) * σ(x) ≡ 2 - 2m (mod 4)`.
      At `m = 4` (`W 8`), `sum_x U(x) * σ(x) ≡ 2 (mod 4)`, so `LHS ≡ 32 (mod 64)`, hence `k % 2 = 1`.
-/
import Balanced242RankCond
import Balanced242Coord

namespace Balanced242Parity
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Global
open Balanced242Reduction (cnt clsA clsC pa pc)
open Balanced242SectionFacts (U point_le_total)
open Balanced242Plateau (Cube bt cube_of_spec ell rad phi rad_spec ell_hom ind ind_nonneg
  all_false_exists add_assoc' add_zero_right sign_sq)
open Balanced242Rank (good rr rr_pos S_good spec_good rr_good spec_values rad_zero)
open Balanced242RankCond (q8 phase_identity sign_vals)
open Balanced242Coord (transv transv_invol transv_add transv_dot exists_transv_axis)

/-! ## Constructive Riesz representation on `W n` -/

def linearVec : (n : Nat) → (W n → Bool) → W n
  | 0, _ => ()
  | n + 1, f => (f (true, zero n), linearVec n (fun x => f (false, x)))

theorem linearVec_zero {n : Nat} (f : W n → Bool)
    (hf : ∀ x y, f (add n x y) = xor (f x) (f y)) : f (zero n) = false := by
  have h := hf (zero n) (zero n)
  rw [add_self] at h
  cases hx : f (zero n) <;> simp [hx] at h ⊢

theorem linearVec_dot : ∀ (n : Nat) (f : W n → Bool),
    (∀ x y, f (add n x y) = xor (f x) (f y)) →
    ∀ x, dot n (linearVec n f) x = f x
  | 0, f, hf, () => (linearVec_zero f hf).symm
  | n + 1, f, hf, (b, x) => by
    have hf' : ∀ y z, f (false, add n y z) = xor (f (false, y)) (f (false, z)) := fun y z => by
      simpa [add] using hf (false, y) (false, z)
    have ih := linearVec_dot n (fun y => f (false, y)) hf' x
    have hsplit : (b, x) = add (n + 1) (b, zero n) (false, x) := by
      simp [add, add_zero_left]
    have hR : f (b, x) = xor (f (b, zero n)) (f (false, x)) := by
      rw [hsplit, hf (b, zero n) (false, x)]
    rw [hR]
    change xor (f (true, zero n) && b) (dot n (linearVec n (fun y => f (false, y))) x) =
      xor (f (b, zero n)) (f (false, x))
    rw [ih]
    cases b
    · have hz : f (false, zero n) = false := linearVec_zero f hf
      simp [hz]
    · simp

/-! ## Linear involution invariance -/

private theorem transform_pull {n : Nat} (T Tt : W n → W n)
    (hTi : ∀ x, T (T x) = x) (hTti : ∀ x, Tt (Tt x) = x)
    (hdot : ∀ a x, dot n (T a) x = dot n a (Tt x))
    (F : W n → Int) (a : W n) :
    transform (fun x => F (Tt x)) a = transform F (T a) := by
  unfold transform
  have step (x : W n) : F (Tt x) * chr a x = F (Tt x) * chr (T a) (Tt x) := by
    simp only [chr]
    have h1 := hdot (T a) x
    rw [hTi a] at h1
    rw [h1]
  simp only [step]
  exact reindex Tt Tt hTti hTti (fun y => F y * chr (T a) y)

private theorem transform_pull_dual {n : Nat} (T Tt : W n → W n)
    (hTi : ∀ x, T (T x) = x) (hTti : ∀ x, Tt (Tt x) = x)
    (hdot : ∀ a x, dot n (T a) x = dot n a (Tt x))
    (G : W n → Int) (x : W n) :
    transform (fun a => G (T a)) x = transform G (Tt x) := by
  apply transform_pull Tt T hTti hTi
  intro a y
  rw [dot_comm n (Tt a) y, ← hdot y a]
  exact dot_comm n (T y) a

/-! ## Two-bit bent slice lemma -/

private theorem two_bit_tau (r01 r10 r11 : Int)
    (h01 : r01 = 1 ∨ r01 = -1) (h10 : r10 = 1 ∨ r10 = -1) (h11 : r11 = 1 ∨ r11 = -1)
    (hbent : r01 * r10 * r11 = -1) :
    let τ : Bool → Bool → Int := fun c0 c1 =>
      (1 + sign c1 * r01 + sign c0 * r10 + sign c0 * sign c1 * r11) / 2
    (∀ c0 c1, (τ c0 c1 = 1 ∨ τ c0 c1 = -1) ∧
      2 * τ c0 c1 = 1 + sign c1 * r01 + sign c0 * r10 + sign c0 * sign c1 * r11) ∧
    (∃ (tmaj : Int) (c0s c1s : Bool), (tmaj = 1 ∨ tmaj = -1) ∧
      ∀ c0 c1, τ c0 c1 = tmaj * (1 - 2 * (if c0 == c0s && c1 == c1s then 1 else 0))) := by
  rcases h01 with rfl | rfl <;> rcases h10 with rfl | rfl <;> rcases h11 with rfl | rfl
  · exact absurd hbent (by decide)
  · refine ⟨fun c0 c1 => by cases c0 <;> cases c1 <;> decide,
      1, true, true, Or.inl rfl, fun c0 c1 => by cases c0 <;> cases c1 <;> decide⟩
  · refine ⟨fun c0 c1 => by cases c0 <;> cases c1 <;> decide,
      1, false, true, Or.inl rfl, fun c0 c1 => by cases c0 <;> cases c1 <;> decide⟩
  · exact absurd hbent (by decide)
  · refine ⟨fun c0 c1 => by cases c0 <;> cases c1 <;> decide,
      1, true, false, Or.inl rfl, fun c0 c1 => by cases c0 <;> cases c1 <;> decide⟩
  · exact absurd hbent (by decide)
  · exact absurd hbent (by decide)
  · refine ⟨fun c0 c1 => by cases c0 <;> cases c1 <;> decide,
      1, false, false, Or.inl rfl, fun c0 c1 => by cases c0 <;> cases c1 <;> decide⟩

private theorem bt_mod8 (w q : Int) (hw : w % 4 = 2) (hq : sign (bt (w / 2)) = q) :
    ∃ k : Int, w = 8 * k + 4 - 2 * q := by
  unfold bt at hq
  cases hb : decide (w / 2 / 2 % 2 = 1)
  · rw [hb] at hq
    simp only [decide_eq_false_iff_not] at hb
    have hq1 : q = 1 := by simpa [sign] using hq.symm
    exact ⟨(w + 2 * q - 4) / 8, by omega⟩
  · rw [hb] at hq
    simp only [decide_eq_true_eq] at hb
    have hq1 : q = -1 := by simpa [sign] using hq.symm
    exact ⟨(w + 2 * q - 4) / 8, by omega⟩

private theorem two_bit_slice_odd (s00 s01 s10 s11 q0 r01 r10 r11 : Int)
    (hq0 : q0 = 1 ∨ q0 = -1)
    (h01 : r01 = 1 ∨ r01 = -1) (h10 : r10 = 1 ∨ r10 = -1) (h11 : r11 = 1 ∨ r11 = -1)
    (hbent : r01 * r10 * r11 = -1)
    (h00 : (s00 + s01 + s10 + s11) % 4 = 2 ∧
      sign (bt ((s00 + s01 + s10 + s11) / 2)) = q0)
    (h01w : (s00 - s01 + s10 - s11) % 4 = 2 ∧
      sign (bt ((s00 - s01 + s10 - s11) / 2)) = q0 * r01)
    (h10w : (s00 + s01 - s10 - s11) % 4 = 2 ∧
      sign (bt ((s00 + s01 - s10 - s11) / 2)) = q0 * r10)
    (h11w : (s00 - s01 - s10 + s11) % 4 = 2 ∧
      sign (bt ((s00 - s01 - s10 + s11) / 2)) = q0 * r11) :
    s00 % 2 = 1 ∧ s01 % 2 = 1 ∧ s10 % 2 = 1 ∧ s11 % 2 = 1 := by
  obtain ⟨k00, e00⟩ := bt_mod8 _ _ h00.1 h00.2
  obtain ⟨k01, e01⟩ := bt_mod8 _ _ h01w.1 h01w.2
  obtain ⟨k10, e10⟩ := bt_mod8 _ _ h10w.1 h10w.2
  obtain ⟨k11, e11⟩ := bt_mod8 _ _ h11w.1 h11w.2
  have p00 : q0 * (1 + r01 + r10 + r11) = q0 + q0 * r01 + q0 * r10 + q0 * r11 := by
    simp only [Int.mul_add, Int.mul_one]
  have p01 : q0 * (1 - r01 + r10 - r11) = q0 - q0 * r01 + q0 * r10 - q0 * r11 := by
    simp only [Int.mul_sub, Int.mul_add, Int.mul_one]
  have p10 : q0 * (1 + r01 - r10 - r11) = q0 + q0 * r01 - q0 * r10 - q0 * r11 := by
    simp only [Int.mul_sub, Int.mul_add, Int.mul_one]
  have p11 : q0 * (1 - r01 - r10 + r11) = q0 - q0 * r01 - q0 * r10 + q0 * r11 := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_one]
  have t00 : 2 * s00 = 4 * (k00 + k01 + k10 + k11 + 2) - q0 * (1 + r01 + r10 + r11) := by omega
  have t01 : 2 * s01 = 4 * (k00 - k01 + k10 - k11) - q0 * (1 - r01 + r10 - r11) := by omega
  have t10 : 2 * s10 = 4 * (k00 + k01 - k10 - k11) - q0 * (1 + r01 - r10 - r11) := by omega
  have t11 : 2 * s11 = 4 * (k00 - k01 - k10 + k11) - q0 * (1 - r01 - r10 + r11) := by omega
  have hsums : (1 + r01 + r10 + r11 = 2 ∨ 1 + r01 + r10 + r11 = -2) ∧
               (1 - r01 + r10 - r11 = 2 ∨ 1 - r01 + r10 - r11 = -2) ∧
               (1 + r01 - r10 - r11 = 2 ∨ 1 + r01 - r10 - r11 = -2) ∧
               (1 - r01 - r10 + r11 = 2 ∨ 1 - r01 - r10 + r11 = -2) := by
    rcases h01 with rfl | rfl <;> rcases h10 with rfl | rfl <;> rcases h11 with rfl | rfl <;>
    first | exact absurd hbent (by decide) | decide
  have odd_of (s K c : Int) (heq : 2 * s = 4 * K - q0 * c) (hc : c = 2 ∨ c = -2) : s % 2 = 1 := by
    rcases hq0 with rfl | rfl <;> rcases hc with rfl | rfl <;> omega
  exact ⟨odd_of s00 _ _ t00 hsums.1,
         odd_of s01 _ _ t01 hsums.2.1,
         odd_of s10 _ _ t10 hsums.2.2.1,
         odd_of s11 _ _ t11 hsums.2.2.2⟩

/-! ## Elementary helper lemmas -/

private theorem total_mod2_sign : ∀ (n : Nat) (F σ : W n → Int),
    (∀ x, σ x = 1 ∨ σ x = -1) →
    total n (fun x => F x * σ x) % 2 = total n F % 2
  | 0, F, σ, hσ => by
    change (F () * σ ()) % 2 = F () % 2
    rcases hσ () with h | h <;> rw [h] <;> omega
  | n + 1, F, σ, hσ => by
    show (total n (fun x => F (false, x) * σ (false, x)) +
          total n (fun x => F (true, x) * σ (true, x))) % 2 =
         (total n (fun x => F (false, x)) + total n (fun x => F (true, x))) % 2
    have h0 := total_mod2_sign n (fun x => F (false, x)) (fun x => σ (false, x)) (fun x => hσ (false, x))
    have h1 := total_mod2_sign n (fun x => F (true, x)) (fun x => σ (true, x)) (fun x => hσ (true, x))
    dsimp only at h0 h1
    omega

private theorem two_points_le_total : ∀ (n : Nat) (F : W n → Int),
    (∀ x, 0 ≤ F x) → ∀ x y : W n, x ≠ y → F x + F y ≤ total n F
  | 0, _, _, (), (), hne => absurd rfl hne
  | n + 1, F, hnn, (b1, x1), (b2, x2), hne => by
    show F (b1, x1) + F (b2, x2) ≤ total n (fun z => F (false, z)) + total n (fun z => F (true, z))
    have hnn0 (z : W n) : 0 ≤ F (false, z) := hnn (false, z)
    have hnn1 (z : W n) : 0 ≤ F (true, z) := hnn (true, z)
    have ht0 : 0 ≤ total n (fun z => F (false, z)) := by
      rw [← total_zero n]; exact total_mono n _ _ hnn0
    have ht1 : 0 ≤ total n (fun z => F (true, z)) := by
      rw [← total_zero n]; exact total_mono n _ _ hnn1
    cases b1 <;> cases b2
    · have hxne : x1 ≠ x2 := fun h => hne (by rw [h])
      have ih := two_points_le_total n (fun z => F (false, z)) hnn0 x1 x2 hxne
      dsimp only at ih; omega
    · have p1 := point_le_total n (fun z => F (false, z)) hnn0 x1
      have p2 := point_le_total n (fun z => F (true, z)) hnn1 x2
      omega
    · have p1 := point_le_total n (fun z => F (true, z)) hnn1 x1
      have p2 := point_le_total n (fun z => F (false, z)) hnn0 x2
      omega
    · have hxne : x1 ≠ x2 := fun h => hne (by rw [h])
      have ih := two_points_le_total n (fun z => F (true, z)) hnn1 x1 x2 hxne
      dsimp only at ih; omega

private theorem pow2_pos : ∀ k : Nat, (0 : Int) < (2 : Int) ^ k
  | 0 => by decide
  | k + 1 => by
    have ih := pow2_pos k
    rw [Int.pow_succ]
    omega

private theorem many_double : ∀ k : Nat, many (2 * k) = ((2 : Int) ^ k) * ((2 : Int) ^ k)
  | 0 => by decide
  | k + 1 => by
    have ih := many_double k
    unfold many at ih ⊢
    change (2 : Int) ^ (2 * k + 1 + 1) = (2 : Int) ^ (k + 1) * (2 : Int) ^ (k + 1)
    rw [Int.pow_succ, Int.pow_succ, Int.pow_succ, ih]
    rw [Int.mul_assoc ((2 : Int) ^ k * (2 : Int) ^ k) 2 2,
        Int.mul_assoc ((2 : Int) ^ k) 2 ((2 : Int) ^ k * 2),
        Int.mul_left_comm 2 ((2 : Int) ^ k) 2,
        ← Int.mul_assoc ((2 : Int) ^ k) ((2 : Int) ^ k) (2 * 2)]

private theorem ell_self {n : Nat} (β : W n → Bool) (d : W n) : ell β d d = false := by
  unfold ell; rw [add_self]; cases β d <;> cases β (zero n) <;> decide

private theorem ell_comm {n : Nat} (β : W n → Bool) (a b : W n) : ell β a b = ell β b a := by
  unfold ell; rw [add_comm n b a]; cases β a <;> cases β b <;> cases β (add n a b) <;> cases β (zero n) <;> decide

private theorem ell_zero_left {n : Nat} (β : W n → Bool) (a : W n) : ell β (zero n) a = false := by
  unfold ell; rw [add_zero_right]; cases β a <;> cases β (zero n) <;> decide

private theorem sign_ell {n : Nat} (β : W n → Bool) (a b : W n) :
    sign (β (add n a b)) = sign (β (zero n)) * sign (β a) * sign (β b) * sign (ell β a b) := by
  unfold ell
  rw [add_comm n a b]
  cases β (add n b a) <;> cases β a <;> cases β b <;> cases β (zero n) <;> decide

private theorem total_bool2 {n : Nat} (F : W (n + 2) → Int) :
    total (n + 2) F =
      total n (fun z => F (false, (false, z))) + total n (fun z => F (false, (true, z))) +
      total n (fun z => F (true, (false, z))) + total n (fun z => F (true, (true, z))) := by
  change (total n (fun z => F (false, (false, z))) + total n (fun z => F (false, (true, z)))) +
         (total n (fun z => F (true, (false, z))) + total n (fun z => F (true, (true, z)))) = _
  omega

private theorem mul_reassoc4 (a b c d : Int) : a * b * (c * d) = (c * a) * (b * d) := by
  rw [Int.mul_assoc, Int.mul_left_comm b c d, ← Int.mul_assoc, Int.mul_comm a c]

private theorem transform_factor {n : Nat} (r : Bool → Bool → Int) (q' : W n → Int)
    (c0 c1 : Bool) (y : W n) :
    transform (fun a : W (n + 2) => r a.1 a.2.1 * q' a.2.2) ((c0, (c1, y)) : W (n + 2)) =
      (r false false + sign c1 * r false true + sign c0 * r true false +
       sign c0 * sign c1 * r true true) * transform q' y := by
  unfold transform
  rw [total_bool2]
  have step (b0 b1 : Bool) :
      total n (fun z => r b0 b1 * q' z * @chr (n + 2) (c0, (c1, y)) (b0, (b1, z))) =
      ((if b0 then sign c0 else 1) * (if b1 then sign c1 else 1) * r b0 b1) *
        total n (fun z => q' z * chr y z) := by
    rw [← total_scale]
    apply congrArg (total n); funext z
    have hchr : @chr (n + 2) (c0, (c1, y)) (b0, (b1, z)) =
        ((if b0 then sign c0 else 1) * (if b1 then sign c1 else 1)) * chr y z := by
      simp only [chr, dot, signMul]
      cases c0 <;> cases b0 <;> cases c1 <;> cases b1 <;> simp [sign]
    rw [hchr, mul_reassoc4]
  dsimp only
  rw [step false false, step false true, step true false, step true true]
  simp only [Bool.false_eq_true, if_false, if_true, Int.one_mul, Int.mul_one, ← Int.add_mul]

private theorem transform_bool2_zero {n : Nat} (F : W (n + 2) → Int) (b0 b1 : Bool) :
    transform F ((b0, (b1, zero n)) : W (n + 2)) =
      total n (fun y => F (false, (false, y))) +
      sign b1 * total n (fun y => F (false, (true, y))) +
      sign b0 * total n (fun y => F (true, (false, y))) +
      sign b0 * sign b1 * total n (fun y => F (true, (true, y))) := by
  unfold transform
  rw [total_bool2]
  have step (c0 c1 : Bool) :
      total n (fun y => F (c0, (c1, y)) * @chr (n + 2) (b0, (b1, zero n)) (c0, (c1, y))) =
      ((if c0 then sign b0 else 1) * (if c1 then sign b1 else 1)) *
        total n (fun y => F (c0, (c1, y))) := by
    rw [← total_scale]
    apply congrArg (total n); funext y
    have hchr : @chr (n + 2) (b0, (b1, zero n)) (c0, (c1, y)) =
        (if c0 then sign b0 else 1) * (if c1 then sign b1 else 1) := by
      simp only [chr, dot, dot_zero, Bool.xor_false, signMul]
      cases b0 <;> cases c0 <;> cases b1 <;> cases c1 <;> simp [sign]
    rw [hchr, Int.mul_comm]
  rw [step false false, step false true, step true false, step true true]
  simp only [Bool.false_eq_true, if_false, if_true, Int.one_mul, Int.mul_one]

private theorem bent_r_prod (v0 v1 v2 v3 : Int)
    (h0 : v0 = 1 ∨ v0 = -1) (h1 : v1 = 1 ∨ v1 = -1) (h2 : v2 = 1 ∨ v2 = -1) (h3 : v3 = 1 ∨ v3 = -1)
    (he : v3 = v0 * v2 * v1 * -1) : (v0 * v1) * (v0 * v2) * (v0 * v3) = -1 := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    rcases h3 with rfl | rfl <;> first | exact absurd he (by decide) | decide

private theorem dot_t3_bool (b0 b1 c0 c1 da dd dy : Bool) :
    xor (xor b0 da && c0) (xor (xor b1 dd && c1) dy) =
      xor (b0 && c0) (xor (b1 && c1) (xor dy (xor (if c0 then da else false) (if c1 then dd else false)))) := by
  cases b0 <;> cases b1 <;> cases c0 <;> cases c1 <;> cases da <;> cases dd <;> cases dy <;> decide

private theorem mul_mod64 (a M : Int) (h : M % 64 = 0) : (a * M) % 64 = 0 := by
  rw [Int.mul_emod, h, Int.mul_zero]; rfl

private theorem mul_neg_mod64 (a M : Int) (h : M % 64 = 0) : (a * -M) % 64 = 0 := by
  rw [Int.mul_neg]; have := mul_mod64 a M h; omega

private theorem pow2_eq_256 (r : Nat) (hlt : r < 9) (h : 2 ^ r = 256) : r = 8 := by
  revert h hlt; revert r; decide

/-! ## Symplectic induction: `bent_parity` on `W (2 * m)` -/

theorem bent_parity : ∀ (m : Nat) (U σ : W (2 * m) → Int),
    (∀ a, transform U a % 4 = 2) →
    (∀ x, σ x = 1 ∨ σ x = -1) →
    (∀ x, transform (fun a => sign (bt (transform U a / 2))) x = ((2 : Int) ^ m) * σ x) →
    total (2 * m) (fun x => U x * σ x) % 4 = if m % 2 = 0 then 2 else 0
  | 0, U, σ, hU, hσ, _ => by
    have hu : U () % 4 = 2 := by simpa [transform, total, chr, dot, sign] using hU ()
    change (U () * σ ()) % 4 = 2
    rcases hσ () with h | h <;> rw [h] <;> omega
  | m + 1, U, σ, hU, hσ, hq => by
    -- Setup at dimension `2 * m + 2`
    let β : W (2 * m + 2) → Bool := fun a => bt (transform U a / 2)
    let q : W (2 * m + 2) → Int := fun a => sign (β a)
    have hcube : Cube β := cube_of_spec U (fun a => transform U a / 2)
      (fun a => by dsimp only; have := hU a; omega) (fun a => by dsimp only; have := hU a; omega)
    -- Step 1: `rr β = 1`
    have hrr1 : rr β = 1 := by
      have hsg := spec_good β hcube (zero (2 * m + 2))
      have hq0 := hq (zero (2 * m + 2))
      change transform q (zero (2 * m + 2)) = (2 : Int) ^ (m + 1) * σ (zero (2 * m + 2)) at hq0
      have hsq : transform q (zero (2 * m + 2)) * transform q (zero (2 * m + 2)) = many (2 * m + 2) := by
        change _ = many (2 * (m + 1))
        rw [hq0, many_double (m + 1)]
        rcases hσ (zero (2 * m + 2)) with hs | hs <;> rw [hs]
        · simp
        · simp [Int.mul_neg, Int.neg_mul, Int.neg_neg]
      rw [hsq] at hsg
      have hmpos := many_pos (2 * m + 2)
      have h1 : rr β * ind (good β (zero (2 * m + 2))) = 1 := by
        have e : many (2 * m + 2) * (rr β * ind (good β (zero (2 * m + 2)))) =
            many (2 * m + 2) * 1 := by rw [Int.mul_one]; exact hsg.symm
        exact Int.eq_of_mul_eq_mul_left (by omega) e
      have hpos := rr_pos β
      cases hg : good β (zero (2 * m + 2)) <;> rw [hg] at h1 <;> simp [ind] at h1
      exact h1
    -- Step 2: `e0 = (true, false, 0)` is outside the radical, so find `v` with `ell β e0 v = true`
    let e0 : W (2 * m + 2) := (true, (false, zero (2 * m)))
    let e1 : W (2 * m + 2) := (false, (true, zero (2 * m)))
    have hrad0 : rad β e0 = false := by
      cases hr : rad β e0
      · rfl
      · have hne : zero (2 * m + 2) ≠ e0 := by
          intro h; exact Bool.noConfusion (congrArg Prod.fst h)
        have hle := two_points_le_total (2 * m + 2) (fun d => ind (rad β d))
          (fun d => ind_nonneg _) (zero (2 * m + 2)) e0 hne
        dsimp only at hle
        rw [rad_zero β, hr] at hle
        change 1 + 1 ≤ rr β at hle
        omega
    have hv_ex : ∃ v : W (2 * m + 2), ell β e0 v = true := by
      obtain ⟨v, _, hv⟩ := all_false_exists _ _ hrad0
      exact ⟨v, by cases he : ell β e0 v <;> simp [he] at hv ⊢⟩
    obtain ⟨⟨b0, v'⟩, hv⟩ := hv_ex
    have hv'_ell : ell β e0 (false, v') = true := by
      cases b0
      · exact hv
      · have hsplit : (true, v') = add (2 * m + 2) e0 (false, v') := by
          show (true, v') = (xor true false, add (2 * m + 1) (zero (2 * m + 1)) v')
          rw [add_zero_left]; rfl
        rw [hsplit, ell_hom β hcube e0 e0 (false, v'), ell_self β e0] at hv
        simpa using hv
    have hv'_ne : v' ≠ zero (2 * m + 1) := by
      intro h0
      rw [h0] at hv'_ell
      have hz : ell β e0 (zero (2 * m + 2)) = false := by
        rw [ell_comm]; exact ell_zero_left β e0
      change ell β e0 (zero (2 * m + 2)) = true at hv'_ell
      rw [hz] at hv'_ell; exact Bool.noConfusion hv'_ell
    -- Step 3: Pull back by extended transvection `T2` mapping `e0 ↦ e0`, `e1 ↦ (false, v')`
    obtain ⟨u2, w2, hu2, hmap⟩ := exists_transv_axis (2 * m) v' hv'_ne
    have hu2t : dot (2 * m + 1) u2 w2 = false := by rw [dot_comm]; exact hu2
    let T2 : W (2 * m + 2) → W (2 * m + 2) := fun ⟨b, y⟩ => (b, transv (2 * m + 1) u2 w2 y)
    let T2t : W (2 * m + 2) → W (2 * m + 2) := fun ⟨b, y⟩ => (b, transv (2 * m + 1) w2 u2 y)
    have hT2i (a : W (2 * m + 2)) : T2 (T2 a) = a := by
      rcases a with ⟨b, y⟩; show (b, transv (2 * m + 1) u2 w2 (transv (2 * m + 1) u2 w2 y)) = (b, y)
      rw [transv_invol _ _ _ _ hu2]
    have hT2ti (x : W (2 * m + 2)) : T2t (T2t x) = x := by
      rcases x with ⟨b, y⟩; show (b, transv (2 * m + 1) w2 u2 (transv (2 * m + 1) w2 u2 y)) = (b, y)
      rw [transv_invol _ _ _ _ hu2t]
    have hT2dot (a x : W (2 * m + 2)) : dot (2 * m + 2) (T2 a) x = dot (2 * m + 2) a (T2t x) := by
      rcases a with ⟨ba, ya⟩; rcases x with ⟨bx, yx⟩
      show xor (ba && bx) (dot (2 * m + 1) (transv (2 * m + 1) u2 w2 ya) yx) =
           xor (ba && bx) (dot (2 * m + 1) ya (transv (2 * m + 1) w2 u2 yx))
      rw [dot_comm (2 * m + 1) (transv _ u2 w2 ya) yx, transv_dot, dot_comm (2 * m + 1) (transv _ w2 u2 yx) ya]
    have hT2add (a b : W (2 * m + 2)) : T2 (add (2 * m + 2) a b) = add (2 * m + 2) (T2 a) (T2 b) := by
      rcases a with ⟨ba, ya⟩; rcases b with ⟨bb, yb⟩
      show (xor ba bb, transv (2 * m + 1) u2 w2 (add (2 * m + 1) ya yb)) = _
      rw [transv_add]; rfl
    have hT2zero : T2 (zero (2 * m + 2)) = zero (2 * m + 2) := by
      show (false, transv (2 * m + 1) u2 w2 (zero (2 * m + 1))) = (false, zero (2 * m + 1))
      unfold transv; rw [dot_zero_right]; rfl
    have hT2e0 : T2 e0 = e0 := by
      show (true, transv (2 * m + 1) u2 w2 (zero (2 * m + 1))) = (true, zero (2 * m + 1))
      unfold transv; rw [dot_zero_right]; rfl
    have hT2e1 : T2 e1 = (false, v') := by
      show (false, transv (2 * m + 1) u2 w2 (true, zero (2 * m))) = (false, v')
      rw [hmap]
    let U2 : W (2 * m + 2) → Int := fun x => U (T2t x)
    let σ2 : W (2 * m + 2) → Int := fun x => σ (T2t x)
    have hU2t (a : W (2 * m + 2)) : transform U2 a = transform U (T2 a) :=
      transform_pull T2 T2t hT2i hT2ti hT2dot U a
    let β2 : W (2 * m + 2) → Bool := fun a => bt (transform U2 a / 2)
    have hβ2 (a : W (2 * m + 2)) : β2 a = β (T2 a) := by simp only [β2, β, hU2t]
    have hq2 (x : W (2 * m + 2)) : transform (fun a => sign (β2 a)) x = ((2 : Int) ^ (m + 1)) * σ2 x := by
      have heq : (fun a => sign (β2 a)) = fun a => q (T2 a) := funext fun a => by simp only [q, hβ2]
      rw [heq, transform_pull_dual T2 T2t hT2i hT2ti hT2dot q x]
      exact hq (T2t x)
    have hsum2 : total (2 * m + 2) (fun x => U2 x * σ2 x) = total (2 * m + 2) (fun x => U x * σ x) :=
      reindex T2t T2t hT2ti hT2ti (fun y => U y * σ y)
    have hell2_01 : ell β2 e0 e1 = true := by
      unfold ell; simp only [hβ2, hT2add, hT2zero, hT2e0, hT2e1]
      exact hv'_ell
    -- Step 4: Orthogonalize `e0, e1` against `W (2*m)` via `T3`
    have hU2 (a : W (2 * m + 2)) : transform U2 a % 4 = 2 := by rw [hU2t]; exact hU (T2 a)
    have hcube2 : Cube β2 := cube_of_spec U2 (fun a => transform U2 a / 2)
      (fun a => by dsimp only; have := hU2 a; omega) (fun a => by dsimp only; have := hU2 a; omega)
    let fA : W (2 * m) → Bool := fun z => ell β2 e1 (false, (false, z))
    let fD : W (2 * m) → Bool := fun z => ell β2 e0 (false, (false, z))
    have hfA_add (z1 z2 : W (2 * m)) : fA (add (2 * m) z1 z2) = xor (fA z1) (fA z2) := by
      simpa only [fA, add, Bool.xor_false] using ell_hom β2 hcube2 e1 (false, (false, z1)) (false, (false, z2))
    have hfD_add (z1 z2 : W (2 * m)) : fD (add (2 * m) z1 z2) = xor (fD z1) (fD z2) := by
      simpa only [fD, add, Bool.xor_false] using ell_hom β2 hcube2 e0 (false, (false, z1)) (false, (false, z2))
    let vA : W (2 * m) := linearVec (2 * m) fA
    let vD : W (2 * m) := linearVec (2 * m) fD
    have hvA (z : W (2 * m)) : dot (2 * m) vA z = fA z := linearVec_dot (2 * m) fA hfA_add z
    have hvD (z : W (2 * m)) : dot (2 * m) vD z = fD z := linearVec_dot (2 * m) fD hfD_add z
    let T3 : W (2 * m + 2) → W (2 * m + 2) := fun ⟨b0, ⟨b1, z⟩⟩ =>
      (xor b0 (dot (2 * m) vA z), (xor b1 (dot (2 * m) vD z), z))
    let T3t : W (2 * m + 2) → W (2 * m + 2) := fun ⟨c0, ⟨c1, y⟩⟩ =>
      (c0, (c1, add (2 * m) y (add (2 * m) (if c0 then vA else zero (2 * m)) (if c1 then vD else zero (2 * m)))))
    have hT3i (a : W (2 * m + 2)) : T3 (T3 a) = a := by
      rcases a with ⟨b0, ⟨b1, z⟩⟩
      show (xor (xor b0 (dot (2 * m) vA z)) (dot (2 * m) vA z),
            (xor (xor b1 (dot (2 * m) vD z)) (dot (2 * m) vD z), z)) = (b0, (b1, z))
      simp [Bool.xor_assoc]
    have hT3ti (x : W (2 * m + 2)) : T3t (T3t x) = x := by
      rcases x with ⟨c0, ⟨c1, y⟩⟩
      dsimp only [T3t]
      rw [add_assoc', add_self, add_zero_right]
    have hT3dot (a x : W (2 * m + 2)) : dot (2 * m + 2) (T3 a) x = dot (2 * m + 2) a (T3t x) := by
      rcases a with ⟨b0, ⟨b1, z⟩⟩; rcases x with ⟨c0, ⟨c1, y⟩⟩
      show xor (xor b0 (dot (2 * m) vA z) && c0) (xor (xor b1 (dot (2 * m) vD z) && c1) (dot (2 * m) z y)) =
           xor (b0 && c0) (xor (b1 && c1) (dot (2 * m) z
             (add (2 * m) y (add (2 * m) (if c0 then vA else zero (2 * m)) (if c1 then vD else zero (2 * m))))))
      rw [dot_right, dot_right, dot_comm (2 * m) z (if c0 then vA else zero (2 * m)),
          dot_comm (2 * m) z (if c1 then vD else zero (2 * m))]
      have ha' : dot (2 * m) (if c0 then vA else zero (2 * m)) z = if c0 then dot (2 * m) vA z else false := by
        cases c0 <;> simp [dot_zero]
      have hd' : dot (2 * m) (if c1 then vD else zero (2 * m)) z = if c1 then dot (2 * m) vD z else false := by
        cases c1 <;> simp [dot_zero]
      rw [ha', hd']
      exact dot_t3_bool b0 b1 c0 c1 (dot (2 * m) vA z) (dot (2 * m) vD z) (dot (2 * m) z y)
    have hT3add (a b : W (2 * m + 2)) : T3 (add (2 * m + 2) a b) = add (2 * m + 2) (T3 a) (T3 b) := by
      rcases a with ⟨ba0, ⟨ba1, za⟩⟩; rcases b with ⟨bb0, ⟨bb1, zb⟩⟩
      show (xor (xor ba0 bb0) (dot (2 * m) vA (add (2 * m) za zb)),
            (xor (xor ba1 bb1) (dot (2 * m) vD (add (2 * m) za zb)), add (2 * m) za zb)) =
           (xor (xor ba0 (dot (2 * m) vA za)) (xor bb0 (dot (2 * m) vA zb)),
            (xor (xor ba1 (dot (2 * m) vD za)) (xor bb1 (dot (2 * m) vD zb)), add (2 * m) za zb))
      rw [dot_right, dot_right]
      have x4 (p q r s : Bool) : xor (xor p q) (xor r s) = xor (xor p r) (xor q s) := by
        cases p <;> cases q <;> cases r <;> cases s <;> decide
      rw [x4 ba0 bb0, x4 ba1 bb1]
    have hT3zero : T3 (zero (2 * m + 2)) = zero (2 * m + 2) := by
      show (xor false (dot (2 * m) vA (zero (2 * m))),
            (xor false (dot (2 * m) vD (zero (2 * m))), zero (2 * m))) = (false, (false, zero (2 * m)))
      simp [dot_zero_right]
    have hT3e0 : T3 e0 = e0 := by
      show (xor true (dot (2 * m) vA (zero (2 * m))),
            (xor false (dot (2 * m) vD (zero (2 * m))), zero (2 * m))) = (true, (false, zero (2 * m)))
      simp [dot_zero_right]
    have hT3e1 : T3 e1 = e1 := by
      show (xor false (dot (2 * m) vA (zero (2 * m))),
            (xor true (dot (2 * m) vD (zero (2 * m))), zero (2 * m))) = (false, (true, zero (2 * m)))
      simp [dot_zero_right]
    let U3 : W (2 * m + 2) → Int := fun x => U2 (T3t x)
    let σ3 : W (2 * m + 2) → Int := fun x => σ2 (T3t x)
    have hU3t (a : W (2 * m + 2)) : transform U3 a = transform U2 (T3 a) :=
      transform_pull T3 T3t hT3i hT3ti hT3dot U2 a
    have hU3 (a : W (2 * m + 2)) : transform U3 a % 4 = 2 := by rw [hU3t]; exact hU2 (T3 a)
    have hσ3 (x : W (2 * m + 2)) : σ3 x = 1 ∨ σ3 x = -1 := hσ (T2t (T3t x))
    let β3 : W (2 * m + 2) → Bool := fun a => bt (transform U3 a / 2)
    let q3 : W (2 * m + 2) → Int := fun a => sign (β3 a)
    have hβ3 (a : W (2 * m + 2)) : β3 a = β2 (T3 a) := by simp only [β3, β2, hU3t]
    have hq3 (x : W (2 * m + 2)) : transform q3 x = ((2 : Int) ^ (m + 1)) * σ3 x := by
      have heq : q3 = fun a => sign (β2 (T3 a)) := funext fun a => by simp only [q3, hβ3]
      rw [heq, transform_pull_dual T3 T3t hT3i hT3ti hT3dot (fun a => sign (β2 a)) x]
      exact hq2 (T3t x)
    have hsum3 : total (2 * m + 2) (fun x => U3 x * σ3 x) = total (2 * m + 2) (fun x => U x * σ x) := by
      rw [← hsum2]
      exact reindex T3t T3t hT3ti hT3ti (fun y => U2 y * σ2 y)
    have hcube3 : Cube β3 := cube_of_spec U3 (fun a => transform U3 a / 2)
      (fun a => by dsimp only; have := hU3 a; omega) (fun a => by dsimp only; have := hU3 a; omega)
    -- Orthogonality of `β3`
    have hell3_01 : ell β3 e0 e1 = true := by
      unfold ell; simp only [hβ3, hT3add, hT3zero, hT3e0, hT3e1]; exact hell2_01
    have hdec_fn (a b : Bool) (z : W (2 * m)) :
        ((a, (b, z)) : W (2 * m + 2)) =
        add (2 * m + 2) (if a then e0 else zero (2 * m + 2))
          (add (2 * m + 2) (if b then e1 else zero (2 * m + 2)) (false, (false, z))) := by
      have hz : add (2 * m) (zero (2 * m)) (add (2 * m) (zero (2 * m)) z) = z := by
        rw [add_zero_left, add_zero_left]
      cases a <;> cases b <;> exact Prod.ext rfl (Prod.ext rfl hz.symm)
    have hell3_orth (b0 b1 : Bool) (z : W (2 * m)) :
        ell β3 (b0, (b1, zero (2 * m))) (false, (false, z)) = false := by
      have h0z : ell β3 e0 (false, (false, z)) = false := by
        have hstep : ell β3 e0 (false, (false, z)) = ell β2 e0 (fA z, (fD z, z)) := by
          unfold ell; simp only [hβ3, hT3add, hT3zero, hT3e0]
          have hT3z : T3 (false, (false, z)) = (fA z, (fD z, z)) := by
            show (xor false (dot (2 * m) vA z), (xor false (dot (2 * m) vD z), z)) = _
            rw [hvA, hvD]; simp
          rw [hT3z]
        rw [hstep, hdec_fn (fA z) (fD z) z, ell_hom β2 hcube2, ell_hom β2 hcube2]
        have ha : ell β2 e0 (if fA z then e0 else zero (2 * m + 2)) = false := by
          cases fA z
          · rw [if_neg (by decide), ell_comm]; exact ell_zero_left β2 e0
          · rw [if_pos rfl]; exact ell_self β2 e0
        have hd : ell β2 e0 (if fD z then e1 else zero (2 * m + 2)) = fD z := by
          cases hf : fD z
          · rw [if_neg (by decide), ell_comm]; exact ell_zero_left β2 e0
          · rw [if_pos rfl]; exact hell2_01
        rw [ha, hd]; change xor false (xor (fD z) (fD z)) = false; simp
      have h1z : ell β3 e1 (false, (false, z)) = false := by
        have hstep : ell β3 e1 (false, (false, z)) = ell β2 e1 (fA z, (fD z, z)) := by
          unfold ell; simp only [hβ3, hT3add, hT3zero, hT3e1]
          have hT3z : T3 (false, (false, z)) = (fA z, (fD z, z)) := by
            show (xor false (dot (2 * m) vA z), (xor false (dot (2 * m) vD z), z)) = _
            rw [hvA, hvD]; simp
          rw [hT3z]
        rw [hstep, hdec_fn (fA z) (fD z) z, ell_hom β2 hcube2, ell_hom β2 hcube2]
        have ha : ell β2 e1 (if fA z then e0 else zero (2 * m + 2)) = fA z := by
          cases hf : fA z
          · rw [if_neg (by decide), ell_comm]; exact ell_zero_left β2 e1
          · rw [if_pos rfl, ell_comm]; exact hell2_01
        have hd : ell β2 e1 (if fD z then e1 else zero (2 * m + 2)) = false := by
          cases fD z
          · rw [if_neg (by decide), ell_comm]; exact ell_zero_left β2 e1
          · rw [if_pos rfl]; exact ell_self β2 e1
        rw [ha, hd]; change xor (fA z) (xor false (fA z)) = false; simp
      cases b0 <;> cases b1
      · exact ell_zero_left β3 _
      · exact h1z
      · exact h0z
      · have h11 : (true, (true, zero (2 * m))) = add (2 * m + 2) e0 e1 := by
          simp [e0, e1, add, add_zero_left]
        rw [h11, ell_comm, ell_hom β3 hcube3, ell_comm _ _ e0, ell_comm _ _ e1, h0z, h1z]; rfl
    -- Step 5: Factor `q3 (b0, (b1, z)) = r b0 b1 * q' z`
    let q0 : Int := q3 (zero (2 * m + 2))
    let r : Bool → Bool → Int := fun b0 b1 => q0 * q3 (b0, (b1, zero (2 * m)))
    let q' : W (2 * m) → Int := fun z => q3 (false, (false, z))
    have hq0 : q0 = 1 ∨ q0 = -1 := sign_vals _
    have hr00 : r false false = 1 := sign_sq _
    have hr01 : r false true = 1 ∨ r false true = -1 := by
      dsimp only [r, q0, q3]; rcases sign_vals (β3 (zero (2 * m + 2))) with h | h <;>
        rcases sign_vals (β3 (false, (true, zero (2 * m)))) with k | k <;> rw [h, k] <;> decide
    have hr10 : r true false = 1 ∨ r true false = -1 := by
      dsimp only [r, q0, q3]; rcases sign_vals (β3 (zero (2 * m + 2))) with h | h <;>
        rcases sign_vals (β3 (true, (false, zero (2 * m)))) with k | k <;> rw [h, k] <;> decide
    have hr11 : r true true = 1 ∨ r true true = -1 := by
      dsimp only [r, q0, q3]; rcases sign_vals (β3 (zero (2 * m + 2))) with h | h <;>
        rcases sign_vals (β3 (true, (true, zero (2 * m)))) with k | k <;> rw [h, k] <;> decide
    have hrbent : r false true * r true false * r true true = -1 := by
      have hse := sign_ell β3 e0 e1
      have h11 : add (2 * m + 2) e0 e1 = (true, (true, zero (2 * m))) := by
        simp [e0, e1, add, add_zero_left]
      rw [h11, hell3_01] at hse
      exact bent_r_prod _ _ _ _ (sign_vals _) (sign_vals _) (sign_vals _) (sign_vals _) hse
    have hq3_fac (a : W (2 * m + 2)) : q3 a = r a.1 a.2.1 * q' a.2.2 := by
      rcases a with ⟨b0, ⟨b1, z⟩⟩
      have hadd : (b0, (b1, z)) = add (2 * m + 2) (b0, (b1, zero (2 * m))) (false, (false, z)) := by
        simp [add, add_zero_left]
      have hse := sign_ell β3 (b0, (b1, zero (2 * m))) (false, (false, z))
      rw [← hadd, hell3_orth b0 b1 z] at hse
      change q3 (b0, (b1, z)) = q0 * q3 (b0, (b1, zero (2 * m))) * q' z * 1 at hse
      rw [Int.mul_one] at hse
      exact hse
    -- Step 6: Factor `σ3` using `two_bit_tau`
    let τ : Bool → Bool → Int := fun c0 c1 =>
      (1 + sign c1 * r false true + sign c0 * r true false + sign c0 * sign c1 * r true true) / 2
    obtain ⟨hτ, tmaj, c0s, c1s, htmaj, hτmaj⟩ := two_bit_tau _ _ _ hr01 hr10 hr11 hrbent
    change ∀ c0 c1, (τ c0 c1 = 1 ∨ τ c0 c1 = -1) ∧
      2 * τ c0 c1 = 1 + sign c1 * r false true + sign c0 * r true false + sign c0 * sign c1 * r true true at hτ
    change ∀ c0 c1, τ c0 c1 = tmaj * (1 - 2 * (if c0 == c0s && c1 == c1s then 1 else 0)) at hτmaj
    have hfac_t (c0 c1 : Bool) (y : W (2 * m)) :
        transform q3 (c0, (c1, y)) = (2 * τ c0 c1) * transform q' y := by
      have heq : q3 = fun a : W (2 * m + 2) => r a.1 a.2.1 * q' a.2.2 := funext hq3_fac
      rw [heq, transform_factor, hr00, (hτ c0 c1).2]
    let σ' : W (2 * m) → Int := fun y => τ false false * σ3 (false, (false, y))
    have hσ' (y : W (2 * m)) : σ' y = 1 ∨ σ' y = -1 := by
      dsimp only [σ']
      rcases (hτ false false).1 with h1 | h1 <;> rcases hσ3 (false, (false, y)) with h2 | h2 <;>
        rw [h1, h2] <;> decide
    have hq'_tr (c0 c1 : Bool) (y : W (2 * m)) :
        transform q' y = ((2 : Int) ^ m) * (τ c0 c1 * σ3 (c0, (c1, y))) := by
      have h1 := hq3 (c0, (c1, y))
      rw [hfac_t c0 c1 y, Int.pow_succ, Int.mul_comm ((2 : Int) ^ m) 2, Int.mul_assoc, Int.mul_assoc] at h1
      have h2 : τ c0 c1 * transform q' y = ((2 : Int) ^ m) * σ3 (c0, (c1, y)) :=
        Int.eq_of_mul_eq_mul_left (by decide) h1
      rcases (hτ c0 c1).1 with h | h <;> rw [h] at h2 ⊢ <;>
        simp only [Int.one_mul, Int.neg_mul, Int.mul_neg] at h2 ⊢ <;> omega
    have hq'_spec (y : W (2 * m)) : transform q' y = ((2 : Int) ^ m) * σ' y :=
      hq'_tr false false y
    have hσ3_fac (c0 c1 : Bool) (y : W (2 * m)) : σ3 (c0, (c1, y)) = τ c0 c1 * σ' y := by
      have h1 := (hq'_tr c0 c1 y).symm.trans (hq'_spec y)
      have h2 : τ c0 c1 * σ3 (c0, (c1, y)) = σ' y :=
        Int.eq_of_mul_eq_mul_left (by have := pow2_pos m; omega) h1
      rcases (hτ c0 c1).1 with h | h <;> rw [h] at h2 ⊢ <;> omega
    -- Step 7: Apply IH to `U' y = ∑_{c0, c1} U3 (c0, (c1, y))`
    let U' : W (2 * m) → Int := fun y =>
      U3 (false, (false, y)) + U3 (false, (true, y)) + U3 (true, (false, y)) + U3 (true, (true, y))
    have hU'_tr (z : W (2 * m)) : transform U' z = transform U3 (false, (false, z)) := by
      unfold transform
      rw [total_bool2]
      have hchr (c0 c1 : Bool) (y : W (2 * m)) :
          @chr (2 * m + 2) (false, (false, z)) (c0, (c1, y)) = chr z y := by
        simp [chr, dot]
      simp only [hchr, U', Int.add_mul, total_add]
    have hU' (z : W (2 * m)) : transform U' z % 4 = 2 := by rw [hU'_tr]; exact hU3 (false, (false, z))
    have hq'_eq : (fun z => sign (bt (transform U' z / 2))) = q' := funext fun z => by
      simp only [q', q3, β3, hU'_tr]
    have hIH := bent_parity m U' σ' hU' hσ' (by rw [hq'_eq]; exact hq'_spec)
    -- Step 8: Show each of the 4 slices `total (2*m) (fun y => U3 (c0, (c1, y)))` is odd
    let s00 := total (2 * m) (fun y => U3 (false, (false, y)))
    let s01 := total (2 * m) (fun y => U3 (false, (true, y)))
    let s10 := total (2 * m) (fun y => U3 (true, (false, y)))
    let s11 := total (2 * m) (fun y => U3 (true, (true, y)))
    have hw00 : transform U3 (false, (false, zero (2 * m))) = s00 + s01 + s10 + s11 := by
      rw [transform_bool2_zero]; simp only [s00, s01, s10, s11, sign, Bool.false_eq_true, if_false, if_true]; omega
    have hw01 : transform U3 (false, (true, zero (2 * m))) = s00 - s01 + s10 - s11 := by
      rw [transform_bool2_zero]; simp only [s00, s01, s10, s11, sign, Bool.false_eq_true, if_false, if_true]; omega
    have hw10 : transform U3 (true, (false, zero (2 * m))) = s00 + s01 - s10 - s11 := by
      rw [transform_bool2_zero]; simp only [s00, s01, s10, s11, sign, Bool.false_eq_true, if_false, if_true]; omega
    have hw11 : transform U3 (true, (true, zero (2 * m))) = s00 - s01 - s10 + s11 := by
      rw [transform_bool2_zero]; simp only [s00, s01, s10, s11, sign, Bool.false_eq_true, if_false, if_true]; omega
    have hqr (b0 b1 : Bool) : q3 (b0, (b1, zero (2 * m))) = q0 * r b0 b1 := by
      dsimp only [r]; rw [← Int.mul_assoc, sign_sq, Int.one_mul]
    have hodd := two_bit_slice_odd s00 s01 s10 s11 q0 (r false true) (r true false) (r true true)
      hq0 hr01 hr10 hr11 hrbent
      ⟨by rw [← hw00]; exact hU3 _, by rw [← hw00]; rfl⟩
      ⟨by rw [← hw01]; exact hU3 _, by rw [← hw01]; exact hqr false true⟩
      ⟨by rw [← hw10]; exact hU3 _, by rw [← hw10]; exact hqr true false⟩
      ⟨by rw [← hw11]; exact hU3 _, by rw [← hw11]; exact hqr true true⟩
    -- Step 9: Combine the 4 slices and close modulo 4
    let S (c0 c1 : Bool) : Int := total (2 * m) (fun y => U3 (c0, (c1, y)) * σ' y)
    have hS_odd : S c0s c1s % 2 = 1 := by
      dsimp only [S]
      rw [total_mod2_sign (2 * m) (fun y => U3 (c0s, (c1s, y))) σ' hσ']
      cases c0s <;> cases c1s
      · exact hodd.1
      · exact hodd.2.1
      · exact hodd.2.2.1
      · exact hodd.2.2.2
    have hU'sum : total (2 * m) (fun y => U' y * σ' y) =
        S false false + S false true + S true false + S true true := by
      simp only [U', S, Int.add_mul, total_add]
    have htotal3 : total (2 * m + 2) (fun x => U3 x * σ3 x) =
        tmaj * (total (2 * m) (fun y => U' y * σ' y) - 2 * S c0s c1s) := by
      rw [total_bool2]
      have slice (c0 c1 : Bool) :
          total (2 * m) (fun y => U3 (c0, (c1, y)) * σ3 (c0, (c1, y))) = τ c0 c1 * S c0 c1 := by
        dsimp only [S]
        rw [← total_scale]
        apply congrArg (total (2 * m)); funext y
        rw [hσ3_fac c0 c1 y, Int.mul_left_comm]
      rw [slice false false, slice false true, slice true false, slice true true, hU'sum]
      rw [hτmaj false false, hτmaj false true, hτmaj true false, hτmaj true true]
      cases c0s <;> cases c1s <;> rcases htmaj with rfl | rfl <;> simp <;> omega
    change (total (2 * m + 2) (fun x => U x * σ x)) % 4 = if (m + 1) % 2 = 0 then 2 else 0
    rw [← hsum3, htotal3]
    rcases htmaj with rfl | rfl <;> omega

/-! ## Global rank-8 parity theorem: `r = 8 ↔ k % 2 = 1` -/

private theorem total_mod2_good : ∀ (n : Nat) (F σ : W n → Int) (g : W n → Bool),
    (∀ x, (g x = true → σ x = 1 ∨ σ x = -1) ∧ (g x = false → σ x = 0)) →
    total n (fun x => F x * σ x) % 2 = total n (fun x => F x * ind (g x)) % 2
  | 0, F, σ, g, hσ => by
    change (F () * σ ()) % 2 = (F () * ind (g ())) % 2
    cases hg : g ()
    · rw [(hσ ()).2 hg]; simp [ind]
    · rcases (hσ ()).1 hg with h | h <;> rw [h] <;> simp [ind] <;> omega
  | n + 1, F, σ, g, hσ => by
    show (total n (fun x => F (false, x) * σ (false, x)) +
          total n (fun x => F (true, x) * σ (true, x))) % 2 =
         (total n (fun x => F (false, x) * ind (g (false, x))) +
          total n (fun x => F (true, x) * ind (g (true, x)))) % 2
    have h0 := total_mod2_good n (fun x => F (false, x)) (fun x => σ (false, x))
      (fun x => g (false, x)) (fun x => hσ (false, x))
    have h1 := total_mod2_good n (fun x => F (true, x)) (fun x => σ (true, x))
      (fun x => g (true, x)) (fun x => hσ (true, x))
    dsimp only at h0 h1
    omega

private theorem total_div8 : ∀ (n : Nat) (F : W n → Int),
    (∀ x, F x % 8 = 0) → total n F % 8 = 0
  | 0, F, h => h ()
  | n + 1, F, h => by
    show (total n (fun x => F (false, x)) + total n (fun x => F (true, x))) % 8 = 0
    have h0 := total_div8 n (fun x => F (false, x)) (fun x => h (false, x))
    have h1 := total_div8 n (fun x => F (true, x)) (fun x => h (true, x))
    omega

private theorem total_div64 : ∀ (n : Nat) (F : W n → Int),
    (∀ x, F x % 64 = 0) → total n F % 64 = 0
  | 0, F, h => h ()
  | n + 1, F, h => by
    show (total n (fun x => F (false, x)) + total n (fun x => F (true, x))) % 64 = 0
    have h0 := total_div64 n (fun x => F (false, x)) (fun x => h (false, x))
    have h1 := total_div64 n (fun x => F (true, x)) (fun x => h (true, x))
    omega

private theorem q8_spec_mod8 (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (a : W 8) :
    (q8 f g a * transform (U f g) a - 2) % 8 = 0 := by
  have hs := spec8 f g res a
  have ho := odd8 f g res a
  rw [hs]
  unfold q8 β8 bt
  cases hb : decide (H8 f g a / 2 % 2 = 1)
  · simp only [sign, Bool.false_eq_true, if_false, Int.one_mul]
    simp only [decide_eq_false_iff_not] at hb; omega
  · simp only [sign, if_true]
    simp only [decide_eq_true_eq] at hb; omega

/-- At global phase rank 8 (`cntGood f g = 256`), `k = pa + pc` is odd; at all lower ranks, `k` is even. -/
theorem rank8_iff_k_odd (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) :
    cntGood f g = 256 ↔ (cnt (clsA f g) + cnt (clsC f g)) % 2 = 1 := by
  have hpi := phase_identity f g res cap
  have hmod : total 8 (fun x => U f g x * transform (q8 f g) x) % 64 =
      (if cntGood f g = 256 then 32 else 0) := by
    have hU4 (a : W 8) : transform (U f g) a % 4 = 2 := by
      have hs := spec8 f g res a; have ho := odd8 f g res a; omega
    have hdiv64 (M : Int) (hM64 : M % 64 = 0) (hMM : M * M = many 8 * rr (β8 f g)) :
        total 8 (fun x => U f g x * transform (q8 f g) x) % 64 = 0 := by
      apply total_div64 8; intro x
      have hv := spec_values (β8 f g) (cube8 f g res) M hMM x
      cases hg : good (β8 f g) x
      · have h0 : transform (q8 f g) x = 0 := hv.2 hg
        rw [h0, Int.mul_zero]; rfl
      · rcases hv.1 hg with h | h
        · change transform (q8 f g) x = M at h; rw [h]; exact mul_mod64 _ M hM64
        · change transform (q8 f g) x = -M at h; rw [h]; exact mul_neg_mod64 _ M hM64
    rcases global_levels f g res with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- r = 8: apply `bent_parity 4`
      rw [if_pos h2]
      have h8 (x : W 8) : transform (q8 f g) x = 16 ∨ transform (q8 f g) x = -16 := by
        have hv := (spec_values (β8 f g) (cube8 f g res) 16 (by rw [h1]; decide) x).1
        exact hv (Balanced242RankCond.all_good f g h2 x)
      let σ : W 8 → Int := fun x => transform (q8 f g) x / 16
      have hσ (x : W 8) : σ x = 1 ∨ σ x = -1 := by
        dsimp only [σ]; rcases h8 x with h | h <;> rw [h] <;> decide
      have hqeq : (fun a => sign (bt (transform (U f g) a / 2))) = q8 f g := funext fun a => by
        have hs := spec8 f g res a
        show sign (bt (transform (U f g) a / 2)) = sign (bt (H8 f g a))
        rw [hs, Int.mul_ediv_cancel_left _ (by decide)]
      have hq16 (x : W 8) : transform (fun a => sign (bt (transform (U f g) a / 2))) x =
          ((2 : Int) ^ 4) * σ x := by
        rw [hqeq]; dsimp only [σ]; rcases h8 x with h | h <;> rw [h] <;> decide
      have hbp := bent_parity 4 (U f g) σ hU4 hσ hq16
      change (total 8 (fun x => U f g x * σ x)) % 4 = 2 at hbp
      have h16 : total 8 (fun x => U f g x * transform (q8 f g) x) =
          16 * total 8 (fun x => U f g x * σ x) := by
        rw [← total_scale]; apply congrArg (total 8); funext x
        have hx : transform (q8 f g) x = 16 * σ x := by
          dsimp only [σ]; rcases h8 x with h | h <;> rw [h] <;> decide
        rw [hx, Int.mul_left_comm]
      rw [h16]
      omega
    · -- r = 6: `rr = 4`, `M = 32`; use `S_good` + `swap`
      rw [if_neg (by omega)]
      let σ : W 8 → Int := fun x => transform (q8 f g) x / 32
      have hv32 (x : W 8) :
          (good (β8 f g) x = true → transform (q8 f g) x = 32 ∨ transform (q8 f g) x = -32) ∧
          (good (β8 f g) x = false → transform (q8 f g) x = 0) :=
        spec_values (β8 f g) (cube8 f g res) 32 (by rw [h1]; decide) x
      have h32 (x : W 8) :
          (good (β8 f g) x = true → σ x = 1 ∨ σ x = -1) ∧
          (good (β8 f g) x = false → σ x = 0) := by
        constructor
        · intro hg; dsimp only [σ]; rcases (hv32 x).1 hg with h | h <;> rw [h] <;> decide
        · intro hg; dsimp only [σ]; rw [(hv32 x).2 hg]; decide
      have h32eq : total 8 (fun x => U f g x * transform (q8 f g) x) =
          32 * total 8 (fun x => U f g x * σ x) := by
        rw [← total_scale]; apply congrArg (total 8); funext x
        have hx : transform (q8 f g) x = 32 * σ x := by
          cases hg : good (β8 f g) x
          · dsimp only [σ]; rw [(hv32 x).2 hg]; decide
          · dsimp only [σ]; rcases (hv32 x).1 hg with h | h <;> rw [h] <;> decide
        rw [hx, Int.mul_left_comm]
      have heven : total 8 (fun x => U f g x * ind (good (β8 f g) x)) % 2 = 0 := by
        have h4 : 4 * total 8 (fun y => U f g y * ind (good (β8 f g) y)) =
            q8 f g (zero 8) * total 8 (fun d => ind (rad (β8 f g) d) * (q8 f g d * transform (U f g) d)) := by
          have lhs : 4 * total 8 (fun y => U f g y * ind (good (β8 f g) y)) =
              total 8 (fun y => total 8 (fun d => ind (rad (β8 f g) d) * (U f g y * sign (phi (β8 f g) y d)))) := by
            rw [← total_scale]; apply congrArg (total 8); funext y
            rw [← h1, Int.mul_left_comm, ← S_good (β8 f g) y, ← total_scale]
            apply congrArg (total 8); funext d; rw [Int.mul_left_comm]
          rw [lhs, swap 8 8, ← total_scale]
          apply congrArg (total 8); funext d
          have inner : total 8 (fun y => ind (rad (β8 f g) d) * (U f g y * sign (phi (β8 f g) y d))) =
              ind (rad (β8 f g) d) * (q8 f g (zero 8) * (q8 f g d * transform (U f g) d)) := by
            unfold transform
            rw [← total_scale, ← total_scale, ← total_scale]
            apply congrArg (total 8); funext y
            have hphi : sign (phi (β8 f g) y d) = q8 f g (zero 8) * q8 f g d * chr d y := by
              unfold phi q8 chr
              rw [dot_comm 8 y d, signMul, signMul]
              rw [Int.mul_comm (sign (dot 8 d y)), Int.mul_assoc]
            rw [hphi]
            have reassoc : U f g y * (q8 f g (zero 8) * q8 f g d * chr d y) =
                q8 f g (zero 8) * (q8 f g d * (U f g y * chr d y)) := by
              rw [Int.mul_assoc (q8 f g (zero 8)), Int.mul_comm (U f g y),
                  Int.mul_assoc, Int.mul_assoc, Int.mul_comm (chr d y)]
            rw [reassoc]
          rw [inner, Int.mul_left_comm]
        have hmod8 : total 8 (fun d => ind (rad (β8 f g) d) * (q8 f g d * transform (U f g) d)) % 8 = 0 := by
          have hdecomp :
              total 8 (fun d => ind (rad (β8 f g) d) * (q8 f g d * transform (U f g) d)) =
              2 * rr (β8 f g) +
              total 8 (fun d => ind (rad (β8 f g) d) * (q8 f g d * transform (U f g) d - 2)) := by
            unfold rr
            rw [← total_scale, ← total_add]
            apply congrArg (total 8); funext d
            cases rad (β8 f g) d <;> simp [ind] <;> omega
          rw [hdecomp, h1]
          have hd8 : total 8 (fun d => ind (rad (β8 f g) d) * (q8 f g d * transform (U f g) d - 2)) % 8 = 0 := by
            apply total_div8 8; intro d
            have hm := q8_spec_mod8 f g res d
            cases rad (β8 f g) d <;> simp [ind] <;> omega
          omega
        rcases sign_vals (β8 f g (zero 8)) with hq0 | hq0
        · change q8 f g (zero 8) = 1 at hq0; rw [hq0, Int.one_mul] at h4; omega
        · change q8 f g (zero 8) = -1 at hq0; rw [hq0] at h4; omega
      have hσ_even : total 8 (fun x => U f g x * σ x) % 2 = 0 := by
        rw [total_mod2_good 8 (U f g) σ (good (β8 f g)) h32, heven]
      rw [h32eq]; omega
    · rw [if_neg (by omega)]; exact hdiv64 64 (by decide) (by rw [h1]; decide)
    · rw [if_neg (by omega)]; exact hdiv64 128 (by decide) (by rw [h1]; decide)
    · rw [if_neg (by omega)]; exact hdiv64 256 (by decide) (by rw [h1]; decide)
  rw [hpi] at hmod
  by_cases h256 : cntGood f g = 256
  · rw [if_pos h256] at hmod; exact ⟨fun _ => by omega, fun _ => h256⟩
  · rw [if_neg h256] at hmod; exact ⟨fun h => absurd h h256, fun h => by omega⟩

/-- Equivalent phrasing using `r : Nat` and `pa + pc`. -/
theorem rank_eq_8_iff_k_odd (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (r : Nat) (hr : cntGood f g = 2 ^ r) :
    r = 8 ↔ (pa f g + pc f g) % 2 = 1 := by
  have h := rank8_iff_k_odd f g res cap
  have cA := Balanced242Reduction.cnt_nonneg (clsA f g)
  have cC := Balanced242Reduction.cnt_nonneg (clsC f g)
  have hpa : ((pa f g + pc f g : Nat) : Int) = cnt (clsA f g) + cnt (clsC f g) := by
    unfold pa pc; omega
  have hr256 : cntGood f g = 256 ↔ r = 8 := by
    rw [hr]
    constructor
    · intro h2
      have h2n : 2 ^ r = 256 := by exact_mod_cast h2
      have hlt : r < 9 := by
        if hlt : r < 9 then exact hlt
        else
          have h9 : 9 ≤ r := by omega
          have hp : 2 ^ 9 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) h9
          omega
      exact pow2_eq_256 r hlt h2n
    · intro r8; subst r8; decide
  rw [hr256] at h
  constructor
  · intro hr8; have h1 := h.1 hr8; omega
  · intro hk; exact h.2 (by omega)

end Balanced242Parity

#print axioms Balanced242Parity.bent_parity
#print axioms Balanced242Parity.rank8_iff_k_odd
#print axioms Balanced242Parity.rank_eq_8_iff_k_odd
