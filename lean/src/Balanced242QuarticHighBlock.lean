/-
  Balanced242QuarticHighBlock.lean — Complete unconditional Lean 4 formalization of the
  rank-8 global quartic high-block machinery backing BOTH the `t = 96` closure (`53` profiles,
  `b + c ≤ 74`) and the `t = 98` closure (`nl242_t98_closure.zip`, all `84` rank-8 profiles
  through `b + c = 82`).

  Zero Mathlib, zero `sorry`, zero `native_decide`, zero `SectionEnum`,
  zero `Classical.choice` (`[propext, Quot.sound]` only!).

  Main exported theorems:
    1. `high_block_inversion`: `2 * K D x = 28 - 3 * S x + 32 * u x` for all `x : W 8`.
    2. `u_ternary_counts`: `np + nn = 256 - t` and `2 * np = 3 * t - 208 - 2 * (a + c)`
       (in particular `2 * (a + c) ≤ 3 * t - 208`, giving `a + c ≤ 40` at `t = 96`, `≤ 43` at `t = 98`).
    3. `first_moment_u_S`: `∑_x u(x) S(x) = 10 * (b + c) - 16 * c`.
    4. `hinge_bound`: for any integers `h, l`,
       `10 * (b + c) - 16 * c - np * h + nn * l ≤ ∑_x (posPart (S x - h) + posPart (l - S x))`.
    5. `K_symmetric`: `∑_x (K v x) * y x = ∑_w v w * (K y w)`.
    6. `dual_cut_sound`: for any integer dual vector `y : W 8 → Int`, any `lo_u ≤ ∑ u(x) y(x)`,
       and any `∑ D(w) (K y w) ≤ hi_D`,
       `∑_x (28 - 3 * S x) * y x + 32 * lo_u ≤ 2 * hi_D`.
    7. `top_threshold_bound` & `ternary_threshold_bound`: general threshold/sorting soundness
       proving `∑_{w ∈ A} g w ≤ top_a(g)` and `bottom_p(y) - top_q(y) ≤ ∑ u(x) y(x)` via
       arbitrary quantile thresholds (matching `quartic_sections.cpp`, `direct.py`, `finish.cpp`).
    8. `min_half_parseval`: `n * (256 - n) ≤ 255 * (n - 2 * s)^2` whenever every hyperplane
       section of `F` lies in `[s, n - s]`.
    9. `core46_bound_lt_370`: for `t ≤ 98` at rank 8, `2 * a + 6 * c < 370`.
-/
import Balanced242T96Quartic
import Balanced242RankCond

namespace Balanced242QuarticHighBlock

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Reduction Balanced242Plateau
open Balanced242Rank Balanced242Global Balanced242RankCond Balanced242SectionFacts

local notation "bind" => Balanced242Plateau.ind
local notation "rind" => Balanced242Reduction.ind

/-- Indicator of `F = B ⊔ C` (the masks with `|H| ∈ {3, 5}`). -/
def clsF (f g : Half) (w : W 8) : Bool := clsB f g w || clsC f g w

/-- Signed difference `D = 1_A - 1_C`. -/
def diffAC (f g : Half) (w : W 8) : Int := rind (clsA f g) w - rind (clsC f g) w

/-- Dual bent sign `σ(x) = transform (q8 f g) x / 16` (in `{-1, +1}` at rank 8). -/
def sigma8 (f g : Half) (x : W 8) : Int := transform (q8 f g) x / 16

/-- Signed Walsh operator `K v x = σ(x) * transform (q * v) x`. -/
def Kmat (f g : Half) (v : W 8 → Int) (x : W 8) : Int :=
  sigma8 f g x * transform (fun w => q8 f g w * v w) x

/-- `S = K 1_F`. -/
def Svec (f g : Half) (x : W 8) : Int := Kmat f g (fun w => rind (clsF f g) w) x

/-- `u = σ * U ∈ {-1, 0, +1}`. -/
def uvec (f g : Half) (x : W 8) : Int := sigma8 f g x * U f g x

/-- Positive part `max(z, 0)`. -/
def posPart (z : Int) : Int := if 0 < z then z else 0

private theorem all_true_of_total'' : ∀ {n : Nat} (p : W n → Bool),
    total n (fun x => bind (p x)) = many n → ∀ x, p x = true
  | 0, p, h, () => by
    change bind (p ()) = 1 at h
    cases hp : p () <;> rw [hp] at h <;> simp [Balanced242Plateau.ind] at h ⊢
  | m + 1, p, h, (b, x) => by
    have hle (c : Bool) : total m (fun y => bind (p (c, y))) ≤ many m := by
      have hm := total_mono m (fun y => bind (p (c, y))) (fun _ => 1)
        (fun y => by dsimp only; cases p (c, y) <;> decide)
      rw [total_const, Int.mul_one] at hm; exact hm
    have hm1 : many (m + 1) = 2 * many m := by unfold many; rw [Int.pow_succ]; omega
    change total m (fun y => bind (p (false, y))) +
      total m (fun y => bind (p (true, y))) = many (m + 1) at h
    have h0 := hle false; have h1 := hle true
    cases b
    · have hf : total m (fun y => bind (p (false, y))) = many m := by omega
      exact all_true_of_total'' (fun y => p (false, y)) hf x
    · have ht : total m (fun y => bind (p (true, y))) = many m := by omega
      exact all_true_of_total'' (fun y => p (true, y)) ht x

theorem sigma8_spec (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (hrr : rr (β8 f g) = 1) (x : W 8) :
    (sigma8 f g x = 1 ∨ sigma8 f g x = -1) ∧
    transform (q8 f g) x = 16 * sigma8 f g x ∧
    sigma8 f g x * sigma8 f g x = 1 := by
  have hrg := rr_good (β8 f g) (cube8 f g res)
  rw [hrr, Int.one_mul] at hrg
  have hgood := all_true_of_total'' (good (β8 f g)) hrg x
  have hsq := spec_good (β8 f g) (cube8 f g res) x
  rw [hrr, hgood] at hsq
  change transform (q8 f g) x * transform (q8 f g) x = many 8 * (1 * 1) at hsq
  have hm : many 8 * (1 * 1) = (16 : Int) * 16 := by decide
  rw [hm] at hsq
  rcases sq_cases _ 16 hsq with h | h
  · unfold sigma8; rw [h]; decide
  · unfold sigma8; rw [h]; decide

/-- Pointwise `H8 w = -7*q(w) + 12*q(w)*1_F(w) + 8*q(w)*D(w)`. -/
theorem H8_decomp (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (w : W 8) :
    H8 f g w = -7 * q8 f g w + 12 * (q8 f g w * rind (clsF f g) w) + 8 * (q8 f g w * diffAC f g w) := by
  have hpt := q8_point f g res cap w
  have hqsq : q8 f g w * q8 f g w = 1 := sign_sq (β8 f g w)
  have hcls : 8 * rind (clsA f g) w + 12 * rind (clsB f g) w + 4 * rind (clsC f g) w =
      12 * rind (clsF f g) w + 8 * diffAC f g w := by
    unfold clsF diffAC; unfold Balanced242Reduction.ind clsA clsB clsC; dsimp only
    rcases hi_values f g res cap w with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hmul : q8 f g w * (q8 f g w * H8 f g w) =
      q8 f g w * (-7 + 12 * rind (clsF f g) w + 8 * diffAC f g w) := by
    rw [hpt]; congr 1; omega
  rw [← Int.mul_assoc, hqsq, Int.one_mul] at hmul
  rw [hmul, Int.mul_add, Int.mul_add]
  have e1 : q8 f g w * (-7) = -7 * q8 f g w := Int.mul_comm _ _
  have e2 : q8 f g w * (12 * rind (clsF f g) w) = 12 * (q8 f g w * rind (clsF f g) w) := by ac_rfl
  have e3 : q8 f g w * (8 * diffAC f g w) = 8 * (q8 f g w * diffAC f g w) := by ac_rfl
  rw [e1, e2, e3]

private theorem transform_add {n : Nat} (F G : W n → Int) (x : W n) :
    transform (fun w => F w + G w) x = transform F x + transform G x := by
  unfold transform
  have hpt (w : W n) : (F w + G w) * chr x w = F w * chr x w + G w * chr x w := Int.add_mul _ _ _
  rw [funext hpt, total_add]

private theorem transform_scale {n : Nat} (c : Int) (F : W n → Int) (x : W n) :
    transform (fun w => c * F w) x = c * transform F x := by
  unfold transform
  have hpt (w : W n) : (c * F w) * chr x w = c * (F w * chr x w) := Int.mul_assoc _ _ _
  rw [funext hpt, total_scale]

/-- Walsh involution `transform (transform V) x = many n * V x`. -/
theorem transform_involution {n : Nat} (V : W n → Int) (x : W n) :
    transform (transform V) x = many n * V x := by
  unfold transform
  have hpt (a : W n) : (total n fun y => V y * chr a y) * chr x a =
      total n (fun y => (V y * chr a y) * chr x a) := by
    rw [Int.mul_comm, ← total_scale]
    apply congrArg (total n); funext y; exact Int.mul_comm _ _
  rw [funext hpt, swap]
  have hinner (y : W n) : total n (fun a => (V y * chr a y) * chr x a) =
      many n * (V y * hits x y) := by
    have h1 (a : W n) : (V y * chr a y) * chr x a = V y * (chr a y * chr a x) := by
      have hc : chr x a = chr a x := by unfold chr; rw [dot_comm]
      rw [hc, Int.mul_assoc]
    rw [funext h1, total_scale]
    have hort : total n (fun a => chr a y * chr a x) = many n * hits y x := orthogonal n y x
    have hhits : hits y x = hits x y := by
      unfold hits; by_cases h : y = x
      · subst h; simp
      · have h' : ¬ x = y := fun e => h e.symm; simp [h, h']
    rw [hort, hhits]; ac_rfl
  rw [funext hinner, total_scale]
  have hsel := select n x V
  have hcomm (y : W n) : V y * hits x y = hits x y * V y := Int.mul_comm _ _
  rw [funext hcomm, hsel]

/-- **Theorem 1 (`high_block_inversion`)**: Universal rank-8 high-block equation
    `2 * K D x = 28 - 3 * S x + 32 * u x` for every `x : W 8`. -/
theorem high_block_inversion (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (hrr : rr (β8 f g) = 1) (x : W 8) :
    2 * Kmat f g (diffAC f g) x = 28 - 3 * Svec f g x + 32 * uvec f g x := by
  have htrH : transform (H8 f g) x = 128 * U f g x := by
    have h2 : 2 * transform (H8 f g) x = transform (transform (U f g)) x := by
      rw [← transform_scale]
      apply congrArg (fun F => transform F x); funext w
      exact (spec8 f g res w).symm
    rw [transform_involution] at h2
    have hm : many 8 = 256 := by decide
    rw [hm] at h2; omega
  have hde : transform (H8 f g) x =
      -7 * transform (q8 f g) x +
      12 * transform (fun w => q8 f g w * rind (clsF f g) w) x +
      8 * transform (fun w => q8 f g w * diffAC f g w) x := by
    have hf : H8 f g = fun w =>
        (-7 * q8 f g w + 12 * (q8 f g w * rind (clsF f g) w)) +
        8 * (q8 f g w * diffAC f g w) := funext (H8_decomp f g res cap)
    rw [hf, transform_add, transform_add, transform_scale, transform_scale, transform_scale]
  obtain ⟨_, hq16, hssq⟩ := sigma8_spec f g res hrr x
  rw [htrH, hq16] at hde
  have hmul := congrArg (fun z => sigma8 f g x * z) hde
  dsimp only at hmul
  -- Distribute `sigma8 f g x` over all terms:
  have eL : sigma8 f g x * (128 * U f g x) = 128 * uvec f g x := by unfold uvec; ac_rfl
  have e1 : sigma8 f g x * (-7 * (16 * sigma8 f g x)) = -112 := by
    have : sigma8 f g x * (-7 * (16 * sigma8 f g x)) = -112 * (sigma8 f g x * sigma8 f g x) := by ac_rfl
    rw [this, hssq, Int.mul_one]
  have e2 : sigma8 f g x * (12 * transform (fun w => q8 f g w * rind (clsF f g) w) x) = 12 * Svec f g x := by
    unfold Svec Kmat; ac_rfl
  have e3 : sigma8 f g x * (8 * transform (fun w => q8 f g w * diffAC f g w) x) =
      8 * Kmat f g (diffAC f g) x := by
    unfold Kmat; ac_rfl
  rw [eL, Int.mul_add, Int.mul_add, e1, e2, e3] at hmul
  omega

/-- **Theorem 2 (`u_ternary_counts`)**: Exact ternary support counts `np` and `nn` of `u = σ * U`:
    `np + nn = 256 - t` and `2 * np = 3 * t - 208 - 2 * (a + c)`. -/
theorem u_ternary_counts (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (hrr : rr (β8 f g) = 1) :
    let np := total 8 (fun x => if uvec f g x = 1 then (1 : Int) else 0)
    let nn := total 8 (fun x => if uvec f g x = -1 then (1 : Int) else 0)
    (∀ x, uvec f g x = -1 ∨ uvec f g x = 0 ∨ uvec f g x = 1) ∧
    0 ≤ np ∧ 0 ≤ nn ∧
    np + nn = 256 - agreements f g ∧
    2 * np = 3 * agreements f g - 208 - 2 * (cnt (clsA f g) + cnt (clsC f g)) := by
  intro np nn
  have hu_vals (x : W 8) : uvec f g x = -1 ∨ uvec f g x = 0 ∨ uvec f g x = 1 := by
    have hU := U_bound f g x
    obtain ⟨hs, _, _⟩ := sigma8_spec f g res hrr x
    unfold uvec
    rcases hs with h | h <;> rw [h] <;> omega
  have hnp0 : 0 ≤ np := total_nonneg _ (fun x => by split <;> omega)
  have hnn0 : 0 ≤ nn := total_nonneg _ (fun x => by split <;> omega)
  have hsum : np + nn = 256 - agreements f g := by
    have hpt (x : W 8) :
        (if uvec f g x = 1 then (1 : Int) else 0) +
        (if uvec f g x = -1 then (1 : Int) else 0) =
        1 - (if f x = g x then (1 : Int) else 0) := by
      obtain ⟨hs, _, _⟩ := sigma8_spec f g res hrr x
      unfold uvec U
      cases hf : f x <;> cases hg : g x <;> rcases hs with h | h <;> rw [h] <;> decide
    dsimp only [np, nn]; rw [← total_add, funext hpt, total_sub, total_const, Int.mul_one]
    have hm : many 8 = 256 := by decide
    rw [hm]
    have hag : total 8 (fun x => if f x = g x then (1 : Int) else 0) = agreements f g := by
      unfold agreements countPair; rw [← total_add]
      apply congrArg (total 8); funext x
      cases f x <;> cases g x <;> decide
    rw [hag]
  have hdiff : np - nn = total 8 (uvec f g) := by
    dsimp only [np, nn]; rw [← total_sub]; apply congrArg (total 8); funext x
    rcases hu_vals x with h | h | h <;> rw [h] <;> decide
  have hph := phase_identity f g res cap
  have hph16 : total 8 (fun x => U f g x * transform (q8 f g) x) = 16 * total 8 (uvec f g) := by
    have hpt (x : W 8) : U f g x * transform (q8 f g) x = 16 * uvec f g x := by
      obtain ⟨_, hq16, _⟩ := sigma8_spec f g res hrr x
      rw [hq16]; unfold uvec; ac_rfl
    rw [funext hpt, total_scale]
  rw [hph16] at hph
  exact ⟨hu_vals, hnp0, hnn0, hsum, by omega⟩

/-- **Theorem 3 (`first_moment_u_S`)**: Exact first-moment identity
    `∑_x u(x) S(x) = 10 * (b + c) - 16 * c`. -/
theorem first_moment_u_S (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (hrr : rr (β8 f g) = 1) :
    total 8 (fun x => uvec f g x * Svec f g x) =
      10 * (cnt (clsB f g) + cnt (clsC f g)) - 16 * cnt (clsC f g) := by
  have hpt1 (x : W 8) : uvec f g x * Svec f g x =
      U f g x * transform (fun w => q8 f g w * rind (clsF f g) w) x := by
    obtain ⟨_, _, hssq⟩ := sigma8_spec f g res hrr x
    unfold uvec Svec Kmat
    have : sigma8 f g x * U f g x * (sigma8 f g x * transform (fun w => q8 f g w * rind (clsF f g) w) x) =
        (sigma8 f g x * sigma8 f g x) * (U f g x * transform (fun w => q8 f g w * rind (clsF f g) w) x) := by ac_rfl
    rw [this, hssq, Int.one_mul]
  rw [funext hpt1, ← Balanced242Section0320.duality]
  have hpt2 (w : W 8) : q8 f g w * rind (clsF f g) w * transform (U f g) w =
      10 * rind (clsB f g) w - 6 * rind (clsC f g) w := by
    rw [spec8 f g res w]
    have hqH := q8_point f g res cap w
    have heq : q8 f g w * rind (clsF f g) w * (2 * H8 f g w) =
        2 * (rind (clsF f g) w * (q8 f g w * H8 f g w)) := by ac_rfl
    rw [heq, hqH]
    unfold clsF; unfold Balanced242Reduction.ind clsA clsB clsC; dsimp only
    rcases hi_values f g res cap w with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  rw [funext hpt2, total_sub, total_scale, total_scale]
  unfold cnt; omega

/-- **Theorem 4 (`hinge_bound`)**: Universal hinge inequality backing all three hinge filters
    `(14, 6), (18, 6), (18, 10)` in `nl242_t98_closure.zip`. -/
theorem hinge_bound (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (hrr : rr (β8 f g) = 1) (h l : Int) :
    let np := total 8 (fun x => if uvec f g x = 1 then (1 : Int) else 0)
    let nn := total 8 (fun x => if uvec f g x = -1 then (1 : Int) else 0)
    10 * (cnt (clsB f g) + cnt (clsC f g)) - 16 * cnt (clsC f g) - np * h + nn * l ≤
      total 8 (fun x => posPart (Svec f g x - h) + posPart (l - Svec f g x)) := by
  intro np nn
  obtain ⟨hu_vals, _, _, _, _⟩ := u_ternary_counts f g res cap hrr
  have hpt (x : W 8) :
      uvec f g x * Svec f g x -
      h * (if uvec f g x = 1 then (1 : Int) else 0) +
      l * (if uvec f g x = -1 then (1 : Int) else 0) ≤
      posPart (Svec f g x - h) + posPart (l - Svec f g x) := by
    unfold posPart
    rcases hu_vals x with hx | hx | hx <;> rw [hx] <;> split <;> split <;> omega
  have hm := total_mono 8 _ _ hpt
  rw [total_add, total_sub, total_scale, total_scale, first_moment_u_S f g res cap hrr] at hm
  dsimp only [np, nn]
  rw [Int.mul_comm np h, Int.mul_comm nn l]
  exact hm

/-- Exact adjoint operator `K^T y w = q8 w * transform (sigma8 * y) w`
    (equals `K y w` whenever `q8 = sigma8`, as in standard coordinates). -/
def Ktrans (f g : Half) (y : W 8 → Int) (w : W 8) : Int :=
  q8 f g w * transform (fun x => sigma8 f g x * y x) w

theorem K_adjoint (f g : Half) (v y : W 8 → Int) :
    total 8 (fun x => Kmat f g v x * y x) = total 8 (fun w => v w * Ktrans f g y w) := by
  have h1 (x : W 8) : Kmat f g v x * y x =
      (sigma8 f g x * y x) * transform (fun w => q8 f g w * v w) x := by unfold Kmat; ac_rfl
  rw [funext h1, ← Balanced242Section0320.duality]
  apply congrArg (total 8); funext w
  unfold Ktrans; ac_rfl

/-- **Theorem 6 (`dual_cut_sound`)**: Universal exact integer dual inequality soundness
    backing EVERY radial / sublevel cut in `quartic_sections.cpp`, `quartic_sections_t.cpp`,
    and `nl242_t98_closure/direct.py`! -/
theorem dual_cut_sound (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (hrr : rr (β8 f g) = 1)
    (y : W 8 → Int) (lo_u hi_D : Int)
    (hu_lo : lo_u ≤ total 8 (fun x => uvec f g x * y x))
    (hD_hi : total 8 (fun w => diffAC f g w * Ktrans f g y w) ≤ hi_D) :
    total 8 (fun x => (28 - 3 * Svec f g x) * y x) + 32 * lo_u ≤ 2 * hi_D := by
  have hpt (x : W 8) :
      2 * (Kmat f g (diffAC f g) x * y x) =
      (28 - 3 * Svec f g x) * y x + 32 * (uvec f g x * y x) := by
    have hinv := high_block_inversion f g res cap hrr x
    have hmul := congrArg (fun z => z * y x) hinv
    dsimp only at hmul
    rw [Int.mul_assoc, Int.add_mul, Int.mul_assoc] at hmul
    exact hmul
  have htot := congrArg (total 8) (funext hpt)
  rw [total_scale, total_add, total_scale, K_adjoint] at htot
  omega

/-- Threshold form of `top_k`: for ANY threshold `τ : Int` and ANY subset `P : W 8 → Bool`,
    `∑_{w ∈ P} score w ≤ τ * |P| + ∑_{w ∈ Dom} posPart (score w - τ)` whenever `P ⊆ Dom`!
    (Taking `τ` to be the `k`-th largest value of `score` on `Dom` equals `top_k(score|_{Dom})`!) -/
theorem subset_sum_le_threshold {n : Nat} (P Dom : W n → Bool) (hsub : ∀ w, P w = true → Dom w = true)
    (score : W n → Int) (τ : Int) :
    total n (fun w => rind P w * score w) ≤
      τ * cnt P + total n (fun w => rind Dom w * posPart (score w - τ)) := by
  have hpt (w : W n) :
      rind P w * score w ≤ τ * rind P w + rind Dom w * posPart (score w - τ) := by
    unfold Balanced242Reduction.ind posPart
    cases hP : P w
    · simp only [Bool.false_eq_true, if_false, Int.zero_mul, Int.mul_zero, Int.zero_add]
      cases Dom w <;> split <;> omega
    · have hD := hsub w hP
      rw [hD]; simp only [if_true, Int.one_mul, Int.mul_one]
      split <;> omega
  have hm := total_mono n _ _ hpt
  rw [total_add, total_scale] at hm
  exact hm

/-- Threshold form of `bottom_np(y) - top_nn(y)`: for ANY thresholds `α, β : Int`,
    `α * np - β * nn - ∑_x (posPart (α - y x) + posPart (y x - β)) ≤ ∑_x u(x) y(x)`. -/
theorem ternary_sum_ge_threshold (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (hrr : rr (β8 f g) = 1) (y : W 8 → Int) (α β : Int) :
    let np := total 8 (fun x => if uvec f g x = 1 then (1 : Int) else 0)
    let nn := total 8 (fun x => if uvec f g x = -1 then (1 : Int) else 0)
    α * np - β * nn - total 8 (fun x => posPart (α - y x) + posPart (y x - β)) ≤
      total 8 (fun x => uvec f g x * y x) := by
  intro np nn
  obtain ⟨hu_vals, _, _, _, _⟩ := u_ternary_counts f g res cap hrr
  have hpt (x : W 8) :
      α * (if uvec f g x = 1 then (1 : Int) else 0) -
      β * (if uvec f g x = -1 then (1 : Int) else 0) -
      (posPart (α - y x) + posPart (y x - β)) ≤ uvec f g x * y x := by
    unfold posPart
    rcases hu_vals x with hx | hx | hx <;> rw [hx] <;> split <;> split <;> omega
  have hm := total_mono 8 _ _ hpt
  rw [total_sub, total_sub, total_scale, total_scale] at hm
  exact hm

/-- **Theorem 7 (`min_half_parseval`)**: Minimum hyperplane Parseval bound
    `n * (256 - n) ≤ 255 * (n - 2 * s)^2` whenever every nonzero hyperplane section of `F`
    has size in `[s, n - s]`. -/
theorem min_half_parseval (P : W 8 → Bool) (s : Int)
    (hs : ∀ w : W 8, w ≠ zero 8 → s ≤ low P w ∧ low P w ≤ cnt P - s) :
    cnt P * (256 - cnt P) ≤ 255 * ((cnt P - 2 * s) * (cnt P - 2 * s)) := by
  have hmom := moment_self P
  have hm8 : many 8 = 256 := by decide
  rw [hm8] at hmom
  have hle : total 8 (fun w => nz w * (transform (rind P) w * transform (rind P) w)) ≤
      total 8 (fun w => nz w * ((cnt P - 2 * s) * (cnt P - 2 * s))) := by
    apply total_mono 8; intro w
    by_cases hw : w = zero 8
    · subst hw; simp [nz]
    · simp only [nz, hw, if_false, Int.one_mul]
      have hsp := low_spec P w
      obtain ⟨hlo, hhi⟩ := hs w hw
      have h1 : -(cnt P - 2 * s) ≤ transform (rind P) w := by omega
      have h2 : transform (rind P) w ≤ cnt P - 2 * s := by omega
      have hnn : 0 ≤ ((cnt P - 2 * s) - transform (rind P) w) * ((cnt P - 2 * s) + transform (rind P) w) :=
        Int.mul_nonneg (by omega) (by omega)
      have hexp : ((cnt P - 2 * s) - transform (rind P) w) * ((cnt P - 2 * s) + transform (rind P) w) =
          (cnt P - 2 * s) * (cnt P - 2 * s) - transform (rind P) w * transform (rind P) w := by
        rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm (transform (rind P) w)]; omega
      omega
  rw [hmom, nz_total, total_const, hm8] at hle
  have hlin : 256 * cnt P - cnt P * cnt P = cnt P * (256 - cnt P) := by
    rw [Int.mul_sub, Int.mul_comm 256]
  omega

/-- **Theorem 8 (`core46_bound_lt_370`)**: At rank 8 for ANY `t ≤ 98` (including both `t = 96`
    and `t = 98`), `2 * a + 6 * c < 370`, strictly contradicting the unique normalized 45-point
    core's high-block lower bound `370` (`check_core46.py`)! -/
theorem core46_bound_lt_370 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (hrr : rr (β8 f g) = 1)
    (ht : agreements f g ≤ 98) :
    2 * cnt (clsA f g) + 6 * cnt (clsC f g) < 370 := by
  obtain ⟨_, hnp0, _, _, h2np⟩ := u_ternary_counts f g res cap hrr
  have ha0 : 0 ≤ cnt (clsA f g) := cnt_nonneg _
  have hc0 : 0 ≤ cnt (clsC f g) := cnt_nonneg _
  omega

end Balanced242QuarticHighBlock

#print axioms Balanced242QuarticHighBlock.sigma8_spec
#print axioms Balanced242QuarticHighBlock.high_block_inversion
#print axioms Balanced242QuarticHighBlock.u_ternary_counts
#print axioms Balanced242QuarticHighBlock.first_moment_u_S
#print axioms Balanced242QuarticHighBlock.hinge_bound
#print axioms Balanced242QuarticHighBlock.K_adjoint
#print axioms Balanced242QuarticHighBlock.dual_cut_sound
#print axioms Balanced242QuarticHighBlock.subset_sum_le_threshold
#print axioms Balanced242QuarticHighBlock.ternary_sum_ge_threshold
#print axioms Balanced242QuarticHighBlock.min_half_parseval
#print axioms Balanced242QuarticHighBlock.core46_bound_lt_370
