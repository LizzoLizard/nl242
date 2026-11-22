/-
  Balanced242T98R6Z144.lean — Unconditional zero-Mathlib Lean 4 formalization of
  `t98/T98_R6_Z144.md`: no balanced-242 low block V : W 8 → {-1, 0, 1} can have
  |supp V| = 98, Vhat(0) = 0, Vhat ∈ 4*{0, ±1, ±2, ±3}, and global rank-6 Z-pattern
  |Z| = 144 (Q_Z = Q6(c) ⊕ 0 on a 2-dim radical with Q6 hyperbolic bent on W 6).

  Zero Mathlib, zero `SectionEnum`, zero `sorry`, zero `native_decide`.
  Note: Step 3 replaces the informal shortcut in `T98_R6_Z144.md` line 18 with a
  completely airtight weight-partition argument using only the pairwise XORs
  `p_i ⊕ p_j = 1_{F_i ⊔ F_j}`, which are strictly quadratic (`Cube`), forcing
  one cell `x*` to hold all of `F6` (and hence `1_C = p_{x'}` to be `Cube`).
-/
import Balanced242Plateau
import Balanced242Blocks

namespace Balanced242T98R6Z144

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Plateau
open Balanced242Section0320 (chr_comm parseval)
open Balanced242Blocks (differences diff_transform_dvd)

/-! ## Part 1: Basic `W 6` / `W 8` Fourier, autocorrelation, and affine/quadratic weight lemmas -/

private theorem chr_zero_left {n : Nat} (x : W n) : chr (zero n) x = 1 := by
  simp [chr, dot_zero, sign]

private theorem chr_zero_right {n : Nat} (y : W n) : chr y (zero n) = 1 := by
  rw [chr_comm]; exact chr_zero_left y

private theorem chr_sq {n : Nat} (y x : W n) : chr y x * chr y x = 1 := by
  unfold chr; exact sign_sq _

private theorem total_chr_eq {n : Nat} (y : W n) :
    total n (fun x => chr y x) = if y = zero n then many n else 0 := by
  have h := orthogonal n y (zero n)
  have hpt (c : W n) : chr c y * chr c (zero n) = chr y c := by
    rw [chr_zero_right, Int.mul_one, chr_comm]
  rw [funext hpt] at h
  rw [h]; unfold hits
  if hy : y = zero n then simp [hy]
  else simp [hy]

private theorem transform_inv_eq {n : Nat} (f : W n → Int) (x : W n) :
    transform (transform f) x = many n * f x := by
  show total n (fun y => transform f y * chr x y) = many n * f x
  have hpt (y : W n) : transform f y * chr x y = transform f y * chr y x := by rw [chr_comm]
  rw [funext hpt]
  exact inversion f x

/-- Wiener–Khinchin identity: `transform (fun c => (transform f c)^2) y = 2^n * ∑_u f(u) f(u ⊕ y)`. -/
private theorem wiener_khinchin {n : Nat} (f : W n → Int) (y : W n) :
    transform (fun c => transform f c * transform f c) y =
      many n * total n (fun u => f u * f (add n u y)) := by
  unfold transform
  have h1 : total n (fun c => (total n (fun u => f u * chr c u) * total n (fun v => f v * chr c v)) * chr y c) =
      total n (fun u => f u * total n (fun v => f v * total n (fun c => chr (add n (add n u v) y) c))) := by
    have step1 : total n (fun c => (total n (fun u => f u * chr c u) * total n (fun v => f v * chr c v)) * chr y c) =
        total n (fun c => total n (fun u => f u * total n (fun v => f v * chr (add n (add n u v) y) c))) := by
      apply congrArg (total n); funext c
      have hmul : (total n (fun u => f u * chr c u) * total n (fun v => f v * chr c v)) * chr y c =
          total n (fun u => (f u * chr c u) * (total n (fun v => f v * chr c v) * chr y c)) := by
        rw [Int.mul_assoc, Int.mul_comm (total n (fun u => f u * chr c u)), ← total_scale]
        apply congrArg (total n); funext u; rw [Int.mul_comm]
      rw [hmul]
      apply congrArg (total n); funext u
      have hinner : (f u * chr c u) * (total n (fun v => f v * chr c v) * chr y c) =
          f u * total n (fun v => f v * chr (add n (add n u v) y) c) := by
        have hstep : (total n (fun v => f v * chr c v)) * chr y c = total n (fun v => f v * (chr c v * chr y c)) := by
          rw [Int.mul_comm, ← total_scale]; apply congrArg (total n); funext v; ac_rfl
        rw [hstep, Int.mul_assoc, ← total_scale]
        apply congrArg (Int.mul (f u)); apply congrArg (total n); funext v
        have hc : chr (add n (add n u v) y) c = chr c u * (chr c v * chr y c) := by
          rw [chr_comm, chr_add, chr_add, chr_comm y c]; ac_rfl
        rw [hc]; ac_rfl
      exact hinner
    rw [step1, swap]
    apply congrArg (total n); funext u
    rw [total_scale, swap]
    apply congrArg (Int.mul (f u))
    apply congrArg (total n); funext v
    rw [total_scale]
  rw [h1]
  have h2 (u : W n) : total n (fun v => f v * total n (fun c => chr (add n (add n u v) y) c)) =
      many n * f (add n u y) := by
    have hpt (v : W n) : f v * total n (fun c => chr (add n (add n u v) y) c) =
        many n * (f v * hits (add n u y) v) := by
      rw [total_chr_eq]
      if hv : add n u y = v then
        subst hv
        have hz : add n (add n u (add n u y)) y = zero n := by
          rw [← add_assoc', add_self, add_zero_left, add_self]
        simp [hz, hits, Int.mul_comm]
      else
        have hnz : add n (add n u v) y ≠ zero n := by
          intro hz
          apply hv
          have heq1 : add n (add n u v) (add n y y) = add n (zero n) y := by
            rw [← add_assoc', hz]
          rw [add_self, add_zero_right, add_zero_left] at heq1
          have heq2 : add n u (add n u v) = add n u y := congrArg (add n u) heq1
          rw [← add_assoc', add_self, add_zero_left] at heq2
          exact heq2.symm
        simp [hnz, hv, hits]
    rw [funext hpt, total_scale]
    apply congrArg (Int.mul (many n))
    have hdiag : total n (fun v => f v * hits (add n u y) v) = f (add n u y) := by
      have hpt2 (v : W n) : f v * hits (add n u y) v = f (add n u y) * hits (add n u y) v := by
        unfold hits; if hv : add n u y = v then subst hv; rfl else simp [hv]
      rw [funext hpt2, total_scale, diagonal, Int.mul_one]
    exact hdiag
  have h3 : total n (fun u => f u * total n (fun v => f v * total n (fun c => chr (add n (add n u v) y) c))) =
      total n (fun u => many n * (f u * f (add n u y))) := by
    apply congrArg (total n); funext u; rw [h2 u]; ac_rfl
  rw [h3, total_scale]

/-- Helper: sum of a symmetric-under-`add n · y` function (`y ≠ 0`) is even. -/
private theorem total_symm_even {n : Nat} (g : W n → Int) (y : W n) (hy : y ≠ zero n)
    (hsym : ∀ u, g (add n u y) = g u) : total n g % 2 = 0 := by
  revert y hy g hsym
  induction n with
  | zero => intro g y hy; cases y; exact False.elim (hy rfl)
  | succ m ih =>
    intro g y hy hsym
    rcases y with ⟨yb, yr⟩
    cases yb
    · have hyr : yr ≠ zero m := fun h => hy (by rw [h]; rfl)
      show (total m (fun u => g (false, u)) + total m (fun u => g (true, u))) % 2 = 0
      have h0 := ih (fun u => g (false, u)) yr hyr (fun u => hsym (false, u))
      have h1 := ih (fun u => g (true, u)) yr hyr (fun u => hsym (true, u))
      omega
    · show (total m (fun u => g (false, u)) + total m (fun u => g (true, u))) % 2 = 0
      have heq : total m (fun u => g (true, u)) = total m (fun u => g (false, u)) := by
        rw [← sum_shift m yr (fun u => g (true, u))]
        apply congrArg (total m); funext u
        have h := hsym (false, u)
        rw [add_comm m yr u]
        simpa [add] using h
      rw [heq]; omega

/-- For any `f : W n → Int` and `y ≠ 0`, autocorrelation `∑_u f u * f (u ⊕ y)` is even. -/
private theorem auto_even {n : Nat} (f : W n → Int) (y : W n) (hy : y ≠ zero n) :
    total n (fun u => f u * f (add n u y)) % 2 = 0 := by
  apply total_symm_even (fun u => f u * f (add n u y)) y hy
  intro u
  have h1 : add n (add n u y) y = u := by rw [add_assoc', add_self, add_zero_right]
  rw [h1, Int.mul_comm]

/-- For any `±1`-valued `f : W n → Int` (`n ≥ 2`) and `y ≠ 0`, autocorrelation is `0 mod 4`. -/
private theorem auto_pm1_mod4 (f : W 6 → Int) (hf : ∀ u, f u = 1 ∨ f u = -1)
    (y : W 6) (hy : y ≠ zero 6) :
    total 6 (fun u => f u * f (add 6 u y)) % 4 = 0 := by
  let d (u : W 6) : Int := if f u = f (add 6 u y) then 0 else 1
  have hd_sym (u : W 6) : d (add 6 u y) = d u := by
    have h1 : add 6 (add 6 u y) y = u := by rw [add_assoc', add_self, add_zero_right]
    dsimp only [d]; rw [h1]
    if heq : f u = f (add 6 u y) then simp [heq]
    else simp [heq, Ne.symm heq]
  have hd_even : total 6 d % 2 = 0 := total_symm_even d y hy hd_sym
  have hpt (u : W 6) : f u * f (add 6 u y) = 1 - 2 * d u := by
    dsimp only [d]
    rcases hf u with h1 | h1 <;> rcases hf (add 6 u y) with h2 | h2 <;> simp [h1, h2]
  rw [funext hpt, total_sub, total_const, total_scale]
  have h64 : many 6 = 64 := by decide
  rw [h64]; omega

/-- Constructive (zero `Classical.choice`) `RM(2, 6)` weight theorem via `Balanced242Plateau.spec_sq`. -/
private theorem divisors64_mem : ∀ r : Nat, r < 65 → 64 % r = 0 →
    r ∈ [0, 1, 2, 4, 8, 16, 32, 64] := by decide

private theorem rm2_6_weight (β : W 6 → Bool) (hc : Cube β) :
    let w := total 6 (fun c => ind (β c))
    w = 0 ∨ w = 16 ∨ w = 24 ∨ w = 28 ∨ w = 32 ∨ w = 36 ∨ w = 40 ∨ w = 48 ∨ w = 64 := by
  intro w
  let S : W 6 → Int := fun y => total 6 (fun d => ind (rad β d) * sign (phi β y d))
  let r := total 6 (fun d => ind (rad β d))
  let c := total 6 (fun y => if S y = r then (1 : Int) else 0)
  have hS (y : W 6) : S y = r * (if S y = r then 1 else 0) := by
    rcases signed_radical β y with h | h
    · change S y = 0 at h
      if e : S y = r then rw [if_pos e, Int.mul_one]; exact e
      else rw [if_neg e, Int.mul_zero]; exact h
    · change S y = r at h; rw [if_pos h, Int.mul_one]; exact h
  have hsum : total 6 S = r * c := by
    rw [← total_scale]; apply congrArg (total 6); funext y; exact hS y
  have par := Balanced242Section0320.parseval (fun a => sign (β a))
  simp only [sign_sq, total_const, Int.mul_one, spec_sq β hc, total_scale] at par
  change many 6 * total 6 S = many 6 * many 6 at par
  rw [hsum] at par
  have h64 : many 6 = 64 := by decide
  have hrc : r * c = 64 := by rw [h64] at par; omega
  have r0 : 0 ≤ r := total_nonneg' _ (fun d => ind_nonneg _)
  have c0 : 0 ≤ c := total_nonneg' _ (fun y => by split <;> decide)
  have hspec0 := spec_sq β hc (zero 6)
  rw [h64] at hspec0
  have htr0 : transform (fun a => sign (β a)) (zero 6) = 64 - 2 * w := by
    unfold transform
    have hpt (a : W 6) : sign (β a) * chr (zero 6) a = 1 - 2 * ind (β a) := by
      rw [chr_zero_left, Int.mul_one]; cases β a <;> decide
    rw [funext hpt, total_sub, total_const, total_scale, h64]; omega
  rw [htr0] at hspec0
  rcases signed_radical β (zero 6) with h0 | hr_eq
  · change S (zero 6) = 0 at h0
    rw [show total 6 (fun d => ind (rad β d) * sign (phi β (zero 6) d)) = 0 from h0, Int.mul_zero] at hspec0
    have hz : 64 - 2 * w = 0 := by
      rcases Int.mul_eq_zero.mp hspec0 with h | h <;> exact h
    omega
  · change S (zero 6) = r at hr_eq
    rw [show total 6 (fun d => ind (rad β d) * sign (phi β (zero 6) d)) = r from hr_eq] at hspec0
    have hr_pos : 0 < r := by
      if hp : 0 < r then exact hp
      else exfalso; have : r = 0 := by omega
           rw [this, Int.zero_mul] at hrc; omega
    have hr_le : r ≤ 64 := by
      have hc_pos : 1 ≤ c := by
        if hcp : 1 ≤ c then exact hcp
        else exfalso; have : c = 0 := by omega
             rw [this, Int.mul_zero] at hrc; omega
      have := Int.mul_le_mul_of_nonneg_left hc_pos (by omega : 0 ≤ r); omega
    have hr_nat : r.toNat < 65 ∧ 64 % r.toNat = 0 := by
      refine ⟨by omega, ?_⟩
      have hmul : r.toNat * c.toNat = 64 := by
        have h1 : (r.toNat : Int) = r := by omega
        have h2 : (c.toNat : Int) = c := by omega
        have : ((r.toNat * c.toNat : Nat) : Int) = 64 := by rw [Int.ofNat_mul, h1, h2]; exact hrc
        omega
      rw [← hmul]; exact Nat.mul_mod_right _ _
    have hmem := divisors64_mem r.toNat hr_nat.1 hr_nat.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    have hr_cases : r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 8 ∨ r = 16 ∨ r = 32 ∨ r = 64 := by omega
    have hsq_non (z a : Int) (h : z * z = a) (hodd : a = 128 ∨ a = 512 ∨ a = 2048) : False := by
      have habs : z.natAbs * z.natAbs = a.toNat := by
        have h1 := congrArg Int.natAbs h
        rw [Int.natAbs_mul] at h1; omega
      have hle : z.natAbs < 65 := by
        if hlt : z.natAbs < 65 then exact hlt
        else exfalso
             have hge : 65 * 65 ≤ z.natAbs * z.natAbs := Nat.mul_le_mul (by omega) (by omega)
             omega
      generalize z.natAbs = M at habs hle
      rcases hodd with rfl | rfl | rfl
      · exact absurd habs (by revert M; decide)
      · exact absurd habs (by revert M; decide)
      · exact absurd habs (by revert M; decide)
    rcases hr_cases with hr | hr | hr | hr | hr | hr | hr
    · rw [hr] at hspec0; have := sq_cases (64 - 2 * w) 8 (by omega); omega
    · rw [hr] at hspec0; exact False.elim (hsq_non _ 128 hspec0 (Or.inl rfl))
    · rw [hr] at hspec0; have := sq_cases (64 - 2 * w) 16 (by omega); omega
    · rw [hr] at hspec0; exact False.elim (hsq_non _ 512 hspec0 (Or.inr (Or.inl rfl)))
    · rw [hr] at hspec0; have := sq_cases (64 - 2 * w) 32 (by omega); omega
    · rw [hr] at hspec0; exact False.elim (hsq_non _ 2048 hspec0 (Or.inr (Or.inr rfl)))
    · rw [hr] at hspec0; have := sq_cases (64 - 2 * w) 64 (by omega); omega

/-- An affine Boolean function on `W 6` has weight in `{0, 32, 64}`. -/
private theorem affine_weight_6 (β : W 6 → Bool)
    (haff : ∀ c a b : W 6, xor (xor (β c) (β (add 6 c a))) (xor (β (add 6 c b)) (β (add 6 (add 6 c a) b))) = false) :
    let w := total 6 (fun c => ind (β c))
    w = 0 ∨ w = 32 ∨ w = 64 := by
  intro w
  let g (u : W 6) : Bool := xor (β u) (β (zero 6))
  have hg_add (a b : W 6) : g (add 6 a b) = xor (g a) (g b) := by
    have h := haff (zero 6) a b
    rw [add_zero_left, add_zero_left] at h
    dsimp only [g]
    cases h0 : β (zero 6) <;> cases h1 : β a <;> cases h2 : β b <;> cases h3 : β (add 6 a b) <;>
      simp [h0, h1, h2, h3] at h ⊢
  cases hall : (worlds 6).all (fun u => !g u)
  · obtain ⟨a, _, ha_neg⟩ := all_false_exists (fun u => !g u) (worlds 6) hall
    have ha : g a = true := by cases hga : g a <;> simp [hga] at ha_neg ⊢
    have hflip (u : W 6) : β (add 6 u a) = !β u := by
      have h1 := hg_add u a
      rw [ha] at h1
      dsimp only [g] at h1
      cases h0 : β (zero 6) <;> cases h2 : β u <;> cases h3 : β (add 6 u a) <;> simp [h0, h2, h3] at h1 ⊢
    have hsum : w + w = 64 := by
      have hshift : total 6 (fun u => ind (β (add 6 u a))) = w := by
        have := sum_shift 6 a (fun u => ind (β u))
        have hcomm : (fun u => ind (β (add 6 u a))) = fun u => ind (β (add 6 a u)) :=
          funext (fun u => by rw [add_comm])
        rw [hcomm]; exact this
      have hpt (u : W 6) : ind (β u) + ind (β (add 6 u a)) = 1 := by
        rw [hflip u]; cases β u <;> decide
      have htot := congrArg (total 6) (funext hpt)
      rw [total_add, hshift, total_const, Int.mul_one] at htot
      have h64 : many 6 = 64 := by decide
      rw [h64] at htot; exact htot
    right; left; omega
  · rw [List.all_eq_true] at hall
    have hconst (u : W 6) : β u = β (zero 6) := by
      have hu := hall u (all_worlds 6 u)
      dsimp only [g] at hu
      cases h0 : β (zero 6) <;> cases h1 : β u <;> simp [h0, h1] at hu ⊢
    have hw : w = total 6 (fun _ => ind (β (zero 6))) := by
      apply congrArg (total 6); funext u; rw [hconst u]
    rw [total_const] at hw
    have h64 : many 6 = 64 := by decide
    rw [h64] at hw
    cases h0 : β (zero 6)
    · left; rw [h0] at hw; simpa [ind] using hw
    · right; right; rw [h0] at hw; simpa [ind] using hw

private theorem xor2_distr (a0 a1 b0 b1 : Bool) :
    xor (xor a0 b0) (xor a1 b1) = xor (xor a0 a1) (xor b0 b1) := by
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> rfl

private theorem xor4_distr (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) :
    xor (xor (xor a0 b0) (xor a1 b1)) (xor (xor a2 b2) (xor a3 b3)) =
    xor (xor (xor a0 a1) (xor a2 a3)) (xor (xor b0 b1) (xor b2 b3)) := by
  rw [xor2_distr a0 a1 b0 b1, xor2_distr a2 a3 b2 b3, xor2_distr]

private theorem xor8_distr (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    xor (xor (xor (xor a0 b0) (xor a1 b1)) (xor (xor a2 b2) (xor a3 b3)))
        (xor (xor (xor a4 b4) (xor a5 b5)) (xor (xor a6 b6) (xor a7 b7))) =
    xor (xor (xor (xor a0 a1) (xor a2 a3)) (xor (xor a4 a5) (xor a6 a7)))
        (xor (xor (xor b0 b1) (xor b2 b3)) (xor (xor b4 b5) (xor b6 b7))) := by
  rw [xor4_distr a0 a1 a2 a3 b0 b1 b2 b3, xor4_distr a4 a5 a6 a7 b4 b5 b6 b7, xor2_distr]

/-- `Cube` is closed under pointwise XOR. -/
private theorem cube_xor {n : Nat} (f g : W n → Bool) (hf : Cube f) (hg : Cube g) :
    Cube (fun a => xor (f a) (g a)) := by
  intro u v w a
  have h1 := hf u v w a
  have h2 := hg u v w a
  dsimp only
  rw [xor8_distr, h1, h2]; rfl

private theorem parity_sub (x y : Int) :
    decide ((x - y) % 2 = 1) = xor (decide (x % 2 = 1)) (decide (y % 2 = 1)) := by
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have h : (x - y) % 2 = 0 := by omega
    simp [hx, hy, h]
  · have h : (x - y) % 2 = 1 := by omega
    simp [hx, hy, h]
  · have h : (x - y) % 2 = 1 := by omega
    simp [hx, hy, h]
  · have h : (x - y) % 2 = 0 := by omega
    simp [hx, hy, h]

/-- If `z = transform v` on `W 6` is divisible by `4` everywhere, then `p c := (z c / 4) % 2 != 0` is `Cube`. -/
private theorem cube_of_div4_transform (v : W 6 → Int) (h4 : ∀ c, transform v c % 4 = 0) :
    Cube (fun c => decide (transform v c / 4 % 2 = 1)) := by
  intro u v' w a
  have h8 := diff_transform_dvd [u, v', w] v a
  simp only [List.length_cons, List.length_nil] at h8
  have hdiv : (8 : Int) ∣ differences [u, v', w] (transform v) a := by simpa using h8
  simp only [differences] at hdiv
  obtain ⟨q, hq⟩ := hdiv
  have h0 := h4 (add 6 u (add 6 v' (add 6 w a)))
  have h1 := h4 (add 6 v' (add 6 w a))
  have h2 := h4 (add 6 u (add 6 w a))
  have h3 := h4 (add 6 w a)
  have h4' := h4 (add 6 u (add 6 v' a))
  have h5 := h4 (add 6 v' a)
  have h6 := h4 (add 6 u a)
  have h7 := h4 a
  have heven : (((transform v (add 6 u (add 6 v' (add 6 w a))) / 4 - transform v (add 6 v' (add 6 w a)) / 4) -
      (transform v (add 6 u (add 6 w a)) / 4 - transform v (add 6 w a) / 4)) -
      ((transform v (add 6 u (add 6 v' a)) / 4 - transform v (add 6 v' a) / 4) -
      (transform v (add 6 u a) / 4 - transform v a / 4))) % 2 = 0 := by
    omega
  have hdec : decide (((((transform v (add 6 u (add 6 v' (add 6 w a))) / 4 - transform v (add 6 v' (add 6 w a)) / 4) -
      (transform v (add 6 u (add 6 w a)) / 4 - transform v (add 6 w a) / 4)) -
      ((transform v (add 6 u (add 6 v' a)) / 4 - transform v (add 6 v' a) / 4) -
      (transform v (add 6 u a) / 4 - transform v a / 4))) % 2) = 1) = false := by
    rw [heven]; decide
  rw [parity_sub, parity_sub, parity_sub, parity_sub, parity_sub, parity_sub, parity_sub] at hdec
  exact hdec

/-- If `z = transform v` on `W 6` is even everywhere, then `β c := (z c / 2) % 2 = 1` is affine. -/
private theorem affine_of_div2_transform (v : W 6 → Int) (h2 : ∀ c, transform v c % 2 = 0) :
    ∀ c a b : W 6,
      let β (u : W 6) := decide (transform v u / 2 % 2 = 1)
      xor (xor (β c) (β (add 6 c a))) (xor (β (add 6 c b)) (β (add 6 (add 6 c a) b))) = false := by
  intro c a b β
  have h4 := diff_transform_dvd [a, b] v c
  simp only [List.length_cons, List.length_nil] at h4
  have hdiv : (4 : Int) ∣ differences [a, b] (transform v) c := by simpa using h4
  simp only [differences] at hdiv
  obtain ⟨q, hq⟩ := hdiv
  have e0 := h2 (add 6 a (add 6 b c))
  have e1 := h2 (add 6 b c)
  have e2 := h2 (add 6 a c)
  have e3 := h2 c
  have heven : ((transform v (add 6 a (add 6 b c)) / 2 - transform v (add 6 b c) / 2) -
      (transform v (add 6 a c) / 2 - transform v c / 2)) % 2 = 0 := by omega
  have hdec : decide ((((transform v (add 6 a (add 6 b c)) / 2 - transform v (add 6 b c) / 2) -
      (transform v (add 6 a c) / 2 - transform v c / 2)) % 2) = 1) = false := by
    rw [heven]; decide
  rw [parity_sub, parity_sub, parity_sub] at hdec
  have k1 : add 6 a (add 6 b c) = add 6 (add 6 c a) b := by
    rw [add_comm 6 b c, add_comm 6 a (add 6 c b), add_assoc', add_comm 6 b a, ← add_assoc']
  have k2 : add 6 b c = add 6 c b := add_comm 6 b c
  have k3 : add 6 a c = add 6 c a := add_comm 6 a c
  rw [k1, k2, k3] at hdec
  dsimp only [β]
  generalize decide (transform v c / 2 % 2 = 1) = x0 at hdec ⊢
  generalize decide (transform v (add 6 c a) / 2 % 2 = 1) = x1 at hdec ⊢
  generalize decide (transform v (add 6 c b) / 2 % 2 = 1) = x2 at hdec ⊢
  generalize decide (transform v (add 6 (add 6 c a) b) / 2 % 2 = 1) = x3 at hdec ⊢
  cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;> simp at hdec ⊢

/-- Nonnegative function with `(∑ D)^2 = ∑ D^2` is supported on at most one point. -/
private theorem support_singleton_of_sum_sq_eq {n : Nat} (D : W n → Int)
    (hnn : ∀ x, 0 ≤ D x) (x0 : W n) (hpos : 0 < D x0)
    (hsq : total n (fun x => D x * D x) = total n D * total n D) :
    ∀ x, x ≠ x0 → D x = 0 := by
  have hS_ge : D x0 ≤ total n D := by
    have hpt (x : W n) : D x0 * hits x0 x ≤ D x := by
      unfold hits
      if hx : x0 = x then subst hx; simp
      else simp [hx, hnn x]
    have hm := total_mono n _ _ hpt
    rw [total_scale, diagonal, Int.mul_one] at hm; exact hm
  -- For any `x1 ≠ x0`, `D x0 + D x1 ≤ total n D`, and `∑ D^2 ≤ total D * max?`
  -- Even simpler: `total D * total D - total (D^2) = ∑_x D x * (total D - D x) ≥ 0`!
  have hdiff : total n (fun x => D x * (total n D - D x)) = 0 := by
    have hpt (x : W n) : D x * (total n D - D x) = total n D * D x - D x * D x := by
      rw [Int.mul_sub, Int.mul_comm]
    rw [funext hpt, total_sub, total_scale, hsq]; omega
  have hterm_nn (x : W n) : 0 ≤ D x * (total n D - D x) := by
    have hle : D x ≤ total n D := by
      have hpt (y : W n) : D x * hits x y ≤ D y := by
        unfold hits; if hy : x = y then subst hy; simp else simp [hy, hnn y]
      have hm := total_mono n _ _ hpt
      rw [total_scale, diagonal, Int.mul_one] at hm; exact hm
    exact Int.mul_nonneg (hnn x) (by omega)
  have hterm_zero (x : W n) : D x * (total n D - D x) = 0 := by
    have hle : D x * (total n D - D x) ≤ total n (fun y => D y * (total n D - D y)) := by
      have hpt (y : W n) : (D x * (total n D - D x)) * hits x y ≤ D y * (total n D - D y) := by
        unfold hits; if hy : x = y then subst hy; simp else simp [hy, hterm_nn y]
      have hm := total_mono n _ _ hpt
      rw [total_scale, diagonal, Int.mul_one] at hm; exact hm
    have h0 := hterm_nn x
    omega
  have hx0_eq : D x0 = total n D := by
    rcases Int.mul_eq_zero.mp (hterm_zero x0) with h | h <;> omega
  intro x hx
  have hle2 : D x0 + D x ≤ total n D := by
    have hpt (y : W n) : D x0 * hits x0 y + D x * hits x y ≤ D y := by
      unfold hits
      if h1 : x0 = y then subst h1; have hne : x ≠ x0 := hx; simp [hne]
      else if h2 : x = y then subst h2; simp [h1]
      else simp [h1, h2, hnn y]
    have hm := total_mono n _ _ hpt
    rw [total_add, total_scale, total_scale, diagonal, diagonal, Int.mul_one, Int.mul_one] at hm
    exact hm
  have := hnn x; omega

private theorem walsh2_classify (x0 x1 x2 x3 m : Int) (hm : 0 ≤ m)
    (e00 : x0 + x1 + x2 + x3 = 2 * m ∨ x0 + x1 + x2 + x3 = -(2 * m))
    (e01 : x0 + -1 * x1 + x2 + -1 * x3 = 2 * m ∨ x0 + -1 * x1 + x2 + -1 * x3 = -(2 * m))
    (e10 : x0 + x1 + -1 * x2 + -1 * x3 = 2 * m ∨ x0 + x1 + -1 * x2 + -1 * x3 = -(2 * m))
    (e11 : x0 + -1 * x1 + -1 * x2 + x3 = 2 * m ∨ x0 + -1 * x1 + -1 * x2 + x3 = -(2 * m)) :
    (x0.natAbs = m.toNat ∧ x1.natAbs = m.toNat ∧ x2.natAbs = m.toNat ∧ x3.natAbs = m.toNat) ∨
    (x0.natAbs = (2 * m).toNat ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0) ∨
    (x0 = 0 ∧ x1.natAbs = (2 * m).toNat ∧ x2 = 0 ∧ x3 = 0) ∨
    (x0 = 0 ∧ x1 = 0 ∧ x2.natAbs = (2 * m).toNat ∧ x3 = 0) ∨
    (x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3.natAbs = (2 * m).toNat) := by
  rcases e00 with a | a <;> rcases e01 with b | b <;> rcases e10 with d | d <;> rcases e11 with e | e
  · right; left; omega
  · left; omega
  · left; omega
  · right; right; right; left; omega
  · left; omega
  · right; right; left; omega
  · right; right; right; right; omega
  · left; omega
  · left; omega
  · right; right; right; right; omega
  · right; right; left; omega
  · left; omega
  · right; right; right; left; omega
  · left; omega
  · left; omega
  · right; left; omega

/-! ## Part 2: Main unconditional theorem `no_t98_r6_z144` -/

set_option maxHeartbeats 600000 in
/-- Unconditional impossibility of `t = 98`, global rank 6, `|Z| = 144` (`t98/T98_R6_Z144.md`). -/
theorem no_t98_r6_z144
    (V : W 8 → Int)
    (hV_val : ∀ u, V u = -1 ∨ V u = 0 ∨ V u = 1)
    (hV_supp : total 8 (fun u => V u * V u) = 98)
    (hV_bal : transform V (zero 8) = 0)
    (hV_spec : ∀ u, transform V u % 4 = 0 ∧ (transform V u).natAbs ≤ 12)
    (Q6 : W 6 → Bool)
    (hQ6_wt : total 6 (fun c => ind (Q6 c)) = 28)
    (hQ6_bent : ∀ y, transform (fun c => sign (Q6 c)) y = 8 ∨
                     transform (fun c => sign (Q6 c)) y = -8)
    (hZ_pat : ∀ b0 b1 (c : W 6),
      (Q6 c = false → transform V (b0, (b1, c)) % 8 = 0) ∧
      (Q6 c = true  → transform V (b0, (b1, c)) % 8 = 4)) :
    False := by
  -- 4 cells v00, v01, v10, v11 on W 6 and their Walsh transforms z00, z01, z10, z11
  let v00 (y : W 6) := V (false, (false, y))
  let v01 (y : W 6) := V (false, (true,  y))
  let v10 (y : W 6) := V (true,  (false, y))
  let v11 (y : W 6) := V (true,  (true,  y))
  let z00 := transform v00
  let z01 := transform v01
  let z10 := transform v10
  let z11 := transform v11
  -- Express `transform V (b0, (b1, c))` directly in terms of `z00..z11`
  have htrV (b0 b1 : Bool) (c : W 6) :
      transform V (b0, (b1, c)) =
        z00 c + sign b1 * z01 c + sign b0 * z10 c + sign b0 * sign b1 * z11 c := by
    unfold transform
    show total 6 (fun y => v00 y * @chr 8 (b0, (b1, c)) (false, (false, y))) +
         total 6 (fun y => v01 y * @chr 8 (b0, (b1, c)) (false, (true,  y))) +
        (total 6 (fun y => v10 y * @chr 8 (b0, (b1, c)) (true,  (false, y))) +
         total 6 (fun y => v11 y * @chr 8 (b0, (b1, c)) (true,  (true,  y)))) = _
    have c00 (y : W 6) : @chr 8 (b0, (b1, c)) (false, (false, y)) = chr c y := by
      show sign ((b0 && false) ^^ ((b1 && false) ^^ dot 6 c y)) = sign (dot 6 c y)
      generalize dot 6 c y = d; cases b0 <;> cases b1 <;> cases d <;> decide
    have c01 (y : W 6) : @chr 8 (b0, (b1, c)) (false, (true, y)) = sign b1 * chr c y := by
      show sign ((b0 && false) ^^ ((b1 && true) ^^ dot 6 c y)) = sign b1 * sign (dot 6 c y)
      generalize dot 6 c y = d; cases b0 <;> cases b1 <;> cases d <;> decide
    have c10 (y : W 6) : @chr 8 (b0, (b1, c)) (true, (false, y)) = sign b0 * chr c y := by
      show sign ((b0 && true) ^^ ((b1 && false) ^^ dot 6 c y)) = sign b0 * sign (dot 6 c y)
      generalize dot 6 c y = d; cases b0 <;> cases b1 <;> cases d <;> decide
    have c11 (y : W 6) : @chr 8 (b0, (b1, c)) (true, (true, y)) = sign b0 * sign b1 * chr c y := by
      show sign ((b0 && true) ^^ ((b1 && true) ^^ dot 6 c y)) = sign b0 * sign b1 * sign (dot 6 c y)
      generalize dot 6 c y = d; cases b0 <;> cases b1 <;> cases d <;> decide
    have s00 : total 6 (fun y => v00 y * @chr 8 (b0, (b1, c)) (false, (false, y))) = z00 c := by
      dsimp only [z00, transform]; apply congrArg (total 6); funext y; rw [c00 y]
    have s01 : total 6 (fun y => v01 y * @chr 8 (b0, (b1, c)) (false, (true, y))) = sign b1 * z01 c := by
      dsimp only [z01, transform]; rw [← total_scale]; apply congrArg (total 6); funext y; rw [c01 y]; ac_rfl
    have s10 : total 6 (fun y => v10 y * @chr 8 (b0, (b1, c)) (true, (false, y))) = sign b0 * z10 c := by
      dsimp only [z10, transform]; rw [← total_scale]; apply congrArg (total 6); funext y; rw [c10 y]; ac_rfl
    have s11 : total 6 (fun y => v11 y * @chr 8 (b0, (b1, c)) (true, (true, y))) = sign b0 * sign b1 * z11 c := by
      dsimp only [z11, transform]; rw [← total_scale]; apply congrArg (total 6); funext y; rw [c11 y]; ac_rfl
    rw [s00, s01, s10, s11]; omega
  have hsf : sign false = 1 := rfl
  have hst : sign true = -1 := rfl
  -- 2x2 Walsh Parseval on the 4 fibers
  have hfiber_sq (c : W 6) :
      transform V (false, (false, c)) * transform V (false, (false, c)) +
      transform V (false, (true,  c)) * transform V (false, (true,  c)) +
      transform V (true,  (false, c)) * transform V (true,  (false, c)) +
      transform V (true,  (true,  c)) * transform V (true,  (true,  c)) =
      4 * (z00 c * z00 c + z01 c * z01 c + z10 c * z10 c + z11 c * z11 c) := by
    rw [htrV false false c, htrV false true c, htrV true false c, htrV true true c]
    simp only [hsf, hst, Int.one_mul, Int.neg_mul, Int.mul_neg, Int.neg_neg]
    generalize z00 c = a; generalize z01 c = b; generalize z10 c = d; generalize z11 c = e
    simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_neg]
    have hab : b * a = a * b := Int.mul_comm _ _
    have had : d * a = a * d := Int.mul_comm _ _
    have hae : e * a = a * e := Int.mul_comm _ _
    have hbd : d * b = b * d := Int.mul_comm _ _
    have hbe : e * b = b * e := Int.mul_comm _ _
    have hde : e * d = d * e := Int.mul_comm _ _
    rw [hab, had, hae, hbd, hbe, hde]; omega
  -- Exact spectrum classification on Z6 and F6
  have hZ_vals (b0 b1 : Bool) (c : W 6) (hQ : Q6 c = false) :
      transform V (b0, (b1, c)) = 0 ∨ transform V (b0, (b1, c)) = 8 ∨ transform V (b0, (b1, c)) = -8 := by
    have h1 := hV_spec (b0, (b1, c))
    have h2 := (hZ_pat b0 b1 c).1 hQ
    omega
  have hF_vals (b0 b1 : Bool) (c : W 6) (hQ : Q6 c = true) :
      transform V (b0, (b1, c)) = 4 ∨ transform V (b0, (b1, c)) = -4 ∨
      transform V (b0, (b1, c)) = 12 ∨ transform V (b0, (b1, c)) = -12 := by
    have h1 := hV_spec (b0, (b1, c))
    have h2 := (hZ_pat b0 b1 c).2 hQ
    omega
  -- Define defect `D(c) = if Q6 c then 2 * k_c else d_c`
  let cnt0 (c : W 6) : Int :=
    (if transform V (false, (false, c)) = 0 then 1 else 0) +
    (if transform V (false, (true,  c)) = 0 then 1 else 0) +
    (if transform V (true,  (false, c)) = 0 then 1 else 0) +
    (if transform V (true,  (true,  c)) = 0 then 1 else 0)
  let cnt4 (c : W 6) : Int :=
    (if (transform V (false, (false, c))).natAbs = 4 then 1 else 0) +
    (if (transform V (false, (true,  c))).natAbs = 4 then 1 else 0) +
    (if (transform V (true,  (false, c))).natAbs = 4 then 1 else 0) +
    (if (transform V (true,  (true,  c))).natAbs = 4 then 1 else 0)
  let D (c : W 6) : Int := if Q6 c then 2 * cnt4 c else cnt0 c
  have hD_nn (c : W 6) : 0 ≤ D c := by
    dsimp only [D, cnt0, cnt4]
    cases Q6 c <;> simp only [Bool.false_eq_true, if_false, if_true] <;> split <;> split <;> split <;> split <;> omega
  have hsum_z_sq (c : W 6) :
      z00 c * z00 c + z01 c * z01 c + z10 c * z10 c + z11 c * z11 c =
        64 + 80 * ind (Q6 c) - 16 * D c := by
    have hf := hfiber_sq c
    cases hQ : Q6 c
    · have v0 := hZ_vals false false c hQ
      have v1 := hZ_vals false true  c hQ
      have v2 := hZ_vals true  false c hQ
      have v3 := hZ_vals true  true  c hQ
      dsimp only [D, cnt0, ind]; rw [hQ]; simp only [Bool.false_eq_true, if_false]
      have hsqZ (x : Int) (hx : x = 0 ∨ x = 8 ∨ x = -8) :
          x * x = 64 - 64 * (if x = 0 then (1 : Int) else 0) := by
        rcases hx with rfl | rfl | rfl <;> decide
      rw [hsqZ _ v0, hsqZ _ v1, hsqZ _ v2, hsqZ _ v3] at hf
      omega
    · have v0 := hF_vals false false c hQ
      have v1 := hF_vals false true  c hQ
      have v2 := hF_vals true  false c hQ
      have v3 := hF_vals true  true  c hQ
      dsimp only [D, cnt4, ind]; rw [hQ]; simp only [if_true]
      have hsqF (x : Int) (hx : x = 4 ∨ x = -4 ∨ x = 12 ∨ x = -12) :
          x * x = 144 - 128 * (if x.natAbs = 4 then (1 : Int) else 0) := by
        rcases hx with rfl | rfl | rfl | rfl <;> decide
      rw [hsqF _ v0, hsqF _ v1, hsqF _ v2, hsqF _ v3] at hf
      omega
  -- STEP 1: Total defect `∑ D = 4`, and `Dhat(y) = ±4`, forcing `D = 4 * δ_0`!
  have hsupp_split :
      total 6 (fun y => v00 y * v00 y) + total 6 (fun y => v01 y * v01 y) +
      total 6 (fun y => v10 y * v10 y) + total 6 (fun y => v11 y * v11 y) = 98 := by
    have h := hV_supp
    change (total 6 (fun y => v00 y * v00 y) + total 6 (fun y => v01 y * v01 y)) +
           (total 6 (fun y => v10 y * v10 y) + total 6 (fun y => v11 y * v11 y)) = 98 at h
    omega
  have h64 : many 6 = 64 := by decide
  have hD_sum : total 6 D = 4 := by
    have p0 : total 6 (fun c => z00 c * z00 c) = 64 * total 6 (fun y => v00 y * v00 y) := by
      have := Balanced242Section0320.parseval v00; rw [h64] at this; exact this
    have p1 : total 6 (fun c => z01 c * z01 c) = 64 * total 6 (fun y => v01 y * v01 y) := by
      have := Balanced242Section0320.parseval v01; rw [h64] at this; exact this
    have p2 : total 6 (fun c => z10 c * z10 c) = 64 * total 6 (fun y => v10 y * v10 y) := by
      have := Balanced242Section0320.parseval v10; rw [h64] at this; exact this
    have p3 : total 6 (fun c => z11 c * z11 c) = 64 * total 6 (fun y => v11 y * v11 y) := by
      have := Balanced242Section0320.parseval v11; rw [h64] at this; exact this
    have htot := congrArg (total 6) (funext hsum_z_sq)
    simp only [total_add, total_sub, total_const, total_scale, h64, hQ6_wt] at htot
    change total 6 (fun c => z00 c * z00 c) + total 6 (fun c => z01 c * z01 c) +
           total 6 (fun c => z10 c * z10 c) + total 6 (fun c => z11 c * z11 c) =
           64 * 64 + 80 * 28 - 16 * total 6 D at htot
    omega
  -- Autocorrelation parity gives `transform D y = ±4` for all `y ≠ 0`
  have hF6_hat (y : W 6) (hy : y ≠ zero 6) :
      2 * transform (fun c => ind (Q6 c)) y = -transform (fun c => sign (Q6 c)) y := by
    unfold transform
    have hpt (c : W 6) : 2 * (ind (Q6 c) * chr y c) = chr y c - sign (Q6 c) * chr y c := by
      cases Q6 c <;> simp [ind, sign] <;> omega
    rw [← total_scale, funext hpt, total_sub, total_chr_eq y]
    simp only [hy, if_false, Int.zero_sub]
  have hD_hat_sq (y : W 6) : transform D y * transform D y = 16 := by
    if hy : y = zero 6 then
      subst hy
      have h0 : transform D (zero 6) = total 6 D := by
        unfold transform; apply congrArg (total 6); funext c; rw [chr_zero_left, Int.mul_one]
      rw [h0, hD_sum]; decide
    else
      have hw0 : transform (fun c => z00 c * z00 c) y = 64 * total 6 (fun u => v00 u * v00 (add 6 u y)) := by
        have := wiener_khinchin v00 y; rw [h64] at this; exact this
      have hw1 : transform (fun c => z01 c * z01 c) y = 64 * total 6 (fun u => v01 u * v01 (add 6 u y)) := by
        have := wiener_khinchin v01 y; rw [h64] at this; exact this
      have hw2 : transform (fun c => z10 c * z10 c) y = 64 * total 6 (fun u => v10 u * v10 (add 6 u y)) := by
        have := wiener_khinchin v10 y; rw [h64] at this; exact this
      have hw3 : transform (fun c => z11 c * z11 c) y = 64 * total 6 (fun u => v11 u * v11 (add 6 u y)) := by
        have := wiener_khinchin v11 y; rw [h64] at this; exact this
      have he0 := auto_even v00 y hy
      have he1 := auto_even v01 y hy
      have he2 := auto_even v10 y hy
      have he3 := auto_even v11 y hy
      have htr_sum : transform (fun c => z00 c * z00 c + z01 c * z01 c + z10 c * z10 c + z11 c * z11 c) y =
          transform (fun c => z00 c * z00 c) y + transform (fun c => z01 c * z01 c) y +
          transform (fun c => z10 c * z10 c) y + transform (fun c => z11 c * z11 c) y := by
        unfold transform
        have hpt (c : W 6) : (z00 c * z00 c + z01 c * z01 c + z10 c * z10 c + z11 c * z11 c) * chr y c =
            z00 c * z00 c * chr y c + z01 c * z01 c * chr y c +
            z10 c * z10 c * chr y c + z11 c * z11 c * chr y c := by
          simp only [Int.add_mul]
        rw [funext hpt, total_add, total_add, total_add]
      have htr_rhs : transform (fun c => 64 + 80 * ind (Q6 c) - 16 * D c) y =
          80 * transform (fun c => ind (Q6 c)) y - 16 * transform D y := by
        unfold transform
        have hpt (c : W 6) : (64 + 80 * ind (Q6 c) - 16 * D c) * chr y c =
            64 * chr y c + 80 * (ind (Q6 c) * chr y c) - 16 * (D c * chr y c) := by
          rw [Int.sub_mul, Int.add_mul]; ac_rfl
        rw [funext hpt, total_sub, total_add, total_scale, total_scale, total_scale, total_chr_eq y]
        simp [hy]
      have hcomb : transform (fun c => z00 c * z00 c) y + transform (fun c => z01 c * z01 c) y +
          transform (fun c => z10 c * z10 c) y + transform (fun c => z11 c * z11 c) y =
          80 * transform (fun c => ind (Q6 c)) y - 16 * transform D y := by
        rw [← htr_sum, funext hsum_z_sq, htr_rhs]
      have hmod8 : transform D y % 8 = 4 := by
        have hF := hF6_hat y hy
        rcases hQ6_bent y with hb | hb <;> omega
      have hbound : -4 ≤ transform D y ∧ transform D y ≤ 4 := by
        have hle : transform D y ≤ total 6 D := by
          unfold transform; apply total_mono 6; intro c
          have hnn := hD_nn c
          have hch : chr y c = 1 ∨ chr y c = -1 := by unfold chr; cases dot 6 y c <;> decide
          rcases hch with h | h <;> rw [h] <;> omega
        have hge : -total 6 D ≤ transform D y := by
          unfold transform
          have : total 6 (fun c => -D c) ≤ total 6 (fun c => D c * chr y c) := by
            apply total_mono 6; intro c
            have hnn := hD_nn c
            have hch : chr y c = 1 ∨ chr y c = -1 := by unfold chr; cases dot 6 y c <;> decide
            rcases hch with h | h <;> rw [h] <;> omega
          have hneg : total 6 (fun c => -D c) = -total 6 D := by
            have hpt (c : W 6) : -D c = (-1 : Int) * D c := by omega
            rw [funext hpt, total_scale]; omega
          omega
        omega
      have hpm4 : transform D y = 4 ∨ transform D y = -4 := by omega
      rcases hpm4 with h | h <;> rw [h] <;> decide
  have hD_sq_sum : total 6 (fun c => D c * D c) = total 6 D * total 6 D := by
    have hp := Balanced242Section0320.parseval D
    rw [h64, funext hD_hat_sq, total_const, h64] at hp
    rw [hD_sum]; omega
  -- From `transform V (zero 8) = 0`, we must have `Q6 (zero 6) = false` and `D (zero 6) ≥ 1`
  have hQ6_0 : Q6 (zero 6) = false := by
    cases h0 : Q6 (zero 6)
    · rfl
    · exfalso
      have hm := (hZ_pat false false (zero 6)).2 h0
      have h0eq : (false, (false, zero 6)) = zero 8 := rfl
      rw [h0eq, hV_bal] at hm; omega
  have hD0_pos : 0 < D (zero 6) := by
    dsimp only [D, cnt0]; rw [hQ6_0]; simp only [Bool.false_eq_true, if_false]
    have h0eq : (false, (false, zero 6)) = zero 8 := rfl
    rw [h0eq, hV_bal]; simp only [if_true]
    split <;> split <;> split <;> omega
  have hD_zero_off : ∀ c, c ≠ zero 6 → D c = 0 :=
    support_singleton_of_sum_sq_eq D hD_nn (zero 6) hD0_pos hD_sq_sum
  have hD0_eq4 : D (zero 6) = 4 := by
    have hpt (c : W 6) : D c = D (zero 6) * hits (zero 6) c := by
      unfold hits
      if hc : zero 6 = c then subst hc; simp
      else simp [hc, hD_zero_off c (Ne.symm hc)]
    have hsum := congrArg (total 6) (funext hpt)
    rw [total_scale, diagonal, Int.mul_one, hD_sum] at hsum; omega
  -- Exact consequences of `D = 4 * δ_0`:
  -- 1. At `c = 0`: `Vhat(b0, b1, 0) = 0` for all `b0, b1`, so `z00 0 = z01 0 = z10 0 = z11 0 = 0`
  have hz_at_0 : z00 (zero 6) = 0 ∧ z01 (zero 6) = 0 ∧ z10 (zero 6) = 0 ∧ z11 (zero 6) = 0 := by
    have hc0 : cnt0 (zero 6) = 4 := by dsimp only [D] at hD0_eq4; rw [hQ6_0] at hD0_eq4; exact hD0_eq4
    dsimp only [cnt0] at hc0
    have hle1 : ∀ p : Prop, [Decidable p] → (if p then (1 : Int) else 0) ≤ 1 := fun p _ => by split <;> decide
    have l00 := hle1 (transform V (false, (false, zero 6)) = 0)
    have l01 := hle1 (transform V (false, (true,  zero 6)) = 0)
    have l10 := hle1 (transform V (true,  (false, zero 6)) = 0)
    have l11 := hle1 (transform V (true,  (true,  zero 6)) = 0)
    have h00 : transform V (false, (false, zero 6)) = 0 := by
      if h : transform V (false, (false, zero 6)) = 0 then exact h
      else exfalso; simp only [h, if_false] at hc0; omega
    have h01 : transform V (false, (true, zero 6)) = 0 := by
      if h : transform V (false, (true, zero 6)) = 0 then exact h
      else exfalso; simp only [h, if_false] at hc0; omega
    have h10 : transform V (true, (false, zero 6)) = 0 := by
      if h : transform V (true, (false, zero 6)) = 0 then exact h
      else exfalso; simp only [h, if_false] at hc0; omega
    have h11 : transform V (true, (true, zero 6)) = 0 := by
      if h : transform V (true, (true, zero 6)) = 0 then exact h
      else exfalso; simp only [h, if_false] at hc0; omega
    rw [htrV false false (zero 6)] at h00
    rw [htrV false true  (zero 6)] at h01
    rw [htrV true  false (zero 6)] at h10
    rw [htrV true  true  (zero 6)] at h11
    simp only [hsf, hst, Int.one_mul, Int.neg_mul, Int.mul_neg, Int.neg_neg] at h00 h01 h10 h11
    omega
  -- 2. On `Z6 \ {0}`: all 4 `Vhat = ±8`, so either all `|z| = 4` OR one `|z| = 8` and three `0`
  have hz_on_Z (c : W 6) (hQ : Q6 c = false) (hc : c ≠ zero 6) :
      ((z00 c).natAbs = 4 ∧ (z01 c).natAbs = 4 ∧ (z10 c).natAbs = 4 ∧ (z11 c).natAbs = 4) ∨
      ((z00 c).natAbs = 8 ∧ z01 c = 0 ∧ z10 c = 0 ∧ z11 c = 0) ∨
      (z00 c = 0 ∧ (z01 c).natAbs = 8 ∧ z10 c = 0 ∧ z11 c = 0) ∨
      (z00 c = 0 ∧ z01 c = 0 ∧ (z10 c).natAbs = 8 ∧ z11 c = 0) ∨
      (z00 c = 0 ∧ z01 c = 0 ∧ z10 c = 0 ∧ (z11 c).natAbs = 8) := by
    have hd0 : cnt0 c = 0 := by have := hD_zero_off c hc; dsimp only [D] at this; rw [hQ] at this; exact this
    dsimp only [cnt0] at hd0
    have hne (b0 b1 : Bool) : transform V (b0, (b1, c)) = 8 ∨ transform V (b0, (b1, c)) = -8 := by
      have hnonneg : ∀ p : Prop, [Decidable p] → 0 ≤ (if p then (1 : Int) else 0) := by
        intro p _; split <;> decide
      have h00_nn := hnonneg (transform V (false, (false, c)) = 0)
      have h01_nn := hnonneg (transform V (false, (true,  c)) = 0)
      have h10_nn := hnonneg (transform V (true,  (false, c)) = 0)
      have h11_nn := hnonneg (transform V (true,  (true,  c)) = 0)
      rcases hZ_vals b0 b1 c hQ with h0 | h8 | hm8
      · exfalso; cases b0 <;> cases b1 <;> simp only [h0, if_true] at hd0 <;> omega
      · exact Or.inl h8
      · exact Or.inr hm8
    have e00 := hne false false; rw [htrV false false c] at e00
    have e01 := hne false true;  rw [htrV false true  c] at e01
    have e10 := hne true  false; rw [htrV true  false c] at e10
    have e11 := hne true  true;  rw [htrV true  true  c] at e11
    simp only [hsf, hst, Int.one_mul, Int.neg_mul, Int.mul_neg, Int.neg_neg] at e00 e01 e10 e11
    exact walsh2_classify (z00 c) (z01 c) (z10 c) (z11 c) 4 (by omega)
      (e00.imp (fun h => by omega) (fun h => by omega))
      (e01.imp (fun h => by omega) (fun h => by omega))
      (e10.imp (fun h => by omega) (fun h => by omega))
      (e11.imp (fun h => by omega) (fun h => by omega))
  -- 3. On `F6`: all 4 `Vhat = ±12`, so either all `|z| = 6` OR one `|z| = 12` and three `0`
  have hz_on_F (c : W 6) (hQ : Q6 c = true) :
      ((z00 c).natAbs = 6 ∧ (z01 c).natAbs = 6 ∧ (z10 c).natAbs = 6 ∧ (z11 c).natAbs = 6) ∨
      ((z00 c).natAbs = 12 ∧ z01 c = 0 ∧ z10 c = 0 ∧ z11 c = 0) ∨
      (z00 c = 0 ∧ (z01 c).natAbs = 12 ∧ z10 c = 0 ∧ z11 c = 0) ∨
      (z00 c = 0 ∧ z01 c = 0 ∧ (z10 c).natAbs = 12 ∧ z11 c = 0) ∨
      (z00 c = 0 ∧ z01 c = 0 ∧ z10 c = 0 ∧ (z11 c).natAbs = 12) := by
    have hcnz : c ≠ zero 6 := fun h => by rw [h, hQ6_0] at hQ; exact Bool.noConfusion hQ
    have hk0 : cnt4 c = 0 := by
      have := hD_zero_off c hcnz; dsimp only [D] at this; rw [hQ] at this; simp only [if_true] at this; omega
    dsimp only [cnt4] at hk0
    have hne (b0 b1 : Bool) : transform V (b0, (b1, c)) = 12 ∨ transform V (b0, (b1, c)) = -12 := by
      have hnonneg : ∀ p : Prop, [Decidable p] → 0 ≤ (if p then (1 : Int) else 0) := by
        intro p _; split <;> decide
      have h00_nn := hnonneg ((transform V (false, (false, c))).natAbs = 4)
      have h01_nn := hnonneg ((transform V (false, (true,  c))).natAbs = 4)
      have h10_nn := hnonneg ((transform V (true,  (false, c))).natAbs = 4)
      have h11_nn := hnonneg ((transform V (true,  (true,  c))).natAbs = 4)
      rcases hF_vals b0 b1 c hQ with h4 | hm4 | h12 | hm12
      · exfalso; have ha4 : (transform V (b0, (b1, c))).natAbs = 4 := by rw [h4]; rfl
        cases b0 <;> cases b1 <;> simp only [ha4, if_true] at hk0 <;> omega
      · exfalso; have ha4 : (transform V (b0, (b1, c))).natAbs = 4 := by rw [hm4]; rfl
        cases b0 <;> cases b1 <;> simp only [ha4, if_true] at hk0 <;> omega
      · exact Or.inl h12
      · exact Or.inr hm12
    have e00 := hne false false; rw [htrV false false c] at e00
    have e01 := hne false true;  rw [htrV false true  c] at e01
    have e10 := hne true  false; rw [htrV true  false c] at e10
    have e11 := hne true  true;  rw [htrV true  true  c] at e11
    simp only [hsf, hst, Int.one_mul, Int.neg_mul, Int.mul_neg, Int.neg_neg] at e00 e01 e10 e11
    exact walsh2_classify (z00 c) (z01 c) (z10 c) (z11 c) 6 (by omega)
      (e00.imp (fun h => by omega) (fun h => by omega))
      (e01.imp (fun h => by omega) (fun h => by omega))
      (e10.imp (fun h => by omega) (fun h => by omega))
      (e11.imp (fun h => by omega) (fun h => by omega))
  -- STEP 2: `β(c) := (z00 c / 2) % 2 = 1` is affine and supported in `F6` (size 28 < 32), so `β ≡ false`!
  have hz00_even (c : W 6) : z00 c % 2 = 0 := by
    cases hQ : Q6 c
    · if hc : c = zero 6 then subst hc; rw [hz_at_0.1]; rfl
      else rcases hz_on_Z c hQ hc with h | h | h | h | h <;> omega
    · rcases hz_on_F c hQ with h | h | h | h | h <;> omega
  let β (c : W 6) : Bool := decide (z00 c / 2 % 2 = 1)
  have hβ_sub (c : W 6) : ind (β c) ≤ ind (Q6 c) := by
    cases hQ : Q6 c
    · have h4 : z00 c % 4 = 0 := by
        if hc : c = zero 6 then subst hc; rw [hz_at_0.1]; rfl
        else rcases hz_on_Z c hQ hc with h | h | h | h | h <;> omega
      have hbf : β c = false := by dsimp only [β]; apply decide_eq_false; omega
      rw [hbf]; simp [ind]
    · simp [ind]; cases β c <;> decide
  have hβ_wt_le : total 6 (fun c => ind (β c)) ≤ 28 := by
    calc total 6 (fun c => ind (β c)) ≤ total 6 (fun c => ind (Q6 c)) := total_mono 6 _ _ hβ_sub
      _ = 28 := hQ6_wt
  have hβ_wt_zero : total 6 (fun c => ind (β c)) = 0 := by
    have hcases := affine_weight_6 β (affine_of_div2_transform v00 hz00_even)
    dsimp only at hcases; omega
  have hβ_false (c : W 6) : β c = false := by
    cases hbc : β c
    · rfl
    · exfalso
      have hge : 1 ≤ total 6 (fun u => ind (β u)) := by
        have hpt (u : W 6) : hits c u ≤ ind (β u) := by
          unfold hits; if hu : c = u then subst hu; simp [hbc, ind] else simp [hu, ind_nonneg]
        have hm := total_mono 6 _ _ hpt; rw [diagonal] at hm; exact hm
      omega
  -- Hence on `F6`, NEVER all four `|z| = 6`; EVERY `z_x(c)` is divisible by 4!
  have hz_on_F_12 (c : W 6) (hQ : Q6 c = true) :
      ((z00 c).natAbs = 12 ∧ z01 c = 0 ∧ z10 c = 0 ∧ z11 c = 0) ∨
      (z00 c = 0 ∧ (z01 c).natAbs = 12 ∧ z10 c = 0 ∧ z11 c = 0) ∨
      (z00 c = 0 ∧ z01 c = 0 ∧ (z10 c).natAbs = 12 ∧ z11 c = 0) ∨
      (z00 c = 0 ∧ z01 c = 0 ∧ z10 c = 0 ∧ (z11 c).natAbs = 12) := by
    rcases hz_on_F c hQ with h6 | h12
    · exfalso
      have hbf := hβ_false c
      dsimp only [β] at hbf
      have h1 : z00 c / 2 % 2 = 1 := by omega
      rw [decide_eq_true h1] at hbf; exact Bool.noConfusion hbf
    · exact h12
  have hz_div4 : (∀ c, z00 c % 4 = 0) ∧ (∀ c, z01 c % 4 = 0) ∧ (∀ c, z10 c % 4 = 0) ∧ (∀ c, z11 c % 4 = 0) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro c; cases hQ : Q6 c)
    · (if hc : c = zero 6 then subst hc; rw [hz_at_0.1]; rfl else rcases hz_on_Z c hQ hc with h | h | h | h | h <;> omega)
    · (rcases hz_on_F_12 c hQ with h | h | h | h <;> omega)
    · (if hc : c = zero 6 then subst hc; rw [hz_at_0.2.1]; rfl else rcases hz_on_Z c hQ hc with h | h | h | h | h <;> omega)
    · (rcases hz_on_F_12 c hQ with h | h | h | h <;> omega)
    · (if hc : c = zero 6 then subst hc; rw [hz_at_0.2.2.1]; rfl else rcases hz_on_Z c hQ hc with h | h | h | h | h <;> omega)
    · (rcases hz_on_F_12 c hQ with h | h | h | h <;> omega)
    · (if hc : c = zero 6 then subst hc; rw [hz_at_0.2.2.2]; rfl else rcases hz_on_Z c hQ hc with h | h | h | h | h <;> omega)
    · (rcases hz_on_F_12 c hQ with h | h | h | h <;> omega)
  -- STEP 3: Quadratic parities `p00..p11` are `Cube`; pairwise XORs force one `|F_{x*}| = 28` and others `0`!
  let p00 (c : W 6) := decide (z00 c / 4 % 2 = 1)
  let p01 (c : W 6) := decide (z01 c / 4 % 2 = 1)
  let p10 (c : W 6) := decide (z10 c / 4 % 2 = 1)
  let p11 (c : W 6) := decide (z11 c / 4 % 2 = 1)
  have hc00 : Cube p00 := cube_of_div4_transform v00 hz_div4.1
  have hc01 : Cube p01 := cube_of_div4_transform v01 hz_div4.2.1
  have hc10 : Cube p10 := cube_of_div4_transform v10 hz_div4.2.2.1
  have hc11 : Cube p11 := cube_of_div4_transform v11 hz_div4.2.2.2
  let F00 (c : W 6) := decide ((z00 c).natAbs = 12)
  let F01 (c : W 6) := decide ((z01 c).natAbs = 12)
  let F10 (c : W 6) := decide ((z10 c).natAbs = 12)
  let F11 (c : W 6) := decide ((z11 c).natAbs = 12)
  let Cset (c : W 6) := decide ((z00 c).natAbs = 4)
  have hp_decomp (c : W 6) :
      p00 c = xor (F00 c) (Cset c) ∧ p01 c = xor (F01 c) (Cset c) ∧
      p10 c = xor (F10 c) (Cset c) ∧ p11 c = xor (F11 c) (Cset c) ∧
      ind (F00 c) + ind (F01 c) + ind (F10 c) + ind (F11 c) = ind (Q6 c) := by
    dsimp only [p00, p01, p10, p11, F00, F01, F10, F11, Cset, ind]
    cases hQ : Q6 c
    · if hc : c = zero 6 then
        subst hc
        have ⟨e0, e1, e2, e3⟩ := hz_at_0
        rw [e0, e1, e2, e3]; decide
      else
        have hZ := hz_on_Z c hQ hc
        generalize z00 c = x0 at hZ ⊢; generalize z01 c = x1 at hZ ⊢
        generalize z10 c = x2 at hZ ⊢; generalize z11 c = x3 at hZ ⊢
        rcases hZ with ⟨a0, a1, a2, a3⟩ | ⟨a0, a1, a2, a3⟩ | ⟨a0, a1, a2, a3⟩ | ⟨a0, a1, a2, a3⟩ | ⟨a0, a1, a2, a3⟩
        · have m0 : x0 / 4 % 2 = 1 := by omega
          have m1 : x1 / 4 % 2 = 1 := by omega
          have m2 : x2 / 4 % 2 = 1 := by omega
          have m3 : x3 / 4 % 2 = 1 := by omega
          simp [a0, a1, a2, a3, m0, m1, m2, m3]
        · have m0 : x0 / 4 % 2 ≠ 1 := by omega
          simp [a0, a1, a2, a3, m0]
        · have m1 : x1 / 4 % 2 ≠ 1 := by omega
          simp [a0, a1, a2, a3, m1]
        · have m2 : x2 / 4 % 2 ≠ 1 := by omega
          simp [a0, a1, a2, a3, m2]
        · have m3 : x3 / 4 % 2 ≠ 1 := by omega
          simp [a0, a1, a2, a3, m3]
    · have hF := hz_on_F_12 c hQ
      generalize z00 c = x0 at hF ⊢; generalize z01 c = x1 at hF ⊢
      generalize z10 c = x2 at hF ⊢; generalize z11 c = x3 at hF ⊢
      rcases hF with ⟨a0, a1, a2, a3⟩ | ⟨a0, a1, a2, a3⟩ | ⟨a0, a1, a2, a3⟩ | ⟨a0, a1, a2, a3⟩
      · have m0 : x0 / 4 % 2 = 1 := by omega
        simp [a0, a1, a2, a3, m0]
      · have m1 : x1 / 4 % 2 = 1 := by omega
        simp [a0, a1, a2, a3, m1]
      · have m2 : x2 / 4 % 2 = 1 := by omega
        simp [a0, a1, a2, a3, m2]
      · have m3 : x3 / 4 % 2 = 1 := by omega
        simp [a0, a1, a2, a3, m3]
  -- Pairwise sums `a_i + a_j` are weights of `Cube` functions `p_i ⊕ p_j = F_i ⊕ F_j`!
  let a0 := total 6 (fun c => ind (F00 c))
  let a1 := total 6 (fun c => ind (F01 c))
  let a2 := total 6 (fun c => ind (F10 c))
  let a3 := total 6 (fun c => ind (F11 c))
  have ha_nn : 0 ≤ a0 ∧ 0 ≤ a1 ∧ 0 ≤ a2 ∧ 0 ≤ a3 :=
    ⟨total_nonneg' _ (fun _ => ind_nonneg _), total_nonneg' _ (fun _ => ind_nonneg _),
     total_nonneg' _ (fun _ => ind_nonneg _), total_nonneg' _ (fun _ => ind_nonneg _)⟩
  have ha_sum : a0 + a1 + a2 + a3 = 28 := by
    have htot := congrArg (total 6) (funext (fun c => (hp_decomp c).2.2.2.2))
    simp only [total_add, hQ6_wt] at htot; exact htot
  have hpair_rm (pa pb Fa Fb : W 6 → Bool) (hpa : Cube pa) (hpb : Cube pb)
      (h1 : ∀ c, pa c = xor (Fa c) (Cset c)) (h2 : ∀ c, pb c = xor (Fb c) (Cset c))
      (hdisj : ∀ c, (Fa c && Fb c) = false) :
      let s := total 6 (fun c => ind (Fa c)) + total 6 (fun c => ind (Fb c))
      s = 0 ∨ s = 16 ∨ s = 24 ∨ s = 28 ∨ s = 32 ∨ s = 36 ∨ s = 40 ∨ s = 48 ∨ s = 64 := by
    have hxor (c : W 6) : ind (xor (pa c) (pb c)) = ind (Fa c) + ind (Fb c) := by
      rw [h1 c, h2 c]
      have hd := hdisj c
      generalize Fa c = b1 at hd ⊢; generalize Fb c = b2 at hd ⊢; generalize Cset c = b3
      cases b1 <;> cases b2 <;> cases b3 <;> simp [ind] at hd ⊢
    have hrm := rm2_6_weight (fun c => xor (pa c) (pb c)) (cube_xor pa pb hpa hpb)
    dsimp only at hrm ⊢
    rw [funext hxor, total_add] at hrm; exact hrm
  have hdisjF (c : W 6) :
      (F00 c && F01 c) = false ∧ (F00 c && F10 c) = false ∧ (F00 c && F11 c) = false ∧
      (F01 c && F10 c) = false ∧ (F01 c && F11 c) = false ∧ (F10 c && F11 c) = false := by
    have hsum1 := (hp_decomp c).2.2.2.2
    generalize F00 c = b0 at hsum1 ⊢; generalize F01 c = b1 at hsum1 ⊢
    generalize F10 c = b2 at hsum1 ⊢; generalize F11 c = b3 at hsum1 ⊢
    generalize Q6 c = bq at hsum1
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases bq <;> simp [ind] at hsum1 ⊢
  have h01 := hpair_rm p00 p01 F00 F01 hc00 hc01 (fun c => (hp_decomp c).1) (fun c => (hp_decomp c).2.1) (fun c => (hdisjF c).1)
  have h02 := hpair_rm p00 p10 F00 F10 hc00 hc10 (fun c => (hp_decomp c).1) (fun c => (hp_decomp c).2.2.1) (fun c => (hdisjF c).2.1)
  have h03 := hpair_rm p00 p11 F00 F11 hc00 hc11 (fun c => (hp_decomp c).1) (fun c => (hp_decomp c).2.2.2.1) (fun c => (hdisjF c).2.2.1)
  have h12 := hpair_rm p01 p10 F01 F10 hc01 hc10 (fun c => (hp_decomp c).2.1) (fun c => (hp_decomp c).2.2.1) (fun c => (hdisjF c).2.2.2.1)
  have h13 := hpair_rm p01 p11 F01 F11 hc01 hc11 (fun c => (hp_decomp c).2.1) (fun c => (hp_decomp c).2.2.2.1) (fun c => (hdisjF c).2.2.2.2.1)
  have h23 := hpair_rm p10 p11 F10 F11 hc10 hc11 (fun c => (hp_decomp c).2.2.1) (fun c => (hp_decomp c).2.2.2.1) (fun c => (hdisjF c).2.2.2.2.2)
  dsimp only at h01 h02 h03 h12 h13 h23
  have hrm_pair28 (u v : Int)
      (hu : u = 0 ∨ u = 16 ∨ u = 24 ∨ u = 28 ∨ u = 32 ∨ u = 36 ∨ u = 40 ∨ u = 48 ∨ u = 64)
      (hv : v = 0 ∨ v = 16 ∨ v = 24 ∨ v = 28 ∨ v = 32 ∨ v = 36 ∨ v = 40 ∨ v = 48 ∨ v = 64)
      (hsum : u + v = 28) : (u = 28 ∧ v = 0) ∨ (u = 0 ∧ v = 28) := by
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩ | omega
  have hone28 :
      (a0 = 28 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0) ∨
      (a0 = 0 ∧ a1 = 28 ∧ a2 = 0 ∧ a3 = 0) ∨
      (a0 = 0 ∧ a1 = 0 ∧ a2 = 28 ∧ a3 = 0) ∨
      (a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 28) := by
    rcases hrm_pair28 (a0 + a1) (a2 + a3) h01 h23 (by omega) with ⟨h01', h23'⟩ | ⟨h01', h23'⟩
    · have ha2 : a2 = 0 := by omega
      have ha3 : a3 = 0 := by omega
      rcases hrm_pair28 (a0 + a2) (a1 + a2) h02 h12 (by omega) with ⟨h0', h1'⟩ | ⟨h0', h1'⟩
      · left; omega
      · right; left; omega
    · have ha0 : a0 = 0 := by omega
      have ha1 : a1 = 0 := by omega
      rcases hrm_pair28 (a0 + a2) (a0 + a3) h02 h03 (by omega) with ⟨h2', h3'⟩ | ⟨h2', h3'⟩
      · right; right; left; omega
      · right; right; right; omega
  -- STEPS 4 & 5 packaged as a single symmetric helper for whichever cell `vs` holds all 28 of `F6`!
  have finish (vs va vb vc : W 6 → Int) (ps pa : W 6 → Bool)
      (hvs_val : ∀ y, vs y = -1 ∨ vs y = 0 ∨ vs y = 1)
      (hpa_cube : Cube pa)
      (hperm : ∀ c,
        (transform vs c = z00 c ∧ transform va c = z01 c ∧ transform vb c = z10 c ∧ transform vc c = z11 c ∧
         ps c = p00 c ∧ pa c = p01 c) ∨
        (transform vs c = z01 c ∧ transform va c = z00 c ∧ transform vb c = z10 c ∧ transform vc c = z11 c ∧
         ps c = p01 c ∧ pa c = p00 c) ∨
        (transform vs c = z10 c ∧ transform va c = z00 c ∧ transform vb c = z01 c ∧ transform vc c = z11 c ∧
         ps c = p10 c ∧ pa c = p00 c) ∨
        (transform vs c = z11 c ∧ transform va c = z00 c ∧ transform vb c = z01 c ∧ transform vc c = z10 c ∧
         ps c = p11 c ∧ pa c = p00 c))
      (hFs_all : total 6 (fun c => ind (decide ((transform vs c).natAbs = 12))) = 28)
      (hFa_zero : total 6 (fun c => ind (decide ((transform va c).natAbs = 12))) = 0) : False := by
    let zs := transform vs; let za := transform va; let zb := transform vb; let zc := transform vc
    -- Every `c ∈ F6` has `|zs c| = 12` and `za c = zb c = zc c = 0`, and off `F6` never `12`!
    have hFa_none (c : W 6) : (za c).natAbs ≠ 12 := by
      intro h12
      have hge : 1 ≤ total 6 (fun u => ind (decide ((za u).natAbs = 12))) := by
        have hpt (u : W 6) : hits c u ≤ ind (decide ((za u).natAbs = 12)) := by
          unfold hits; if hu : c = u then subst hu; simp [h12, ind] else simp [hu, ind_nonneg]
        have hm := total_mono 6 _ _ hpt; rw [diagonal] at hm; exact hm
      change total 6 (fun u => ind (decide ((za u).natAbs = 12))) = 0 at hFa_zero
      omega
    -- `pa = Cset`, so `Cset` is `Cube`!
    have hpa_eq_C (c : W 6) : pa c = Cset c := by
      rcases hperm c with ⟨_, ea, _, _, _, epa⟩ | ⟨_, ea, _, _, _, epa⟩ | ⟨_, ea, _, _, _, epa⟩ | ⟨_, ea, _, _, _, epa⟩
      · have hne := hFa_none c; dsimp only [za] at hne; rw [ea] at hne
        have hF : F01 c = false := decide_eq_false hne
        rw [epa, (hp_decomp c).2.1, hF, Bool.false_xor]
      · have hne := hFa_none c; dsimp only [za] at hne; rw [ea] at hne
        have hF : F00 c = false := decide_eq_false hne
        rw [epa, (hp_decomp c).1, hF, Bool.false_xor]
      · have hne := hFa_none c; dsimp only [za] at hne; rw [ea] at hne
        have hF : F00 c = false := decide_eq_false hne
        rw [epa, (hp_decomp c).1, hF, Bool.false_xor]
      · have hne := hFa_none c; dsimp only [za] at hne; rw [ea] at hne
        have hF : F00 c = false := decide_eq_false hne
        rw [epa, (hp_decomp c).1, hF, Bool.false_xor]
    have hC_cube : Cube Cset := by
      have : Cset = pa := funext (fun c => (hpa_eq_C c).symm)
      rw [this]; exact hpa_cube
    have hC_rm := rm2_6_weight Cset hC_cube
    dsimp only at hC_rm
    -- Pointwise spectrum of `zs, za, zb, zc`!
    have hzs_F (c : W 6) (hQ : Q6 c = true) : (zs c).natAbs = 12 ∧ za c = 0 ∧ zb c = 0 ∧ zc c = 0 := by
      have hsub (u : W 6) : ind (decide ((zs u).natAbs = 12)) ≤ ind (Q6 u) := by
        cases hQu : Q6 u
        · have hne12 : (zs u).natAbs ≠ 12 := by
            rcases hperm u with ⟨es, _, _, _, _, _⟩ | ⟨es, _, _, _, _, _⟩ | ⟨es, _, _, _, _, _⟩ | ⟨es, _, _, _, _, _⟩ <;>
              (dsimp only [zs]; rw [es]; if hu : u = zero 6 then subst hu; omega else rcases hz_on_Z u hQu hu with h | h | h | h | h <;> omega)
          simp [hne12, ind]
        · simp only [ind, if_true]; split <;> decide
      have heq12 : (zs c).natAbs = 12 := by
        if h12 : (zs c).natAbs = 12 then exact h12
        else
          exfalso
          have hle : total 6 (fun u => ind (decide ((zs u).natAbs = 12))) ≤ 27 := by
            have hpt (u : W 6) : ind (decide ((zs u).natAbs = 12)) ≤ ind (Q6 u) - hits c u := by
              unfold hits
              if hu : c = u then subst hu; simp [h12, hQ, ind]
              else simp only [hu, if_false, Int.sub_zero]; exact hsub u
            have hm := total_mono 6 _ _ hpt
            rw [total_sub, hQ6_wt, diagonal] at hm; exact hm
          change total 6 (fun u => ind (decide ((zs u).natAbs = 12))) = 28 at hFs_all
          omega
      rcases hperm c with ⟨es, ea, eb, ec, _, _⟩ | ⟨es, ea, eb, ec, _, _⟩ | ⟨es, ea, eb, ec, _, _⟩ | ⟨es, ea, eb, ec, _, _⟩ <;>
        (dsimp only [zs, za, zb, zc] at heq12 ⊢; rw [es] at heq12 ⊢; rw [ea, eb, ec];
         rcases hz_on_F_12 c hQ with h | h | h | h <;> omega)
    -- Define `Bs, Ba, Bb, Bc` counts of `|z| = 8` on `Z6 \ {0}`
    let Bs := total 6 (fun c => ind (decide ((zs c).natAbs = 8)))
    let Ba := total 6 (fun c => ind (decide ((za c).natAbs = 8)))
    let Bb := total 6 (fun c => ind (decide ((zb c).natAbs = 8)))
    let Bc := total 6 (fun c => ind (decide ((zc c).natAbs = 8)))
    let Ccnt := total 6 (fun c => ind (Cset c))
    have hzs_sq_pt (c : W 6) :
        zs c * zs c = 144 * ind (Q6 c) + 64 * ind (decide ((zs c).natAbs = 8)) + 16 * ind (Cset c) := by
      cases hQ : Q6 c
      · if hc : c = zero 6 then
          subst hc
          have h0s : zs (zero 6) = 0 := by
            rcases hperm (zero 6) with ⟨es, _, _, _, _, _⟩ | ⟨es, _, _, _, _, _⟩ | ⟨es, _, _, _, _, _⟩ | ⟨es, _, _, _, _, _⟩ <;>
              (dsimp only [zs]; rw [es]; omega)
          have h0C : Cset (zero 6) = false := by dsimp only [Cset]; rw [hz_at_0.1]; rfl
          simp [h0s, h0C, ind]
        else
          rcases hperm c with ⟨es, _, _, _, _, _⟩ | ⟨es, _, _, _, _, _⟩ | ⟨es, _, _, _, _, _⟩ | ⟨es, _, _, _, _, _⟩ <;>
            (dsimp only [zs, Cset]; rw [es];
             rcases hz_on_Z c hQ hc with ⟨k0, k1, k2, k3⟩ | ⟨k0, k1, k2, k3⟩ | ⟨k0, k1, k2, k3⟩ | ⟨k0, k1, k2, k3⟩ | ⟨k0, k1, k2, k3⟩ <;>
               (have hsq (x : Int) (m : Nat) (h : x.natAbs = m) : x * x = (m : Int) * (m : Int) := by
                  have h1 : x = (m : Int) ∨ x = -(m : Int) := by omega
                  rcases h1 with rfl | rfl <;> simp
                simp [ind, k0, k1, k2, k3]; try (rw [hsq _ _ ‹_›]; decide)))
      · have hf := hzs_F c hQ
        have hC : Cset c = false := by
          dsimp only [Cset]; rcases hz_on_F_12 c hQ with h | h | h | h <;> apply decide_eq_false <;> omega
        have hsq12 : zs c * zs c = 144 := by
          have : zs c = 12 ∨ zs c = -12 := by omega
          rcases this with h | h <;> rw [h] <;> decide
        have hne8 : (zs c).natAbs ≠ 8 := by omega
        simp [hsq12, hne8, hC, ind]
    have hparseval_s : total 6 (fun a => zs a * zs a) = 64 * total 6 (fun y => vs y * vs y) := by
      have := Balanced242Section0320.parseval vs; rw [h64] at this; exact this
    have htot_s := congrArg (total 6) (funext hzs_sq_pt)
    simp only [total_add, total_scale, hQ6_wt] at htot_s
    change total 6 (fun x => zs x * zs x) = 144 * 28 + 64 * Bs + 16 * Ccnt at htot_s
    have hms_le : total 6 (fun y => vs y * vs y) ≤ 64 := by
      have hpt (y : W 6) : vs y * vs y ≤ 1 := by rcases hvs_val y with h | h | h <;> rw [h] <;> decide
      have hm := total_mono 6 _ _ hpt; rw [total_const, Int.mul_one, h64] at hm; exact hm
    have hBs_nn : 0 ≤ Bs := total_nonneg' _ (fun _ => ind_nonneg _)
    have hC_nn : 0 ≤ Ccnt := total_nonneg' _ (fun _ => ind_nonneg _)
    -- `64 * ms = 4032 + 64 * Bs + 16 * Ccnt ≤ 4096` => `Ccnt ≤ 4` => `Ccnt = 0` and `Bs ≤ 1`!
    have hC_zero : Ccnt = 0 := by omega
    have hC_false (c : W 6) : Cset c = false := by
      cases hc : Cset c
      · rfl
      · exfalso
        have hge : 1 ≤ Ccnt := by
          have hpt (u : W 6) : hits c u ≤ ind (Cset u) := by
            unfold hits; if hu : c = u then subst hu; simp [hc, ind] else simp [hu, ind_nonneg]
          have hm := total_mono 6 _ _ hpt; rw [diagonal] at hm; exact hm
        omega
    -- Sum of `Bs + Ba + Bb + Bc = 35`!
    have hB_sum_pt (c : W 6) :
        ind (decide ((zs c).natAbs = 8)) + ind (decide ((za c).natAbs = 8)) +
        ind (decide ((zb c).natAbs = 8)) + ind (decide ((zc c).natAbs = 8)) =
        1 - ind (Q6 c) - hits (zero 6) c := by
      cases hQ : Q6 c
      · if hc : c = zero 6 then
          subst hc
          rcases hperm (zero 6) with ⟨es, ea, eb, ec, _, _⟩ | ⟨es, ea, eb, ec, _, _⟩ | ⟨es, ea, eb, ec, _, _⟩ | ⟨es, ea, eb, ec, _, _⟩ <;>
            (dsimp only [zs, za, zb, zc]; rw [es, ea, eb, ec];
             simp [hz_at_0.1, hz_at_0.2.1, hz_at_0.2.2.1, hz_at_0.2.2.2, ind, hits])
        else
          have hcf := hC_false c; dsimp only [Cset] at hcf
          have hne4 : (z00 c).natAbs ≠ 4 := fun h => by rw [decide_eq_true h] at hcf; exact Bool.noConfusion hcf
          rcases hperm c with ⟨es, ea, eb, ec, _, _⟩ | ⟨es, ea, eb, ec, _, _⟩ | ⟨es, ea, eb, ec, _, _⟩ | ⟨es, ea, eb, ec, _, _⟩ <;>
            (dsimp only [zs, za, zb, zc]; rw [es, ea, eb, ec];
             rcases hz_on_Z c hQ hc with ⟨k0, _, _, _⟩ | ⟨k0, k1, k2, k3⟩ | ⟨k0, k1, k2, k3⟩ | ⟨k0, k1, k2, k3⟩ | ⟨k0, k1, k2, k3⟩
             · exact False.elim (hne4 k0)
             · simp [k0, k1, k2, k3, ind, hits, Ne.symm hc]
             · simp [k0, k1, k2, k3, ind, hits, Ne.symm hc]
             · simp [k0, k1, k2, k3, ind, hits, Ne.symm hc]
             · simp [k0, k1, k2, k3, ind, hits, Ne.symm hc])
      · have hne0 : zero 6 ≠ c := fun h => by rw [← h, hQ6_0] at hQ; exact Bool.noConfusion hQ
        have hf := hzs_F c hQ
        have hne8 : (zs c).natAbs ≠ 8 := by omega
        simp [hf.2.1, hf.2.2.1, hf.2.2.2, hne8, ind, hits, hne0]
    have hB_sum : Bs + Ba + Bb + Bc = 35 := by
      have htot := congrArg (total 6) (funext hB_sum_pt)
      simp only [total_add, total_sub, total_const, Int.mul_one, h64, hQ6_wt, diagonal] at htot
      exact htot
    -- Each of `Ba, Bb, Bc` is EVEN (via autocorrelation parity of `va, vb, vc` at any nonzero `y0`)!
    have hB_even (vx : W 6 → Int)
        (hvx8 : ∀ c, transform vx c * transform vx c = 64 * ind (decide ((transform vx c).natAbs = 8))) :
        total 6 (fun c => ind (decide ((transform vx c).natAbs = 8))) % 2 = 0 := by
      let y0 : W 6 := (true, (false, (false, (false, (false, (false, ()))))))
      have hy0 : y0 ≠ zero 6 := fun h => Bool.noConfusion (congrArg Prod.fst h)
      have hwk := wiener_khinchin vx y0
      rw [h64, funext hvx8] at hwk
      have htr : transform (fun c => 64 * ind (decide ((transform vx c).natAbs = 8))) y0 =
          64 * total 6 (fun c => ind (decide ((transform vx c).natAbs = 8)) * chr y0 c) := by
        show total 6 (fun c => (64 * ind (decide ((transform vx c).natAbs = 8))) * chr y0 c) = _
        rw [← total_scale]; apply congrArg (total 6); funext c; exact Int.mul_assoc 64 _ _
      rw [htr] at hwk
      have hev := auto_even vx y0 hy0
      have hsum_even : total 6 (fun c => ind (decide ((transform vx c).natAbs = 8)) * chr y0 c) % 2 = 0 := by omega
      have hmod2_eq : total 6 (fun c => ind (decide ((transform vx c).natAbs = 8)) -
          ind (decide ((transform vx c).natAbs = 8)) * chr y0 c) % 2 = 0 := by
        have hpt (c : W 6) : ind (decide ((transform vx c).natAbs = 8)) -
            ind (decide ((transform vx c).natAbs = 8)) * chr y0 c =
            2 * (ind (decide ((transform vx c).natAbs = 8)) * (if dot 6 y0 c then 1 else 0)) := by
          unfold chr; cases dot 6 y0 c <;> simp [sign] <;> omega
        rw [funext hpt, total_scale]; omega
      rw [total_sub] at hmod2_eq; omega
    have hsq8_of (c : W 6) (vx : W 6 → Int)
        (hcases : transform vx c = 0 ∨ (transform vx c).natAbs = 8) :
        transform vx c * transform vx c = 64 * ind (decide ((transform vx c).natAbs = 8)) := by
      generalize transform vx c = t at hcases ⊢
      rcases hcases with h0 | h8
      · simp [h0, ind]
      · have hpm : t = 8 ∨ t = -8 := by omega
        rcases hpm with h | h <;> simp [h, ind]
    have hother_cases (c : W 6) :
        (za c = 0 ∨ (za c).natAbs = 8) ∧ (zb c = 0 ∨ (zb c).natAbs = 8) ∧ (zc c = 0 ∨ (zc c).natAbs = 8) := by
      cases hQ : Q6 c
      · if hc : c = zero 6 then
          subst hc
          have ⟨e0, e1, e2, e3⟩ := hz_at_0
          rcases hperm (zero 6) with ⟨_, ea, eb, ec, _, _⟩ | ⟨_, ea, eb, ec, _, _⟩ | ⟨_, ea, eb, ec, _, _⟩ | ⟨_, ea, eb, ec, _, _⟩ <;>
            (dsimp only [za, zb, zc]; rw [ea, eb, ec]; exact ⟨Or.inl (by assumption), Or.inl (by assumption), Or.inl (by assumption)⟩)
        else
          have hcf := hC_false c; dsimp only [Cset] at hcf
          have hne4 : (z00 c).natAbs ≠ 4 := fun h => by rw [decide_eq_true h] at hcf; exact Bool.noConfusion hcf
          have h4_08 : (z00 c = 0 ∨ (z00 c).natAbs = 8) ∧ (z01 c = 0 ∨ (z01 c).natAbs = 8) ∧
              (z10 c = 0 ∨ (z10 c).natAbs = 8) ∧ (z11 c = 0 ∨ (z11 c).natAbs = 8) := by
            rcases hz_on_Z c hQ hc with ⟨k0, _, _, _⟩ | ⟨k0, k1, k2, k3⟩ | ⟨k0, k1, k2, k3⟩ | ⟨k0, k1, k2, k3⟩ | ⟨k0, k1, k2, k3⟩
            · exact False.elim (hne4 k0)
            · exact ⟨Or.inr k0, Or.inl k1, Or.inl k2, Or.inl k3⟩
            · exact ⟨Or.inl k0, Or.inr k1, Or.inl k2, Or.inl k3⟩
            · exact ⟨Or.inl k0, Or.inl k1, Or.inr k2, Or.inl k3⟩
            · exact ⟨Or.inl k0, Or.inl k1, Or.inl k2, Or.inr k3⟩
          rcases hperm c with ⟨_, ea, eb, ec, _, _⟩ | ⟨_, ea, eb, ec, _, _⟩ | ⟨_, ea, eb, ec, _, _⟩ | ⟨_, ea, eb, ec, _, _⟩ <;>
            (dsimp only [za, zb, zc]; rw [ea, eb, ec]; exact ⟨by first | exact h4_08.1 | exact h4_08.2.1,
              by first | exact h4_08.2.1 | exact h4_08.2.2.1, by first | exact h4_08.2.2.1 | exact h4_08.2.2.2⟩)
      · have hf := hzs_F c hQ; exact ⟨Or.inl hf.2.1, Or.inl hf.2.2.1, Or.inl hf.2.2.2⟩
    have hBa_ev : Ba % 2 = 0 := hB_even va (fun c => hsq8_of c va (hother_cases c).1)
    have hBb_ev : Bb % 2 = 0 := hB_even vb (fun c => hsq8_of c vb (hother_cases c).2.1)
    have hBc_ev : Bc % 2 = 0 := hB_even vc (fun c => hsq8_of c vc (hother_cases c).2.2)
    -- Therefore `Bs = 1` and `ms = 64`!
    have hBs_eq1 : Bs = 1 := by omega
    have hms_eq64 : total 6 (fun y => vs y * vs y) = 64 := by omega
    have hvs_pm1 (y : W 6) : vs y = 1 ∨ vs y = -1 := by
      rcases hvs_val y with h | h | h
      · exact Or.inr h
      · exfalso
        have hle : total 6 (fun u => vs u * vs u) ≤ 63 := by
          have hpt (u : W 6) : vs u * vs u ≤ 1 - hits y u := by
            unfold hits
            if hu : y = u then subst hu; simp [h]
            else simp only [hu, if_false, Int.sub_zero]; rcases hvs_val u with hu1 | hu1 | hu1 <;> rw [hu1] <;> decide
          have hm := total_mono 6 _ _ hpt; rw [total_sub, total_const, Int.mul_one, h64, diagonal] at hm; exact hm
        omega
      · exact Or.inl h
    -- Extract the unique point `e ∈ W 6` with `|zs e| = 8`!
    have hex_e : ∃ e : W 6, (zs e).natAbs = 8 := by
      cases hall : (worlds 6).all (fun c => !decide ((zs c).natAbs = 8))
      · obtain ⟨e, _, he_neg⟩ := all_false_exists (fun c => !decide ((zs c).natAbs = 8)) (worlds 6) hall
        have he : decide ((zs e).natAbs = 8) = true := by
          cases hb : decide ((zs e).natAbs = 8) <;> simp [hb] at he_neg ⊢
        exact ⟨e, of_decide_eq_true he⟩
      · exfalso
        rw [List.all_eq_true] at hall
        have hz0 (c : W 6) : ind (decide ((zs c).natAbs = 8)) = 0 := by
          have := hall c (all_worlds 6 c); cases hb : decide ((zs c).natAbs = 8) <;> simp [hb, ind] at this ⊢
        have hBs0 : Bs = 0 := by dsimp only [Bs]; rw [funext hz0, total_zero]
        omega
    obtain ⟨e, he8⟩ := hex_e
    have he_nz : e ≠ zero 6 := by
      intro h; subst h
      have h0s : zs (zero 6) = 0 := by
        rcases hperm (zero 6) with ⟨es, _, _, _, _, _⟩ | ⟨es, _, _, _, _, _⟩ | ⟨es, _, _, _, _, _⟩ | ⟨es, _, _, _, _, _⟩ <;>
          (dsimp only [zs]; rw [es]; omega)
      omega
    have he_uniq (c : W 6) : ind (decide ((zs c).natAbs = 8)) = hits e c := by
      unfold hits
      if hce : e = c then subst hce; simp [he8, ind]
      else
        simp only [hce, if_false]
        cases h8 : decide ((zs c).natAbs = 8)
        · rfl
        · exfalso
          have hge2 : 2 ≤ Bs := by
            have hpt (u : W 6) : hits e u + hits c u ≤ ind (decide ((zs u).natAbs = 8)) := by
              unfold hits
              if h1 : e = u then subst h1; simp [he8, Ne.symm hce, ind]
              else if h2 : c = u then subst h2; simp [h1, h8, ind]
              else simp [h1, h2, ind_nonneg]
            have hm := total_mono 6 _ _ hpt; rw [total_add, diagonal, diagonal] at hm; exact hm
          omega
    -- STEP 5: Autocorrelation of `vs` forces `chr y e = transform (sign Q6) y / 8` for ALL `y ∈ W 6`,
    -- contradicting `0 = ∑ chr y e = ∑ transform (sign Q6) y / 8 = 8 * sign (Q6 0) = 8`!
    have hdual_eq (y : W 6) : 8 * chr y e = transform (fun c => sign (Q6 c)) y := by
      if hy : y = zero 6 then
        subst hy
        rw [chr_zero_left, Int.mul_one]
        unfold transform
        have hpt (c : W 6) : sign (Q6 c) * chr (zero 6) c = 1 - 2 * ind (Q6 c) := by
          rw [chr_zero_left, Int.mul_one]; cases Q6 c <;> decide
        rw [funext hpt, total_sub, total_const, total_scale, h64, hQ6_wt]; omega
      else
        have hwk : transform (fun c => zs c * zs c) y = 64 * total 6 (fun u => vs u * vs (add 6 u y)) := by
          have := wiener_khinchin vs y; rw [h64] at this; exact this
        have hzs_pt2 (c : W 6) : zs c * zs c = 144 * ind (Q6 c) + 64 * hits e c := by
          rw [hzs_sq_pt c, he_uniq c, hC_false c]; simp [ind]
        rw [funext hzs_pt2] at hwk
        have htr_lhs : transform (fun c => 144 * ind (Q6 c) + 64 * hits e c) y =
            144 * transform (fun c => ind (Q6 c)) y + 64 * chr y e := by
          unfold transform
          have hpt (c : W 6) : (144 * ind (Q6 c) + 64 * hits e c) * chr y c =
              144 * (ind (Q6 c) * chr y c) + 64 * (chr y c * hits e c) := by
            rw [Int.add_mul]; ac_rfl
          rw [funext hpt, total_add, total_scale, total_scale]
          have he_sum : total 6 (fun c => chr y c * hits e c) = chr y e := by
            have hpt2 (c : W 6) : chr y c * hits e c = chr y e * hits e c := by
              unfold hits; if h : e = c then subst h; rfl else simp [h]
            rw [funext hpt2, total_scale, diagonal, Int.mul_one]
          rw [he_sum]
        rw [htr_lhs] at hwk
        have hF := hF6_hat y hy
        have hmod4 := auto_pm1_mod4 vs hvs_pm1 y hy
        have hchr_pm : chr y e = 1 ∨ chr y e = -1 := by unfold chr; cases dot 6 y e <;> decide
        rcases hQ6_bent y with hb | hb <;> rcases hchr_pm with hc | hc <;> omega
    -- Sum `8 * chr y e = transform (sign Q6) y` over all `y ∈ W 6`: `0 = 64`, contradiction!
    have hsum_both := congrArg (total 6) (funext hdual_eq)
    rw [total_scale] at hsum_both
    have hlhs : total 6 (fun y => chr y e) = 0 := by
      have hsym : (fun y => chr y e) = fun y => chr e y := funext (fun y => chr_comm y e)
      rw [hsym, total_chr_eq e]; simp [he_nz]
    have hrhs : total 6 (fun y => transform (fun c => sign (Q6 c)) y) = 64 := by
      have hinv : total 6 (fun y => transform (fun c => sign (Q6 c)) y * chr (zero 6) y) =
          many 6 * sign (Q6 (zero 6)) := transform_inv_eq (fun c => sign (Q6 c)) (zero 6)
      have hpt (y : W 6) : transform (fun c => sign (Q6 c)) y * chr (zero 6) y =
          transform (fun c => sign (Q6 c)) y := by rw [chr_zero_left, Int.mul_one]
      rw [funext hpt, h64, hQ6_0] at hinv
      simpa [sign] using hinv
    rw [hlhs, hrhs] at hsum_both; omega
  rcases hone28 with ⟨h0, h1, _, _⟩ | ⟨h0, h1, _, _⟩ | ⟨h0, _, h2, _⟩ | ⟨h0, _, _, h3⟩
  · exact finish v00 v01 v10 v11 p00 p01 (fun y => hV_val _) hc01
      (fun c => Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) h0 h1
  · exact finish v01 v00 v10 v11 p01 p00 (fun y => hV_val _) hc00
      (fun c => Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)) h1 h0
  · exact finish v10 v00 v01 v11 p10 p00 (fun y => hV_val _) hc00
      (fun c => Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))) h2 h0
  · exact finish v11 v00 v01 v10 p11 p00 (fun y => hV_val _) hc00
      (fun c => Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))) h3 h0

end Balanced242T98R6Z144

#print axioms Balanced242T98R6Z144.no_t98_r6_z144
