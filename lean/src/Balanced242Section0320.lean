/-
  No 7-variable high section has profile (0,32,0) (mass 96, no coefficients of magnitude 1 or 3).

  Section data: D : W 7 -> Int with |D| <= 2 and transform D = 2 H, where every H value is
  +-5 or +-7 and exactly 32 have magnitude 5.  The phase q = (-1)^((H-1)/2) is a quadratic
  sign, so its Walsh transform takes values in {0, +m, -m} with m = 128 / 2^(rank/2), i.e.
  m in {16, 32, 64, 128}; this standard plateau property is the only hypothesis on q.
-/
import Balanced242Support

namespace Balanced242Section0320
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom Balanced242Support

/-- (-1)^((h-1)/2) for odd h. -/
def phase (h : Int) : Int := if h % 4 = 1 then 1 else -1

theorem chr_comm {n : Nat} (c d : W n) : chr c d = chr d c := by simp [chr, dot_comm n c d]

theorem parseval (D : W n → Int) :
    total n (fun a => transform D a * transform D a) = many n * total n (fun y => D y * D y) := by
  have step (a : W n) : transform D a * transform D a =
      total n (fun y => D y * (transform D a * chr a y)) := by
    show transform D a * total n (fun y => D y * chr a y) = _
    rw [← total_scale]; apply congrArg (total n); funext y; ac_rfl
  simp only [step]; rw [swap]
  have inner (y : W n) : total n (fun a => D y * (transform D a * chr a y)) = D y * (many n * D y) := by
    rw [total_scale, inversion]
  simp only [inner]
  rw [← total_scale]; apply congrArg (total n); funext y; ac_rfl

theorem duality (D q : W n → Int) :
    total n (fun a => q a * transform D a) = total n (fun y => D y * transform q y) := by
  have step (a : W n) : q a * transform D a = total n (fun y => D y * (q a * chr a y)) := by
    show q a * total n (fun y => D y * chr a y) = _
    rw [← total_scale]; apply congrArg (total n); funext y; ac_rfl
  simp only [step]; rw [swap]
  apply congrArg (total n); funext y
  rw [total_scale]; congr 1; unfold transform; apply congrArg (total n); funext a
  rw [chr_comm]

theorem no_section_0_32_0 (D H : W 7 → Int)
    (hD : ∀ y, -2 ≤ D y ∧ D y ≤ 2)
    (hspec : ∀ a, transform D a = 2 * H a)
    (hH : ∀ a, H a = 5 ∨ H a = -5 ∨ H a = 7 ∨ H a = -7)
    (h5 : total 7 (fun a => if H a = 5 ∨ H a = -5 then (1 : Int) else 0) = 32)
    (m : Int) (hm : m = 16 ∨ m = 32 ∨ m = 64 ∨ m = 128)
    (hplat : ∀ y, transform (fun a => phase (H a)) y = 0 ∨
      transform (fun a => phase (H a)) y = m ∨ transform (fun a => phase (H a)) y = -m) :
    False := by
  let q : W 7 → Int := fun a => phase (H a)
  let e : W 7 → Int := fun a => if H a = 5 ∨ H a = -5 then 1 else 0
  have hm128 : many 7 = 128 := by decide
  -- pointwise algebra of the four admissible values
  have F1 (a : W 7) : q a * q a = 1 := by
    rcases hH a with h | h | h | h <;> simp [q, phase, h]
  have F2 (a : W 7) : 2 * H a = -14 * q a + 24 * (q a * e a) := by
    rcases hH a with h | h | h | h <;> simp [q, e, phase, h]
  have F3 (a : W 7) : q a * H a = -7 + 12 * e a := by
    rcases hH a with h | h | h | h <;> simp [q, e, phase, h]
  have F4 (a : W 7) : H a * H a = 49 - 24 * e a := by
    rcases hH a with h | h | h | h <;> simp [q, e, phase, h]
  -- (S1) sum of D^2 is 172
  have S1 : total 7 (fun y => D y * D y) = 172 := by
    have p := parseval D
    simp only [hspec, hm128] at p
    have r (a : W 7) : 2 * H a * (2 * H a) = 196 - 96 * e a := by
      rcases hH a with h | h | h | h <;> simp [e, h]
    simp only [r, total_sub, total_const, total_scale, hm128] at p
    change 128 * 196 - 96 * total 7 e = 128 * _ at p
    have : total 7 e = 32 := h5
    omega
  -- (S2) sum of D * q^ is -1024
  have S2 : total 7 (fun y => D y * transform q y) = -1024 := by
    rw [← duality]
    have r (a : W 7) : q a * transform D a = -14 + 24 * e a := by
      rw [hspec, Int.mul_left_comm, F3]; omega
    simp only [r, total_add, total_const, total_scale, hm128]
    have : total 7 e = 32 := h5
    omega
  -- (S3) sum of q^2 is 16384
  have S3 : total 7 (fun y => transform q y * transform q y) = 16384 := by
    rw [parseval]; simp only [F1, total_const, hm128]; decide
  -- (P) inversion: 64 D = -7 q^ + 12 Y
  have P (y : W 7) : 64 * D y = -7 * transform q y + 12 * total 7 (fun a => q a * e a * chr a y) := by
    have inv := inversion D y
    simp only [hspec, hm128, F2, Int.add_mul, total_add, Int.mul_assoc, total_scale] at inv
    have hq : total 7 (fun a => q a * chr a y) = transform q y := by
      unfold transform; apply congrArg (total 7); funext a; rw [chr_comm]
    rw [hq] at inv
    have : total 7 (fun a => q a * (e a * chr a y)) = total 7 (fun a => q a * e a * chr a y) := by
      apply congrArg (total 7); funext a; rw [Int.mul_assoc]
    rw [this] at inv
    omega
  rcases hm with hm | hm | hm | hm
  · -- rank six: 128 D^2 = 8 D q^ + q^2 at every point
    subst hm
    have pt (y : W 7) : 128 * (D y * D y) = 8 * (D y * transform q y) + transform q y * transform q y := by
      have hp := P y
      have hd : D y = -2 ∨ D y = -1 ∨ D y = 0 ∨ D y = 1 ∨ D y = 2 := by have := hD y; omega
      generalize total 7 (fun a => q a * e a * chr a y) = Y at hp
      rcases hplat y with h | h | h <;> change transform q y = _ at h <;>
        rw [h] at hp ⊢ <;> rcases hd with d | d | d | d | d <;> rw [d] at hp ⊢ <;> omega
    have sum := congrArg (total 7) (funext pt)
    simp only [total_add, total_scale] at sum
    rw [S1, S2, S3] at sum
    omega
  all_goals
    -- rank at most four: 1024 D^2 <= 4 q^2 at every point
    subst hm
    have pt (y : W 7) : 1024 * (D y * D y) ≤ 4 * (transform q y * transform q y) := by
      have hp := P y
      have hd : D y = -2 ∨ D y = -1 ∨ D y = 0 ∨ D y = 1 ∨ D y = 2 := by have := hD y; omega
      generalize total 7 (fun a => q a * e a * chr a y) = Y at hp
      rcases hplat y with h | h | h <;> change transform q y = _ at h <;>
        rw [h] at hp ⊢ <;> rcases hd with d | d | d | d | d <;> rw [d] at hp ⊢ <;> omega
    have sum := total_mono 7 _ _ pt
    simp only [total_scale] at sum
    rw [S1, S3] at sum
    omega

end Balanced242Section0320

#print axioms Balanced242Section0320.no_section_0_32_0
