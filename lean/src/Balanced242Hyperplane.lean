/-
  Affine frequency hyperplanes as seven-variable sections.

  For a nonzero w in W (n+1) and c : Bool, `secPt n w c` parametrizes the hyperplane
  {a : dot w a = c} by W n, and `secFun n w c U` is the folded table on n variables whose
  Walsh transform is the restriction of the transform of U:

      transform U (secPt n w c a) = transform (secFun n w c U) a.

  Sums over the hyperplane become sums over W n (`sec_total`), and folding a table with
  values in [-1, 1] gives values in [-2, 2] (`secFun_bound`).
-/
import Balanced242Support

namespace Balanced242Hyperplane
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom Balanced242Support

theorem add_assoc' (n : Nat) (x y z : W n) : add n (add n x y) z = add n x (add n y z) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [add]; rw [Bool.xor_assoc, ih]

theorem add_cancel (n : Nat) (v x : W n) : add n v (add n v x) = x := by
  rw [← add_assoc', add_self, add_zero_left]

theorem chr_add {n : Nat} (y a b : W n) : chr y (add n a b) = chr y a * chr y b := by
  simp only [chr, dot_right, signMul]

theorem transform_add {n : Nat} (F G : W n → Int) (a : W n) :
    transform (fun x => F x + G x) a = transform F a + transform G a := by
  unfold transform; simp only [Int.add_mul, total_add]

theorem transform_smul {n : Nat} (k : Int) (G : W n → Int) (a : W n) :
    transform (fun x => k * G x) a = k * transform G a := by
  unfold transform; simp only [Int.mul_assoc, total_scale]

def secPt : (n : Nat) → W (n+1) → Bool → W n → W (n+1)
  | 0, w, c, a => if w.1 then (xor c (dot 0 w.2 a), a) else (c, a)
  | m+1, w, c, a => if w.1 then (xor c (dot (m+1) w.2 a), a) else (a.1, secPt m w.2 c a.2)

def secFun : (n : Nat) → W (n+1) → Bool → (W (n+1) → Int) → W n → Int
  | 0, w, c, U, x => if w.1 then U (false, x) + sign c * U (true, add 0 w.2 x) else 0
  | m+1, w, c, U, x => if w.1 then U (false, x) + sign c * U (true, add (m+1) w.2 x)
      else secFun m w.2 c (fun y => U (x.1, y)) x.2

theorem secPt_true (n : Nat) (w : W n) (c : Bool) (a : W n) :
    secPt n (true, w) c a = (xor c (dot n w a), a) := by
  cases n <;> rfl

theorem secFun_true (n : Nat) (w : W n) (c : Bool) (U : W (n+1) → Int) (x : W n) :
    secFun n (true, w) c U x = U (false, x) + sign c * U (true, add n w x) := by
  cases n <;> rfl

theorem secPt_false (m : Nat) (w : W (m+1)) (c : Bool) (b : Bool) (a : W m) :
    secPt (m+1) (false, w) c (b, a) = (b, secPt m w c a) := rfl

theorem secFun_false (m : Nat) (w : W (m+1)) (c : Bool) (U : W (m+2) → Int) (b : Bool) (x : W m) :
    secFun (m+1) (false, w) c U (b, x) = secFun m w c (fun y => U (b, y)) x := rfl

theorem chr_cons {n : Nat} (b : Bool) (a : W n) (v : Bool) (x : W n) :
    chr (r := n+1) (b, a) (v, x) = sign (b && v) * chr a x := by
  simp only [chr, dot, signMul]

theorem transform_split {n : Nat} (U : W (n+1) → Int) (b : Bool) (a : W n) :
    transform U (b, a) =
      transform (fun x => U (false, x)) a + sign b * transform (fun x => U (true, x)) a := by
  show total (n+1) (fun x => U x * chr (r := n+1) (b, a) x) = _
  simp only [total]
  unfold transform
  rw [← total_scale]
  congr 1
  · apply congrArg (total n); funext x
    rw [chr_cons]; cases b <;> simp [sign]
  · apply congrArg (total n); funext x
    rw [chr_cons, Bool.and_true, Int.mul_left_comm]

theorem transform_shift {n : Nat} (G : W n → Int) (v a : W n) :
    transform (fun x => G (add n v x)) a = sign (dot n v a) * transform G a := by
  unfold transform
  have e := sum_shift n v (fun y => G y * chr a (add n v y))
  simp only [add_cancel] at e
  rw [e, ← total_scale]
  apply congrArg (total n); funext y
  rw [chr_add, dot_comm]
  show G y * (sign (dot n a v) * chr a y) = sign (dot n a v) * (G y * chr a y)
  rw [Int.mul_left_comm]

theorem sec_true_transform (n : Nat) (w : W n) (c : Bool) (U : W (n+1) → Int) (a : W n) :
    transform U (xor c (dot n w a), a) =
      transform (fun x => U (false, x) + sign c * U (true, add n w x)) a := by
  rw [transform_split, transform_add, transform_smul, transform_shift (fun x => U (true, x)),
    signMul, Int.mul_assoc]

theorem zero_cons (n : Nat) : zero (n+1) = (false, zero n) := rfl

theorem sec_transform : ∀ (n : Nat) (w : W (n+1)), w ≠ zero (n+1) →
    ∀ (c : Bool) (U : W (n+1) → Int) (a : W n),
      transform U (secPt n w c a) = transform (secFun n w c U) a := by
  intro n
  induction n with
  | zero =>
    intro w hw c U a
    rcases w with ⟨b, w'⟩
    cases b
    · exact absurd rfl hw
    · rw [secPt_true, sec_true_transform]
      apply congrArg (fun F => transform F a); funext x; rw [secFun_true]
  | succ m ih =>
    intro w hw c U a
    rcases w with ⟨b, w'⟩
    cases b
    · have hw' : w' ≠ zero (m+1) := fun h => hw (by rw [h]; rfl)
      rcases a with ⟨a1, a2⟩
      rw [secPt_false, transform_split, ih w' hw', ih w' hw', transform_split]
      rfl
    · rw [secPt_true, sec_true_transform]
      apply congrArg (fun F => transform F a); funext x; rw [secFun_true]

theorem sec_total : ∀ (n : Nat) (w : W (n+1)), w ≠ zero (n+1) →
    ∀ (c : Bool) (F : W (n+1) → Int),
      total (n+1) (fun a => if dot (n+1) w a = c then F a else 0) =
        total n (fun a => F (secPt n w c a)) := by
  have tcase (n : Nat) (w' : W n) (c : Bool) (F : W (n+1) → Int) :
      total (n+1) (fun a => if dot (n+1) (true, w') a = c then F a else 0) =
        total n (fun a => F (secPt n (true, w') c a)) := by
    show total n _ + total n _ = _
    rw [← total_add]
    apply congrArg (total n); funext a
    rw [secPt_true]
    simp only [dot, Bool.true_and]
    cases dot n w' a <;> cases c <;> simp
  intro n
  induction n with
  | zero =>
    intro w hw c F
    rcases w with ⟨b, w'⟩
    cases b
    · exact absurd rfl hw
    · exact tcase 0 w' c F
  | succ m ih =>
    intro w hw c F
    rcases w with ⟨b, w'⟩
    cases b
    · have hw' : w' ≠ zero (m+1) := fun h => hw (by rw [h]; rfl)
      show total (m+1) _ + total (m+1) _ = total m _ + total m _
      have e (v : Bool) := ih w' hw' c (fun a => F (v, a))
      simp only [dot, Bool.false_and, Bool.false_xor] at e ⊢
      rw [e false, e true]
      rfl
    · exact tcase (m+1) w' c F

theorem secFun_bound : ∀ (n : Nat) (w : W (n+1)) (c : Bool) (U : W (n+1) → Int),
    (∀ x, -1 ≤ U x ∧ U x ≤ 1) → ∀ a, -2 ≤ secFun n w c U a ∧ secFun n w c U a ≤ 2 := by
  have tcase (n : Nat) (w' : W n) (c : Bool) (U : W (n+1) → Int)
      (hU : ∀ x, -1 ≤ U x ∧ U x ≤ 1) (a : W n) :
      -2 ≤ secFun n (true, w') c U a ∧ secFun n (true, w') c U a ≤ 2 := by
    rw [secFun_true]
    have h1 := hU (false, a); have h2 := hU (true, add n w' a)
    cases c <;> simp only [sign, Bool.false_eq_true, if_false, if_true] <;>
      exact ⟨by omega, by omega⟩
  intro n
  induction n with
  | zero =>
    intro w c U hU a
    rcases w with ⟨b, w'⟩
    cases b
    · show -2 ≤ (0 : Int) ∧ (0 : Int) ≤ 2; decide
    · exact tcase 0 w' c U hU a
  | succ m ih =>
    intro w c U hU a
    rcases w with ⟨b, w'⟩
    cases b
    · rcases a with ⟨a1, a2⟩
      rw [secFun_false]
      exact ih w' c _ (fun y => hU (a1, y)) a2
    · exact tcase (m+1) w' c U hU a

/-- Folding preserves the total modulo two. -/
theorem secFun_total : ∀ (n : Nat) (w : W (n+1)), w ≠ zero (n+1) →
    ∀ (c : Bool) (U : W (n+1) → Int), ∃ k : Int,
      total n (secFun n w c U) = total (n+1) U + 2 * k := by
  have tcase (n : Nat) (w' : W n) (c : Bool) (U : W (n+1) → Int) : ∃ k : Int,
      total n (secFun n (true, w') c U) = total (n+1) U + 2 * k := by
    have e : secFun n (true, w') c U = fun x => U (false, x) + sign c * U (true, add n w' x) := by
      funext x; exact secFun_true n w' c U x
    rw [e, total_add, total_scale, sum_shift n w' (fun x => U (true, x))]
    show ∃ k : Int, _ = total n (fun x => U (false, x)) + total n (fun x => U (true, x)) + 2 * k
    cases c
    · exact ⟨0, by simp [sign]⟩
    · exact ⟨-total n (fun x => U (true, x)), by simp only [sign, if_true]; omega⟩
  intro n
  induction n with
  | zero =>
    intro w hw c U
    rcases w with ⟨b, w'⟩
    cases b
    · exact absurd rfl hw
    · exact tcase 0 w' c U
  | succ m ih =>
    intro w hw c U
    rcases w with ⟨b, w'⟩
    cases b
    · have hw' : w' ≠ zero (m+1) := fun h => hw (by rw [h]; rfl)
      obtain ⟨k0, h0⟩ := ih w' hw' c (fun y => U (false, y))
      obtain ⟨k1, h1⟩ := ih w' hw' c (fun y => U (true, y))
      refine ⟨k0 + k1, ?_⟩
      show total m _ + total m _ = total (m+1) _ + total (m+1) _ + _
      have e0 : (fun x => secFun (m+1) (false, w') c U (false, x)) =
          secFun m w' c (fun y => U (false, y)) := rfl
      have e1 : (fun x => secFun (m+1) (false, w') c U (true, x)) =
          secFun m w' c (fun y => U (true, y)) := rfl
      rw [e0, e1, h0, h1]; omega
    · exact tcase (m+1) w' c U

end Balanced242Hyperplane

#print axioms Balanced242Hyperplane.sec_transform
#print axioms Balanced242Hyperplane.sec_total
#print axioms Balanced242Hyperplane.secFun_bound
#print axioms Balanced242Hyperplane.secFun_total
