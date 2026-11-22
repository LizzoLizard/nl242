/-
  Linear coordinate change to the adapted support-XOR axis for nine-variable Boolean functions.

  For any nonzero vector `s : W (n+1)`, a single F2-linear transvection `T = transv (n+1) u w`
  (with `dot (n+1) w u = false`) is an involution on `W (n+1)` with transpose `transv (n+1) w u`
  mapping `(true, zero n)` to `s`. Composing a balanced nine-variable function `F : W 9 → Bool`
  having `supportXor F ≠ zero 9` (which holds whenever some Walsh coefficient has magnitude 28)
  with `T` yields halves `f, g : Half` in adapted coordinates (`supportXor (halves f g) = (true, zero 8)`)
  preserving balance, the Walsh cap `|W| ≤ 28`, and the canonical agreement count along `supportXor F`.
-/
import Balanced242Hyperplane

namespace Balanced242Coord
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Blocks Balanced242Support Balanced242Hyperplane

/-- F2-linear transvection `x ↦ x + (w · x) u`. When `w · u = 0`, it is an involution. -/
def transv (n : Nat) (u w x : W n) : W n :=
  if dot n w x then add n u x else x

theorem transv_dot_self (n : Nat) (u w x : W n) (hu : dot n w u = false) :
    dot n w (transv n u w x) = dot n w x := by
  unfold transv
  cases hx : dot n w x
  · simp [hx]
  · simp [dot_right, hu, hx]

theorem transv_invol (n : Nat) (u w x : W n) (hu : dot n w u = false) :
    transv n u w (transv n u w x) = x := by
  change (if dot n w (transv n u w x) then add n u (transv n u w x) else transv n u w x) = x
  rw [transv_dot_self n u w x hu]
  unfold transv
  cases hx : dot n w x
  · simp
  · simp [add_cancel]

theorem transv_add (n : Nat) (u w x y : W n) :
    transv n u w (add n x y) = add n (transv n u w x) (transv n u w y) := by
  unfold transv
  rw [dot_right]
  cases dot n w x <;> cases dot n w y
  · rfl
  · simp only [Bool.xor_false, Bool.false_xor, Bool.false_eq_true, if_false, if_true]
    rw [add_comm n x (add n u y), add_assoc', add_comm n y x]
  · simp only [Bool.xor_false, Bool.false_xor, Bool.false_eq_true, if_false, if_true]
    exact (add_assoc' n u x y).symm
  · simp only [Bool.xor_self, Bool.false_eq_true, if_false, if_true]
    rw [add_assoc', add_comm n x (add n u y), add_assoc', add_cancel, add_comm n y x]

theorem transv_dot (n : Nat) (u w a x : W n) :
    dot n a (transv n u w x) = dot n (transv n w u a) x := by
  unfold transv
  cases hx : dot n w x <;> cases ha : dot n u a
  · simp
  · simp [dot_add, hx]
  · simp [dot_right, dot_comm n a u, ha]
  · simp [dot_right, dot_add, dot_comm n a u, ha, hx]

theorem transform_transv (n : Nat) (u w : W n) (hu : dot n w u = false)
    (G : W n → Int) (a : W n) :
    transform (fun x => G (transv n u w x)) a = transform G (transv n w u a) := by
  unfold transform
  have step (x : W n) : G (transv n u w x) * chr a x =
      G (transv n u w x) * chr (transv n w u a) (transv n u w x) := by
    simp only [chr]
    rw [transv_dot n u w (transv n w u a) x]
    have hwt : dot n u w = false := by rw [dot_comm]; exact hu
    rw [transv_invol n w u a hwt]
  simp only [step]
  exact reindex (transv n u w) (transv n u w)
    (fun x => transv_invol n u w x hu) (fun x => transv_invol n u w x hu)
    (fun y => G y * chr (transv n w u a) y)

/-- Every nonzero vector `s : W (n+1)` is the image of `(true, zero n)` under a single
involution transvection. -/
theorem exists_transv_axis (n : Nat) (s : W (n+1)) (hs : s ≠ zero (n+1)) :
    ∃ u w : W (n+1), dot (n+1) w u = false ∧ transv (n+1) u w (true, zero n) = s := by
  let e : W (n+1) := (true, zero n)
  let u : W (n+1) := add (n+1) e s
  have hcancel : add (n+1) u e = s := by
    dsimp only [u]
    rw [add_comm (n+1) e s, add_assoc', add_self, add_comm (n+1) s (zero (n+1)), add_zero_left]
  rcases s with ⟨b, v⟩
  cases b with
  | true =>
    refine ⟨u, e, ?_, ?_⟩
    · change xor (true && xor true true) (dot n (zero n) (add n (zero n) v)) = false
      simp [dot_zero]
    · unfold transv
      have hwe : dot (n+1) e e = true := by
        change xor (true && true) (dot n (zero n) (zero n)) = true
        simp [dot_zero]
      rw [hwe]; simp only [if_true]; exact hcancel
  | false =>
    have hv : v ≠ zero n := fun h => hs (by rw [h]; rfl)
    obtain ⟨w', _, hsep⟩ := separating_wire n v (zero n) hv
    rw [dot_zero_right] at hsep
    have hwv : dot n w' v = true := by cases h : dot n w' v <;> simp_all
    let w : W (n+1) := (true, w')
    refine ⟨u, w, ?_, ?_⟩
    · change xor (true && xor true false) (dot n w' (add n (zero n) v)) = false
      rw [add_zero_left, hwv]; rfl
    · unfold transv
      have hwe : dot (n+1) w e = true := by
        change xor (true && true) (dot n w' (zero n)) = true
        rw [dot_zero_right]; rfl
      rw [hwe]; simp only [if_true]; exact hcancel

/-- Twice the agreement count along the canonical axis `supportXor F`. -/
def axisAgreements (F : W 9 → Bool) : Int :=
  total 9 (fun x => if F x == F (add 9 (supportXor F) x) then 1 else 0)

/-- Unnormalized autocorrelation of `F` in direction `d`. -/
def autocorr (F : W 9 → Bool) (d : W 9) : Int :=
  total 9 (fun x => sign (F x) * sign (F (add 9 d x)))

theorem autocorr_eq_axisAgreements (F : W 9 → Bool) :
    autocorr F (supportXor F) = 2 * axisAgreements F - 512 := by
  unfold autocorr axisAgreements
  have pt (x : W 9) : sign (F x) * sign (F (add 9 (supportXor F) x)) =
      2 * (if F x == F (add 9 (supportXor F) x) then (1 : Int) else 0) - 1 := by
    cases F x <;> cases F (add 9 (supportXor F) x) <;> decide
  simp only [pt, total_sub, total_scale, total_const]
  change _ = 2 * _ - 512
  have h512 : many 9 * (1 : Int) = 512 := by decide
  rw [h512]

/-- A balanced nine-variable function with a Walsh coefficient of magnitude 28 (nonlinearity 242)
necessarily has nonzero `supportXor`. -/
theorem supportXor_ne_zero_of_peak28 (F : W 9 → Bool)
    (bal : total 9 (fun x => sign (F x)) = 0)
    (peak : ∃ a, (booleanSpec F a).natAbs = 28) :
    supportXor F ≠ zero 9 := by
  intro hz
  obtain ⟨a, ha⟩ := peak
  have hres := balanced_residue F bal a
  rw [hz, dot_zero_right] at hres
  change booleanSpec F a % 8 = 0 at hres
  omega

/-- Coordinate change to adapted halves: any balanced nine-variable function with nonzero
`supportXor` is linearly equivalent to `halves f g` with `supportXor (halves f g) = (true, zero 8)`,
same balance, permuted Walsh spectrum (hence same cap `≤ 28`), and `2 * agreements f g = axisAgreements F`. -/
theorem to_adapted (F : W 9 → Bool)
    (bal : total 9 (fun x => sign (F x)) = 0)
    (hs : supportXor F ≠ zero 9) :
    ∃ f g : Half,
      supportXor (halves f g) = (true, zero 8) ∧
      total 9 (fun x => sign (halves f g x)) = 0 ∧
      (∀ a, ∃ b, lo f g a = booleanSpec F b) ∧
      (∀ a, ∃ b, hi f g a = booleanSpec F b) ∧
      2 * agreements f g = axisAgreements F := by
  obtain ⟨u, w, hu, himg⟩ := exists_transv_axis 8 (supportXor F) hs
  let T : W 9 → W 9 := transv 9 u w
  let Tt : W 9 → W 9 := transv 9 w u
  have hT_invol : ∀ x, T (T x) = x := fun x => transv_invol 9 u w x hu
  let F' : W 9 → Bool := fun x => F (T x)
  let f : Half := fun x => F' (false, x)
  let g : Half := fun x => F' (true, x)
  have hfg : halves f g = F' := by
    funext x; rcases x with ⟨b, y⟩; cases b <;> rfl
  have hbal' : total 9 (fun x => sign (F' x)) = 0 := by
    have h := reindex T T hT_invol hT_invol (fun y => sign (F y))
    simpa [F', T, bal] using h
  have hspec (a : W 9) : booleanSpec F' a = booleanSpec F (Tt a) :=
    transform_transv 9 u w hu (fun y => sign (F y)) a
  have haxis : supportXor F' = (true, zero 8) := by
    apply dot_ext 9
    intro a
    rw [dot_comm 9 _ a, dot_comm 9 (true, zero 8) a]
    have r1 := balanced_residue F' hbal' a
    have r2 := balanced_residue F bal (Tt a)
    change booleanSpec F' a % 8 = _ at r1
    change booleanSpec F (Tt a) % 8 = _ at r2
    rw [hspec a] at r1
    have hbit : (if dot 9 a (supportXor F') then (1 : Int) else 0) =
        (if dot 9 (Tt a) (supportXor F) then (1 : Int) else 0) := by
      have hEq : 4 * (if dot 9 a (supportXor F') then (1 : Int) else 0) =
          4 * (if dot 9 (Tt a) (supportXor F) then (1 : Int) else 0) := r1.symm.trans r2
      omega
    have hdot : dot 9 (Tt a) (supportXor F) = dot 9 a (true, zero 8) := by
      have hTs : T (supportXor F) = (true, zero 8) := by rw [← himg]; exact hT_invol (true, zero 8)
      rw [← hTs]; exact (transv_dot 9 u w a (supportXor F)).symm
    rw [hdot] at hbit
    cases h1 : dot 9 a (supportXor F') <;> cases h2 : dot 9 a (true, zero 8) <;>
      simp_all
  have hlo (a : W 8) : lo f g a = booleanSpec F (Tt (false, a)) := by
    have ht := head_transform (fun x => sign (F' x)) false a
    have hl : lo f g a = transform (fun x => sign (F' x)) (false, a) := by
      rw [ht]; simp [lo, spec, f, g]
    rw [hl]; exact hspec (false, a)
  have hhi (a : W 8) : hi f g a = booleanSpec F (Tt (true, a)) := by
    have ht := head_transform (fun x => sign (F' x)) true a
    have hh : hi f g a = transform (fun x => sign (F' x)) (true, a) := by
      rw [ht]; simp [hi, spec, f, g, Int.sub_eq_add_neg]
    rw [hh]; exact hspec (true, a)
  have hag : 2 * agreements f g = axisAgreements F := by
    have hstep (x : W 9) :
        (if F' x == F' (add 9 (true, zero 8) x) then (1 : Int) else 0) =
        (if F (T x) == F (add 9 (supportXor F) (T x)) then (1 : Int) else 0) := by
      have hadd : T (add 9 (true, zero 8) x) = add 9 (supportXor F) (T x) := by
        change transv 9 u w (add 9 (true, zero 8) x) = add 9 (supportXor F) (transv 9 u w x)
        rw [transv_add, himg]
      simp only [F', hadd]
    have hre := reindex T T hT_invol hT_invol
      (fun y => if F y == F (add 9 (supportXor F) y) then (1 : Int) else 0)
    have hsum : total 9 (fun x => if F' x == F' (add 9 (true, zero 8) x) then (1 : Int) else 0) =
        axisAgreements F := by
      rw [funext hstep]; exact hre
    have hsplit : total 9 (fun x => if F' x == F' (add 9 (true, zero 8) x) then (1 : Int) else 0) =
        2 * agreements f g := by
      rw [total]
      have hL (y : W 8) :
          (if F' (false, y) == F' (add 9 (true, zero 8) (false, y)) then (1 : Int) else 0) =
          sameBit false (f y) (g y) + sameBit true (f y) (g y) := by
        have hadd : add 9 (true, zero 8) (false, y) = (true, y) := by
          change (xor true false, add 8 (zero 8) y) = (true, y)
          rw [add_zero_left]; rfl
        rw [hadd]
        change (if f y == g y then (1 : Int) else 0) = _
        cases f y <;> cases g y <;> rfl
      have hR (y : W 8) :
          (if F' (true, y) == F' (add 9 (true, zero 8) (true, y)) then (1 : Int) else 0) =
          sameBit false (f y) (g y) + sameBit true (f y) (g y) := by
        have hadd : add 9 (true, zero 8) (true, y) = (false, y) := by
          change (xor true true, add 8 (zero 8) y) = (false, y)
          rw [add_zero_left]; rfl
        rw [hadd]
        change (if g y == f y then (1 : Int) else 0) = _
        cases f y <;> cases g y <;> rfl
      simp only [hL, hR, total_add]
      unfold agreements countPair
      omega
    omega
  refine ⟨f, g, ?_, ?_, ?_, ?_, hag⟩
  · rw [hfg]; exact haxis
  · rw [hfg]; exact hbal'
  · intro a; exact ⟨Tt (false, a), hlo a⟩
  · intro a; exact ⟨Tt (true, a), hhi a⟩

end Balanced242Coord

#print axioms Balanced242Coord.to_adapted
#print axioms Balanced242Coord.supportXor_ne_zero_of_peak28
