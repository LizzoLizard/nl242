import Balanced242Endpoint

namespace Balanced242HighSections
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
  Balanced242Parents Balanced242Blocks Balanced242Support

private def disagreement (f g : Half) (x : W 8) : Int :=
  if f x = g x then 0 else sign (f x)

private theorem hi_disagreement (f g : Half) (a : W 8) :
    hi f g a = 2 * transform (disagreement f g) a := by
  have point (x : W 8) : sign (f x) - sign (g x) = 2 * disagreement f g x := by
    cases h : f x <;> cases j : g x <;> simp [disagreement,h,j,sign]
  unfold hi spec transform
  rw [←total_sub,←total_scale]
  apply congrArg (total 8); funext x
  rw [←Int.sub_mul,point,Int.mul_assoc]

private def projectSign (F : W n → Int) (b d x : W n) :=
  F x + chr b d * F (add n d x)

private theorem twice_add (n : Nat) (d x : W n) : add n d (add n d x) = x := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rcases d with ⟨d,ds⟩; rcases x with ⟨x,xs⟩
    cases d <;> cases x <;> simp [add,ih]

private theorem project_spec (F : W n → Int) (b d a : W n) :
    transform (projectSign F b d) a = (1 + chr b d * chr a d) * transform F a := by
  have shift := sum_shift n d (fun x => F (add n d x) * chr a x)
  simp only [twice_add,chr,dot_right,signMul] at shift
  have assoc (x : W n) : F x * (sign (dot n a d) * sign (dot n a x)) =
      chr a d * (F x * chr a x) := by unfold chr; ac_rfl
  simp only [assoc,total_scale] at shift
  change chr a d * total n (fun x => F x * chr a x) = total n (fun x => F (add n d x) * chr a x) at shift
  simp only [transform,projectSign,Int.add_mul,Int.mul_assoc,total_add,total_scale,
    Int.one_mul,←shift]

private theorem total_mod_zero (F : W n → Int) (h : ∀ a, 7 ∣ F a) : 7 ∣ total n F := by
  induction n with
  | zero => exact h ()
  | succ k ih => exact Int.dvd_add (ih _ (fun x => h (false,x))) (ih _ (fun x => h (true,x)))

/-- Every nonempty affine slice given by two frequency tests meets the
high coefficients that are nonzero modulo seven. The two tests may repeat. -/
theorem exception_on_intersection (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (b d e : W 8) :
    ∃ a, dot 8 a d = dot 8 b d ∧ dot 8 a e = dot 8 b e ∧ hi f g a % 7 ≠ 0 := by
  apply Classical.byContradiction
  intro none
  let U := disagreement f g
  let D := projectSign (projectSign U b d) b e
  have td (a : W 8) : transform D a =
      (1+chr b e*chr a e)*((1+chr b d*chr a d)*transform U a) := by
    simp only [D,project_spec]
  have divisible (a : W 8) : 7 ∣ transform D a := by
    have gain (v : W 8) : 1 + chr b v * chr a v = (if dot 8 a v = dot 8 b v then 2 else 0) := by
      cases p : dot 8 b v <;> cases q : dot 8 a v <;> simp [chr,p,q,sign]
    rw [td,gain,gain]
    by_cases p : dot 8 a d = dot 8 b d <;> by_cases q : dot 8 a e = dot 8 b e
    · have h : hi f g a % 7 = 0 := Classical.byContradiction (fun n => none ⟨a,p,q,n⟩)
      have spec : hi f g a = 2 * transform U a := hi_disagreement f g a
      simp only [if_pos p,if_pos q]; omega
    all_goals simp [p,q]; decide
  have smallU (x : W 8) : -1 ≤ U x ∧ U x ≤ 1 := by
    cases h : f x <;> cases j : g x <;> simp [U,disagreement,h,j,sign]
  have bounds (F : W 8 → Int) (a v x : W 8) (k : Int)
      (range : ∀ z, -k ≤ F z ∧ F z ≤ k) :
      -(2*k) ≤ projectSign F a v x ∧ projectSign F a v x ≤ 2*k := by
    have h := range x; have j := range (add 8 v x)
    cases c : dot 8 a v <;> simp [projectSign,chr,c,sign] <;> omega
  have dead (x : W 8) : D x = 0 := by
    have k := total_mod_zero (fun a => transform D a * chr a x)
      (fun a => by obtain ⟨j,h⟩ := divisible a; exact ⟨j*chr a x,by change transform D a * chr a x = _; rw [h,Int.mul_assoc]⟩)
    rw [inversion] at k
    change 7 ∣ 256 * D x at k
    have small : -4 ≤ D x ∧ D x ≤ 4 := bounds _ _ _ _ 2 (fun z => bounds U b d z 1 smallU)
    omega
  have z : transform D b = 0 := by simp [transform,dead,total_zero]
  rw [td] at z
  have h := hi_disagreement f g b
  change hi f g b = 2*transform U b at h
  have r := res b
  cases hd : dot 8 b d <;> cases he : dot 8 b e <;> simp [chr,hd,he,sign] at z <;> omega

/-- Up to a linear character and the DC offset, the two blocks have the
same sign phase modulo sixteen. This applies to arbitrary Boolean halves. -/
theorem coupled_phase (f g : Half) (a : W 8) :
    (hi f g a - hi f g (zero 8)) % 16 =
      (lo f g a - lo f g (zero 8) + 8 * (if dot 8 a (supportXor g) then 1 else 0)) % 16 := by
  have h := walsh_residue_offset g (by decide) a
  have dc : spec g (zero 8) = total 8 (fun x => sign (g x)) := by
    simp [spec,transform,chr,dot_zero,sign]
  change spec g a % 8 = _ at h
  rw [← dc] at h
  unfold hi lo
  cases hd : dot 8 a (supportXor g) <;> simp only [hd] at * <;> omega

/-- Complementary signed input tables are equivalent to two Boolean halves. -/
def complementary (v u : Int) : Prop :=
  (v = 0 ∧ (u = 1 ∨ u = -1)) ∨ (u = 0 ∧ (v = 1 ∨ v = -1))

private theorem switch_site (v u b eps : Int) (src : complementary v u)
    (unit : b = 1 ∨ b = -1) (es : eps = 1 ∨ eps = -1)
    (orient : u * b ≤ 0) (cancel : u = 0 → v = -eps) :
    complementary (v + eps) (u + b) := by
  rcases src with ⟨h,k|k⟩ | ⟨h,k|k⟩ <;> rcases unit with h₁|h₁ <;>
    rcases es with h₂|h₂ <;> simp_all [complementary]

/-- Transfer occupancy on a plane. The high correction has spectrum twice a
sign. The low correction is zero off the residue flat and at most four on it.
The singleton cancellation hypothesis can be satisfied if at most one site
on the plane has u=0. All final Walsh coefficients are bounded by 24. -/
theorem plane_switch (V U P S : W 8 → Int) (eps : Int)
    (es : eps = 1 ∨ eps = -1) (src : ∀ x, complementary (V x) (U x))
    (sites : ∀ x, (P x = 0 ∧ S x = 0) ∨
      (P x = 1 ∧ (S x = 1 ∨ S x = -1) ∧ U x * S x ≤ 0 ∧ (U x = 0 → V x = -eps)))
    (low : ∀ a, (transform V a).natAbs ≤ 12 ∧
      (transform P a = 0 ∨ ((transform V a).natAbs ≤ 8 ∧ (transform P a).natAbs ≤ 4)))
    (high : ∀ a, ∃ q h : Int, (q = 1 ∨ q = -1) ∧
      (h = 1 ∨ h = -3 ∨ h = 5 ∨ h = -7) ∧
      transform U a = 2*q*h ∧ transform S a = 2*q) :
    ∃ f g : Half, ∀ a, (lo f g a).natAbs ≤ 24 ∧ (hi f g a).natAbs ≤ 24 := by
  let v (x : W 8) := V x + eps * P x
  let u (x : W 8) := U x + S x
  have comp (x : W 8) : complementary (v x) (u x) := by
    rcases sites x with ⟨p,s⟩ | ⟨p,b,h,c⟩
    · simpa [v,u,p,s] using src x
    · simpa [v,u,p] using switch_site _ _ _ _ (src x) b es h c
  let f (x : W 8) := decide (v x + u x < 0)
  let g (x : W 8) := decide (v x - u x < 0)
  have sums (x : W 8) : sign (f x) + sign (g x) = 2*v x ∧
      sign (f x) - sign (g x) = 2*u x := by
    rcases comp x with ⟨p,h|h⟩ | ⟨p,h|h⟩ <;> simp [f,g,p,h,sign]
  refine ⟨f,g,?_⟩
  intro a
  have l : lo f g a = 2*(transform V a + eps*transform P a) := by
    calc
      _ = total 8 (fun x => (sign (f x) + sign (g x)) * chr a x) := by
        simp only [lo,spec,transform,Int.add_mul,total_add]
      _ = _ := by
        simp only [(sums _).1,v,Int.mul_assoc,Int.add_mul,total_add,total_scale,transform]
  have r : hi f g a = 2*(transform U a + transform S a) := by
    unfold hi spec transform
    rw [←total_sub]
    simp only [←Int.sub_mul,(sums _).2,u,Int.mul_assoc,Int.add_mul,total_add,total_scale]
  rw [l,r]
  constructor
  · obtain ⟨b,p|⟨j,k⟩⟩ := low a
    · simp only [p,Int.mul_zero,Int.add_zero]; omega
    · rcases es with e|e <;> rw [e] <;> omega
  · obtain ⟨q,h,qval,hval,j,k⟩ := high a
    rw [j,k]
    rcases qval with e|e <;> rcases hval with d|d|d|d <;> rw [e,d] <;> decide

#print axioms plane_switch
#print axioms coupled_phase
#print axioms exception_on_intersection
end Balanced242HighSections
