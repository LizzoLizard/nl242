import Balanced242Support

namespace Balanced242Sectors
open FrozenShells CandyKnots CollisionLaw MaskRecovery SilentRoom Balanced242Parents
  Balanced242Blocks Balanced242Support

def smallIn (f g : Half) (d : W 8) (a : W 8) : Int :=
  if dot 8 a d && decide ((lo f g a).natAbs = 8) then 1 else 0

/-- One occupied input in an unordered pair around d. Counting its occupied
end counts each such pair once. -/
def singlePairs (f g : Half) (d : W 8) : Int :=
  total 8 (fun x => if f x = g x ∧ f (add 8 d x) ≠ g (add 8 d x) then 1 else 0)

private def signedAgreement (a b : Bool) : Int := if a = b then sign a else 0

private theorem pair_squares (a b c e : Bool) :
    let z := signedAgreement a b - signedAgreement c e
    z*z = (if a = b ∧ c ≠ e then 1 else 0) + (if c = e ∧ a ≠ b then 1 else 0) +
      4*((if z = 2 then 1 else 0) + (if signedAgreement c e - signedAgreement a b = 2 then 1 else 0)) := by
  cases a <;> cases b <;> cases c <;> cases e <;> decide

private theorem sum_mod (m : Int) (F G : W n → Int) (h : ∀ a, F a % m = G a % m) :
    total n F % m = total n G % m := by
  induction n with
  | zero => exact h ()
  | succ n ih =>
    change (_+_) % m = (_+_) % m
    rw [Int.add_emod, ih _ _ (fun a => h (false,a)), ih _ _ (fun a => h (true,a)), ←Int.add_emod]

private theorem duality (D B : W n → Int) :
    total n (fun x => D x * synth B x) = total n (fun a => B a * transform D a) := by
  simp only [synth,transform,←total_scale]
  rw [swap]
  apply congrArg (total n); funext a
  apply congrArg (total n); funext x; ac_rfl

private theorem odd_bound (d t : Int) (odd : t % 2 = 1) (red : (d+t)%3 = 0) :
    9 - t*t + 4*(d*t) ≤ 4*(d*d) := by
  let z := 2*d-t
  have wide : z ≤ -3 ∨ 3 ≤ z := by dsimp [z]; omega
  have positive (y : Int) (h : 3 ≤ y) : 9 ≤ y*y := by
    have hh := Int.mul_le_mul_of_nonneg_right h (show 0 ≤ y by omega)
    have k := Int.mul_le_mul_of_nonneg_left h (show (0:Int) ≤ 3 by decide); omega
  have square : 9 ≤ z*z := by
    rcases wide with h|h
    · have hh := positive (-z) (by omega)
      rwa [Int.neg_mul_neg] at hh
    · exact positive z h
  have expand : z*z = 4*(d*d) - 4*(d*t) + t*t := by
    have k : (2*d)*(2*d) = 4*(d*d) := by change _ = (2*2)*(d*d); ac_rfl
    have l : t*(2*d) = 2*(d*t) := by ac_rfl
    have r : (2*d)*t = 2*(d*t) := by ac_rfl
    simp only [z,Int.sub_mul,Int.mul_sub,k,l,r]; omega
  omega

private theorem even_identity (d t : Int) (hd : -2 ≤ d ∧ d ≤ 2)
    (ht : -2 ≤ t ∧ t ≤ 2) (p : t%2=0) (h : (d+t)%3=0) :
    2*(d*d) = t*t-d*t := by
  have vals : t = -2 ∨ t = 0 ∨ t = 2 := by omega
  rcases vals with rfl|rfl|rfl <;>
    have vals : d = -2 ∨ d = -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 := by omega
  all_goals rcases vals with rfl|rfl|rfl|rfl|rfl <;> first | decide | (exfalso; exact (by decide : ¬_) h)

/-- On a linear half-space of frequencies with magnitudes 8 and 24 only,
the number m of magnitude-8 coefficients is four or at least six. -/
theorem halfspace_small_counts (f g : Half) (d : W 8) (nz : d ≠ zero 8)
    (levels : ∀ a, dot 8 a d = true → (lo f g a).natAbs = 8 ∨ (lo f g a).natAbs = 24) :
    let m := total 8 (smallIn f g d)
    4 ≤ m ∧ (m % 2 = 1 → 7 ≤ m) ∧ (m + singlePairs f g d) % 4 = 0 := by
  let V (x : W 8) : Int := if f x = g x then sign (f x) else 0
  have twice (x : W 8) : pairSign f g x = 2*V x := by
    cases h : f x <;> cases j : g x <;> simp [V,pairSign,h,j,sign]
  have L (a : W 8) : lo f g a = 2*transform V a := by
    rw [lo_transform]; simp only [transform,twice,Int.mul_assoc,total_scale]
  let D (x : W 8) := V x - V (add 8 d x)
  let S := transform D
  have twiceD (x : W 8) : add 8 d (add 8 d x) = x := by
    have h (n : Nat) (d x : W n) : add n d (add n d x) = x := by
      induction n with
      | zero => rfl
      | succ n ih => rcases x with ⟨b,x⟩; simp [add,ih]
    exact h _ _ _
  have spectra (a : W 8) : S a = if dot 8 a d then lo f g a else 0 := by
    have shift := sum_shift 8 d (fun x => V (add 8 d x) * chr a x)
    simp only [twiceD,chr,dot_right,signMul] at shift
    have factor (x : W 8) : V x * (sign (dot 8 a d) * sign (dot 8 a x)) =
        sign (dot 8 a d) * (V x * sign (dot 8 a x)) := by ac_rfl
    simp only [factor,total_scale] at shift
    simp only [S,D,transform,Int.sub_mul,total_sub,chr,L,←shift]
    cases h : dot 8 a d <;> simp [sign,h] <;> omega
  let I := smallIn f g d
  let J (a : W 8) : Int := if dot 8 a d then 1 else 0
  let B (a : W 8) := if I a = 1 then S a / 8 else 0
  let T := synth B
  let m := total 8 I
  have vals (a : W 8) :
      (S a = 0 ∧ B a = 0 ∧ I a = 0 ∧ J a = 0) ∨
      ((S a = 24 ∨ S a = -24) ∧ B a = 0 ∧ I a = 0 ∧ J a = 1) ∨
      ((S a = 8 ∧ B a = 1 ∨ S a = -8 ∧ B a = -1) ∧ I a = 1 ∧ J a = 1) := by
    cases h : dot 8 a d with
    | false => simp [spectra,B,I,J,smallIn,h]
    | true =>
      have z := levels a h
      have vv : lo f g a = 8 ∨ lo f g a = -8 ∨ lo f g a = 24 ∨ lo f g a = -24 := by omega
      rcases vv with e|e|e|e <;> simp [B,I,J,smallIn,spectra,h,e]
  have moments (a : W 8) :
      S a * S a = 576*J a - 512*I a ∧ B a * B a = I a ∧ B a * S a = 8*I a := by
    rcases vals a with ⟨h,j,k,l⟩ | ⟨h|h,j,k,l⟩ | ⟨⟨h,j⟩|⟨h,j⟩,k,l⟩ <;> simp [h,j,k,l]
  have half : total 8 J = 128 := by
    have h := identity_spectrum 8 d
    change total 8 (chr d) = _ at h
    have bit (x : W 8) : chr d x = 1-2*J x := by
      simp only [chr,dot_comm 8 d x,J]; cases dot 8 x d <;> decide
    rw [funext bit,total_sub,total_const,total_scale] at h
    simp only [nz,if_false] at h; change 256*1 - 2*total 8 J = 0 at h; omega
  have dEnergy := parsevalInt 8 D
  change total 8 (fun a => S a * S a) = 256*total 8 (fun x => D x * D x) at dEnergy
  simp only [(moments _).1,total_sub,total_scale,half] at dEnergy
  have tSpec (x : W 8) : T x = transform B x := by
    simp only [T,synth,transform,chr,dot_comm 8 x]
  have tEnergy := parsevalInt 8 B
  simp only [←tSpec,(moments _).2.1] at tEnergy
  change total 8 (fun x => T x * T x) = 256*m at tEnergy
  have mixed := duality D B
  change total 8 (fun x => D x * T x) = total 8 (fun a => B a * S a) at mixed
  simp only [(moments _).2.2,total_scale] at mixed
  change total 8 (fun x => D x * T x) = 8*m at mixed
  change 576*128-512*m = 256*total 8 (fun x => D x * D x) at dEnergy
  let one (x : W 8) : Int := if f x = g x ∧ f (add 8 d x) ≠ g (add 8 d x) then 1 else 0
  let two (x : W 8) : Int := if D x = 2 then 1 else 0
  have pairMoment (x : W 8) : D x * D x = one x + one (add 8 d x) +
      4*(two x + two (add 8 d x)) := by
    simp only [two,D,one,twiceD,V]
    exact pair_squares (f x) (g x) (f (add 8 d x)) (g (add 8 d x))
  have both := congrArg (total 8) (funext pairMoment)
  simp only [total_add,total_scale,sum_shift] at both
  have modFour : (m + singlePairs f g d) % 4 = 0 := by
    change (m + total 8 one) % 4 = 0
    omega
  have dRange (x : W 8) : -2 ≤ D x ∧ D x ≤ 2 := by
    have rangeV (a : W 8) : V a = 0 ∨ V a = 1 ∨ V a = -1 := by
      cases h : f a <;> cases j : g a <;> simp [V,h,j,sign]
    have h := rangeV x; have j := rangeV (add 8 d x); dsimp only [D]; omega
  have term (a x : W 8) :
      -I a ≤ B a * chr a x ∧ B a * chr a x ≤ I a ∧
      (B a * chr a x)%2 = I a%2 ∧ (S a * chr a x)%3 = (-B a * chr a x)%3 := by
    rcases vals a with ⟨h,j,k,l⟩ | ⟨h|h,j,k,l⟩ | ⟨⟨h,j⟩|⟨h,j⟩,k,l⟩ <;>
      cases e : dot 8 a x <;> simp [chr,sign,h,j,k,e]
  have atX (x : W 8) : -m ≤ T x ∧ T x ≤ m ∧ T x % 2 = m % 2 ∧ (D x + T x)%3 = 0 := by
    have lower := total_mono 8 _ _ (fun a => (term a x).1)
    have upper := total_mono 8 _ _ (fun a => (term a x).2.1)
    have par := sum_mod 2 _ _ (fun a => (term a x).2.2.1)
    have red := sum_mod 3 _ _ (fun a => (term a x).2.2.2)
    have inv := inversion D x
    change total 8 (fun a => S a * chr a x) = 256*D x at inv
    have neg (a : W 8) : -B a * chr a x = -1*(B a*chr a x) := by rw [Int.neg_mul]; omega
    simp only [neg,total_scale,inv] at red
    have minus (a : W 8) : -I a = -1*I a := by omega
    simp only [minus,total_scale] at lower
    change -1*m ≤ T x at lower
    change T x ≤ m at upper
    change T x % 2 = m % 2 at par
    change 256*D x % 3 = (-1*T x) % 3 at red
    exact ⟨by omega,upper,par,by omega⟩
  have oddLarge (odd : m%2=1) : 7 ≤ m := by
    have pt (x : W 8) := odd_bound (D x) (T x) ((atX x).2.2.1.trans odd) (atX x).2.2.2
    have h := total_mono 8 _ _ pt
    simp only [total_scale,total_add,total_sub,total_const,tEnergy,mixed] at h
    change 256*9 - 256*m + 4*(8*m) ≤ _ at h; omega
  refine ⟨?_,oddLarge,modFour⟩
  change 4 ≤ m
  by_cases few : m ≤ 3
  · by_cases even : m%2=0
    · have pt (x : W 8) := even_identity (D x) (T x) (dRange x)
          (by have h := atX x; omega) ((atX x).2.2.1.trans even) (atX x).2.2.2
      have h := congrArg (total 8) (funext pt)
      simp only [total_scale,total_sub,tEnergy,mixed] at h; omega
    · have h := oddLarge (by omega); omega
  · omega

#print axioms halfspace_small_counts
end Balanced242Sectors
