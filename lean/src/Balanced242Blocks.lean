import Balanced242Parents

/-! Integer finite differences of the two Walsh blocks, and an obstruction
when the two halves agree precisely on a codimension-two affine flat.
For the latter, coordinates put the flat at (0,0) × F₂⁶. -/
namespace Balanced242Blocks
open FrozenShells CandyKnots CollisionLaw SilentRoom Balanced242Parents

def differences {n : Nat} : List (W n) → (W n → Int) → W n → Int
  | [], F, a => F a
  | p :: ps, F, a => differences ps (fun b => F (add n p b) - F b) a

theorem diff_scale (ps : List (W n)) (k : Int) (F : W n → Int) (a : W n) :
    differences ps (fun b => k * F b) a = k * differences ps F a := by
  induction ps generalizing F with
  | nil => rfl
  | cons p ps ih => simp only [differences, ← Int.mul_sub, ih]

theorem diff_sub (ps : List (W n)) (F G : W n → Int) (a : W n) :
    differences ps (fun b => F b - G b) a = differences ps F a - differences ps G a := by
  induction ps generalizing F G with
  | nil => rfl
  | cons p ps ih =>
    simp only [differences]
    have e (b : W n) : (F (add n p b) - G (add n p b)) - (F b - G b) =
        (F (add n p b) - F b) - (G (add n p b) - G b) := by omega
    simp only [e,ih]

/-- Each mask difference restricts the input sum to one hyperplane and
supplies a factor of -2, even for integer-valued input tables. -/
theorem diff_transform_dvd (ps : List (W n)) (v : W n → Int) (a : W n) :
    (2:Int)^ps.length ∣ differences ps (transform v) a := by
  induction ps generalizing v with
  | nil => exact ⟨transform v a, by simp [differences]⟩
  | cons p ps ih =>
    let u (x : W n) := if dot n p x then v x else 0
    have e (b : W n) : transform v (add n p b) - transform v b = -2 * transform u b := by
      simp only [transform, ← total_sub, ← total_scale]
      apply congrArg (total n); funext x
      simp only [chr,dot_add,signMul]
      cases h : dot n p x <;> simp [u,h,sign] <;> omega
    obtain ⟨z,hz⟩ := ih u
    refine ⟨-z,?_⟩
    rw [differences,funext e,diff_scale,hz,List.length_cons,Int.pow_succ]
    simp [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]

def booleanSpec {n : Nat} (f : W n → Bool) : W n → Int := transform (fun x => sign (f x))
private def oneAtZero (n : Nat) (a : W n) : Int := if a = zero n then 1 else 0
private def occupied (f : W n → Bool) (x : W n) : Int := if f x then 1 else 0

private theorem spec_split (f : W n → Bool) (a : W n) :
    booleanSpec f a = many n * oneAtZero n a - 2 * transform (occupied f) a := by
  have e (x : W n) : sign (f x) = 1 - 2 * occupied f x := by cases h : f x <;> simp [sign,occupied,h]
  have flat := identity_spectrum n a
  change total n (chr a) = _ at flat
  simp only [booleanSpec,transform,e,Int.sub_mul,Int.one_mul,Int.mul_assoc,total_sub,total_scale,flat]
  by_cases z : a = zero n <;> simp [oneAtZero,z]

/-- The mod-32 third differences of the low and high blocks agree, for
all Boolean halves, all base masks, and arbitrary (even repeated) directions. -/
theorem shared_cubic_residue (f g : Half) (a p q r : W 8) :
    (32:Int) ∣ differences [p,q,r] (lo f g) a - differences [p,q,r] (hi f g) a := by
  let ds := [p,q,r]
  have e : (fun b => lo f g b - hi f g b) = fun b => 2 * booleanSpec g b := by
    funext b; change (_ + spec g b) - (_ - spec g b) = 2 * spec g b; omega
  change (32:Int) ∣ differences ds _ a - differences ds _ a
  rw [← diff_sub,e,diff_scale,funext (spec_split g),diff_sub,diff_scale,diff_scale]
  obtain ⟨z,h⟩ := diff_transform_dvd ds (occupied g) a
  change differences ds _ a = 8*z at h
  rw [h]
  change (32:Int) ∣ 2 * (256 * _ - 2 * (8*z))
  exact ⟨16 * differences ds (oneAtZero 8) a - z, by omega⟩

private def halfDifference (b c : Bool) : Int := if b = c then 0 else sign b
private def halfSum (b c : Bool) : Int := if b = c then sign b else 0

private theorem blocks_exact (f g : Half) (a : W 8) :
    lo f g a = 2 * transform (fun x => halfSum (f x) (g x)) a ∧
    hi f g a = 2 * transform (fun x => halfDifference (f x) (g x)) a := by
  have plus (b c : Bool) : sign b + sign c = 2 * halfSum b c := by cases b <;> cases c <;> decide
  have minus (b c : Bool) : sign b - sign c = 2 * halfDifference b c := by cases b <;> cases c <;> decide
  constructor
  · simp only [lo,spec,transform,← total_add,← Int.add_mul,plus,Int.mul_assoc,total_scale]
  · simp only [hi,spec,transform,← total_sub,← Int.sub_mul,minus,Int.mul_assoc,total_scale]

/-- Each block has vanishing fourth differences modulo 32. -/
theorem quartic_vanishes (f g : Half) (a p q r s : W 8) :
    (32:Int) ∣ differences [p,q,r,s] (lo f g) a ∧
    (32:Int) ∣ differences [p,q,r,s] (hi f g) a := by
  have dvd (u : W 8 → Int) : (32:Int) ∣ differences [p,q,r,s] (fun b => 2 * transform u b) a := by
    obtain ⟨z,h⟩ := diff_transform_dvd [p,q,r,s] u a
    change differences _ _ _ = 16*z at h
    exact ⟨z,by rw [diff_scale,h]; omega⟩
  rw [funext (fun a => (blocks_exact f g a).1),funext (fun a => (blocks_exact f g a).2)]
  exact ⟨dvd _,dvd _⟩

abbrev Slice := W 6 → Bool

private theorem energy (f : Slice) :
    total 6 (fun a => booleanSpec f a * booleanSpec f a) = 4096 := by
  have sq (x : W 6) : sign (f x) * sign (f x) = 1 := by cases f x <;> decide
  simp only [booleanSpec,parsevalInt,sq,total_const]; decide

private theorem slice_residue (f : Slice) :
    (∀ a, booleanSpec f a % 4 = 0) ∨ (∀ a, booleanSpec f a % 4 = 2) := by
  have zeroRight (n : Nat) (a : W n) : add n a (zero n) = a := by
    induction n with
    | zero => cases a; rfl
    | succ n ih => rcases a with ⟨b,a⟩; simp [add,zero,ih]
  have same (a : W 6) : booleanSpec f a % 4 = booleanSpec f (zero 6) % 4 := by
    obtain ⟨z,h⟩ := diff_transform_dvd [a] (occupied f) (zero 6)
    change transform _ (add 6 a (zero 6)) - transform _ (zero 6) = 2*z at h
    rw [zeroRight] at h
    rw [spec_split,spec_split]
    change (64*_ - 2*_) % 4 = (64*_ - 2*_) % 4
    omega
  have even : booleanSpec f (zero 6) % 2 = 0 := by rw [spec_split]; change (64*_ - 2*_) % 2 = 0; omega
  by_cases h : booleanSpec f (zero 6) % 4 = 0
  · exact Or.inl (fun a => (same a).trans h)
  · exact Or.inr (fun a => (same a).trans (by omega))

private theorem budgets (i j k : Nat) (cap : i+j+k ≤ 14) :
    (2 ≤ i → 6*(i*i)+8*(j*j)+8*(k*k) ≤ 1176) ∧
    (i ≤ 12 → j ≤ 12 → k ≤ 12 → i*i+j*j+k*k ≤ 168) := by
  have all : ∀ i j k : Fin 15, i.val+j.val+k.val ≤ 14 →
      (2 ≤ i.val → 6*(i.val*i.val)+8*(j.val*j.val)+8*(k.val*k.val) ≤ 1176) ∧
      (i.val ≤ 12 → j.val ≤ 12 → k.val ≤ 12 →
        i.val*i.val+j.val*j.val+k.val*k.val ≤ 168) := by decide
  exact all ⟨i,by omega⟩ ⟨j,by omega⟩ ⟨k,by omega⟩ cap

private theorem odd_impossible (A B C : Slice) (odd : ∀ a, booleanSpec A a % 4 = 2)
    (cap : ∀ a, (booleanSpec A a).natAbs + (booleanSpec B a).natAbs + (booleanSpec C a).natAbs ≤ 14) : False := by
  have pt (a : W 6) : 6*(booleanSpec A a * booleanSpec A a) +
      8*(booleanSpec B a * booleanSpec B a) + 8*(booleanSpec C a * booleanSpec C a) ≤ 1176 := by
    have lim := cap a
    have par := odd a
    have v := (budgets _ _ _ lim).1 (by omega)
    simpa only [Int.natCast_add,Int.natCast_mul,Int.natAbs_mul_self'] using (Int.ofNat_le.mpr v)
  have h := total_mono 6 _ _ pt
  simp only [total_add,total_scale,total_const,energy] at h
  change _ ≤ 64*1176 at h; omega

/-- Three six-bit Boolean spectra cannot fit a pointwise sum-of-magnitudes budget of 14. -/
theorem three_slices (A B C : Slice) :
    ¬ ∀ a, (booleanSpec A a).natAbs + (booleanSpec B a).natAbs + (booleanSpec C a).natAbs ≤ 14 := by
  intro cap
  rcases slice_residue A with evenA|oddA
  · rcases slice_residue B with evenB|oddB
    · rcases slice_residue C with evenC|oddC
      · have pt (a : W 6) : booleanSpec A a * booleanSpec A a + booleanSpec B a * booleanSpec B a +
            booleanSpec C a * booleanSpec C a ≤ 168 := by
          have lim := cap a
          have ea := evenA a; have eb := evenB a; have ec := evenC a
          have v := (budgets _ _ _ lim).2
            (by omega) (by omega) (by omega)
          simpa only [Int.natCast_add,Int.natCast_mul,Int.natAbs_mul_self'] using (Int.ofNat_le.mpr v)
        have h := total_mono 6 _ _ pt
        simp only [total_add,total_const,energy] at h
        change _ ≤ 64*168 at h; omega
      · exact odd_impossible C A B oddC (fun a => by have := cap a; omega)
    · exact odd_impossible B A C oddB (fun a => by have := cap a; omega)
  · exact odd_impossible A B C oddA cap

private theorem flat_hi_line (f g : Half)
    (flat : ∀ (b c : Bool) (u : W 6), f (b,c,u) = g (b,c,u) ↔ b = false ∧ c = false)
    (i j : Bool) (a : W 6) :
    hi f g (i,j,a) = 2*(sign j * booleanSpec (fun u => f (false,true,u)) a +
      sign i * booleanSpec (fun u => f (true,false,u)) a +
      (sign i * sign j) * booleanSpec (fun u => f (true,true,u)) a) := by
  have f00 (u : W 6) : halfDifference (f (false,false,u)) (g (false,false,u)) = 0 := by
    simp [halfDifference,(flat false false u).2 ⟨rfl,rfl⟩]
  have rest (b c : Bool) (u : W 6) (h : ¬(b = false ∧ c = false)) :
      halfDifference (f (b,c,u)) (g (b,c,u)) = sign (f (b,c,u)) := by
    have ne : f (b,c,u) ≠ g (b,c,u) := fun e => h ((flat b c u).1 e)
    exact if_neg ne
  rw [(blocks_exact ..).2,head_transform,head_transform,head_transform]
  simp only [f00,rest false true _ (by decide),rest true false _ (by decide),rest true true _ (by decide)]
  have z : transform (fun _ : W 6 => (0:Int)) a = 0 := by simp [transform,total_zero]
  cases i <;> cases j <;> simp [z,booleanSpec,sign] <;> omega

/-- Agreement on exactly one of the four cosets leaves three Boolean slices
in the high block. The two quotient-mask bits realize all four sign patterns
up to an overall sign. -/
theorem flat_agreement_obstruction (f g : Half)
    (flat : ∀ (b c : Bool) (u : W 6), f (b,c,u) = g (b,c,u) ↔ b = false ∧ c = false) :
    ¬ ∀ a, (hi f g a).natAbs ≤ 28 := by
  let A : Slice := fun u => f (false,true,u)
  let B : Slice := fun u => f (true,false,u)
  let C : Slice := fun u => f (true,true,u)
  intro bound
  apply three_slices A B C
  intro a
  have h₁ := bound (false,false,a); have h₂ := bound (false,true,a)
  have h₃ := bound (true,false,a); have h₄ := bound (true,true,a)
  rw [flat_hi_line f g flat] at h₁ h₂ h₃ h₄
  change (2 * (_ * booleanSpec A a + _ * booleanSpec B a + _ * booleanSpec C a)).natAbs ≤ 28 at h₁ h₂ h₃ h₄
  simp only [sign,Bool.false_eq_true,if_false,if_true,Int.one_mul,Int.neg_mul,
    Int.mul_one,Int.neg_neg] at h₁ h₂ h₃ h₄
  omega

/-- In the adapted coordinates the high block is 4 modulo 8, so breaking
28 forces a coefficient of magnitude at least 36. -/
theorem flat_forces_36 (f g : Half)
    (flat : ∀ (b c : Bool) (u : W 6), f (b,c,u) = g (b,c,u) ↔ b = false ∧ c = false)
    (axis : supportXor (halves f g) = (true,zero 8))
    (bal : total 9 (fun x => sign (halves f g x)) = 0) :
    ∃ a, 36 ≤ (hi f g a).natAbs := by
  classical
  apply Classical.byContradiction
  intro no
  apply flat_agreement_obstruction f g flat
  intro a
  have lt : ¬36 ≤ (hi f g a).natAbs := fun h => no ⟨a,h⟩
  have residue := (adapted_blocks f g axis bal a).2
  omega

/-- The six-bit inner product, with four zeros flipped to balance it. -/
def flatSign : Slice
  | (a,b,c,x,y,z,()) =>
    xor (xor (a && x) (xor (b && y) (c && z)))
        (!(x || y || z) && !((a && b) || (b && c) || (c && a)))

/-- A four-bit bent phase with two linear labels. Its three labels give
disjoint six-bit Walsh supports before the one-entry perturbation. -/
private def tagged (i j : Bool) : Slice
  | (a,b,c,d,x,y,()) => xor (xor (a && b) (c && d)) (xor (i && x) (j && y))

def witnessLeft : Half
  | (false,false,u) => flatSign u
  | (false,true,u) => xor (tagged false false u) (decide (u = zero 6))
  | (true,false,u) => tagged true false u
  | (true,true,u) => tagged false true u

def witnessRight (x : W 8) : Bool :=
  if x.1 || x.2.1 then !(witnessLeft x) else witnessLeft x

theorem witness_flat (b c : Bool) (u : W 6) :
    witnessLeft (b,c,u) = witnessRight (b,c,u) ↔ b = false ∧ c = false := by
  cases b <;> cases c <;> simp [witnessRight]

private theorem example_line (i j : Bool) (a : W 6) :
    lo witnessLeft witnessRight (i,j,a) = 2 * booleanSpec flatSign a := by
  have val (b c : Bool) (u : W 6) :
      halfSum (witnessLeft (b,c,u)) (witnessRight (b,c,u)) =
      if b = false ∧ c = false then sign (flatSign u) else 0 := by
    cases b <;> cases c <;> simp [halfSum,witnessRight,witnessLeft]
  rw [(blocks_exact ..).1,head_transform,head_transform,head_transform]
  have z : transform (fun _ : W 6 => (0:Int)) a = 0 := by simp [transform,total_zero]
  cases i <;> cases j <;> simp [val,z,booleanSpec]

/-- An actual balanced, correctly adapted nine-bit table attains the low
peak 24, passes all low residues, and admits the preceding obstruction. -/
theorem low_block_witness :
    total 9 (fun x => sign (halves witnessLeft witnessRight x)) = 0 ∧
    supportXor (halves witnessLeft witnessRight) = (true,zero 8) ∧
    (∀ a, (lo witnessLeft witnessRight a).natAbs ≤ 24 ∧ lo witnessLeft witnessRight a % 8 = 0) ∧
    (∃ a, lo witnessLeft witnessRight a = 24) := by
  refine ⟨by decide,by decide,?_,?_⟩
  · rintro ⟨i,j,a⟩
    rw [example_line]
    have e : (FreezeMovies.worlds 6).all (fun v =>
        decide ((2 * booleanSpec flatSign v).natAbs ≤ 24 ∧ (2 * booleanSpec flatSign v) % 8 = 0)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp e a (FreezeMovies.all_worlds 6 a))
  · exact ⟨(false,false,true,true,true,false,false,false,()),by rw [example_line]; decide⟩


/-- On this balanced table the upper bound 36 on the high block is attained.
The three tags have disjoint initial spectral supports, and a single flip adds
magnitude two to the six-bit budget. -/
theorem flat_bound_attained :
    (∀ a, (hi witnessLeft witnessRight a).natAbs ≤ 36) ∧
    ∃ a, (hi witnessLeft witnessRight a).natAbs = 36 := by
  let S (b c : Bool) : Slice := fun u => witnessLeft (b,c,u)
  let test (v : W 6) := decide ((booleanSpec (S false true) v).natAbs +
    (booleanSpec (S true false) v).natAbs + (booleanSpec (S true true) v).natAbs ≤ 18)
  have table : (FreezeMovies.worlds 6).all test = true := by decide
  have upper (a : W 8) : (hi witnessLeft witnessRight a).natAbs ≤ 36 := by
    rcases a with ⟨i,j,a⟩
    have small := of_decide_eq_true (List.all_eq_true.mp table a (FreezeMovies.all_worlds 6 a))
    change (booleanSpec (S false true) a).natAbs + (booleanSpec (S true false) a).natAbs +
      (booleanSpec (S true true) a).natAbs ≤ 18 at small
    rw [flat_hi_line _ _ witness_flat]
    change (2*(sign j * booleanSpec (S false true) a + sign i * booleanSpec (S true false) a +
      (sign i * sign j) * booleanSpec (S true true) a)).natAbs ≤ 36
    cases i <;> cases j <;> simp [sign] <;> omega
  obtain ⟨a,h⟩ := flat_forces_36 _ _ witness_flat low_block_witness.2.1 low_block_witness.1
  exact ⟨upper,a,Nat.le_antisymm (upper a) h⟩

def oddCount (F : W n → Int) := total n (fun a => F a % 2)

private theorem constant_mass (F : W n → Int) (live : ∃ a, F a % 2 = 1)
    (flat : ∀ p b, (F (add n p b) - F b) % 2 = 0) : oddCount F = many n := by
  obtain ⟨a,ha⟩ := live
  have parity (b : W n) : F b % 2 = 1 := by
    have x := flat a (zero n); have y := flat b (zero n)
    simp only [MaskRecovery.add_comm _ _ (zero n),MaskRecovery.add_zero_left] at x y
    omega
  simp [oddCount,parity,total_const]

/-- A nonzero residue of Boolean degree at most k has support at least
2^(n-k). Each nonconstant directional derivative costs at most a factor two. -/
theorem residue_distance (k : Nat) (F : W n → Int) (live : ∃ a, F a % 2 = 1)
    (order : ∀ ds : List (W n), ds.length = k+1 → ∀ a, differences ds F a % 2 = 0) :
    many n ≤ many k * oddCount F := by
  classical
  induction k generalizing F with
  | zero =>
    have flat (p b : W n) := order [p] rfl b
    rw [constant_mass F live flat]; simp [many]
  | succ k ih =>
    by_cases flat : ∀ p b, (F (add n p b) - F b) % 2 = 0
    · rw [constant_mass F live flat]
      have m := many_pos (k+1)
      simpa using Int.mul_le_mul_of_nonneg_right (show 1 ≤ many (k+1) by omega) (many_nonneg n)
    · have witness : ∃ p b, (F (add n p b) - F b) % 2 = 1 := by
        apply Classical.byContradiction
        intro h; apply flat; intro p b
        have ne : (F (add n p b) - F b) % 2 ≠ 1 := fun e => h ⟨p,b,e⟩
        omega
      obtain ⟨p,b,hb⟩ := witness
      let D (x : W n) := F (add n p x) - F x
      have bound := ih D ⟨b,hb⟩ (fun ds len a => order (p::ds) (by simp [len]) a)
      have sub : oddCount D ≤ 2*oddCount F := by
        have h := total_mono n (fun x => D x % 2) (fun x => F (add n p x) % 2 + F x % 2)
          (fun x => by dsimp [D]; omega)
        rw [total_add, MaskRecovery.sum_shift n p (fun x => F x % 2)] at h
        unfold oddCount; omega
      have step := Int.mul_le_mul_of_nonneg_left sub (many_nonneg k)
      rw [← Int.mul_assoc] at step
      exact Int.le_trans bound step

/-- The low block modulo sixteen defines a quadratic Boolean residue. -/
theorem low_residue_order (f g : Half) (res : ∀ a, lo f g a % 8 = 0) :
    ∀ ds : List (W 8), ds.length = 3 → ∀ a,
      differences ds (fun b => lo f g b / 8 + 1) a % 2 = 0 := by
  let F (a : W 8) := lo f g a / 8 + 1
  have repr (a : W 8) : 8 * F a = lo f g a - (-8) := by have := res a; dsimp [F]; omega
  intro ds len a
  change differences ds F a % 2 = 0
  have e := diff_scale ds 8 F a
  rw [funext repr,diff_sub] at e
  have const0 : differences ds (fun _ => (-8:Int)) a = 0 := by
    match ds with
    | [_,_,_] => simp [differences]
    | [] | [_] | [_,_] | _::_::_::_::_ => simp at len
  rw [const0,Int.sub_zero] at e
  rw [funext (fun b => (blocks_exact f g b).1),diff_scale] at e
  obtain ⟨z,hz⟩ := diff_transform_dvd ds (fun x => halfSum (f x) (g x)) a
  rw [len] at hz
  change differences ds _ a = 8*z at hz
  rw [hz] at e; omega

/-- At least 64 low masks, including DC, have residue zero modulo 16. -/
theorem sixty_four_low (f g : Half) (dc : lo f g (zero 8) = 0)
    (res : ∀ a, lo f g a % 8 = 0) :
    64 ≤ total 8 (fun a => if lo f g a % 16 = 0 then 1 else 0) := by
  let F (a : W 8) := lo f g a / 8 + 1
  have ord := low_residue_order f g res
  have h := residue_distance 2 F ⟨zero 8,by simp [F,dc]⟩ ord
  have v (a : W 8) : F a % 2 = if lo f g a % 16 = 0 then 1 else 0 := by
    have := res a; dsimp [F]; split <;> omega
  simp only [oddCount,v] at h
  change 256 ≤ 4 * _ at h; omega

theorem equal_pair_range (f g : Half)
    (axis : supportXor (halves f g) = (true,zero 8))
    (bal : total 9 (fun x => sign (halves f g x)) = 0)
    (cap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28) :
    countPair f g false = countPair f g true ∧ 30 ≤ countPair f g true ∧ countPair f g true ≤ 61 := by
  have split0 : total 8 (fun x => sign (f x) + sign (g x)) = 0 := by rw [total_add]; exact bal
  have dc : lo f g (zero 8) = 0 := by simpa [lo,spec,transform,chr,dot_zero,sign,total_add] using split0
  have signs (b c : Bool) : sign b + sign c = 2*(sameBit false b c - sameBit true b c) := by
    cases b <;> cases c <;> decide
  have eqv := split0
  simp only [signs,total_scale,total_sub] at eqv
  change 2*(countPair f g false - countPair f g true) = 0 at eqv
  have res (a : W 8) := (adapted_blocks f g axis bal a).1
  have count := sixty_four_low f g dc res
  let mark (a : W 8) : Int := if lo f g a % 16 = 0 then 1 else 0
  have pt (a : W 8) : lo f g a * lo f g a + 320*mark a + hits (zero 8) a ≤ 576 := by
    have h := (cap a).1; have r := res a
    by_cases z : zero 8 = a
    · subst a; simp [dc,mark,hits]
    · have vals : lo f g a = -24 ∨ lo f g a = -16 ∨ lo f g a = -8 ∨ lo f g a = 0 ∨
          lo f g a = 8 ∨ lo f g a = 16 ∨ lo f g a = 24 := by omega
      rcases vals with e|e|e|e|e|e|e <;> simp [hits,z,mark,e]
  have sq (b c : Bool) : halfSum b c * halfSum b c = sameBit false b c + sameBit true b c := by
    cases b <;> cases c <;> decide
  have energyLo : total 8 (fun a => lo f g a * lo f g a) =
      1024*(countPair f g false+countPair f g true) := by
    have scaleSq (z : Int) : 2*z*(2*z) = 4*(z*z) := by
      change 2*z*(2*z) = (2*2)*(z*z); ac_rfl
    simp only [(blocks_exact f g _).1,scaleSq,total_scale,parsevalInt,sq,total_add,countPair]
    change 4*(256*_) = 1024*_; omega
  have h := total_mono 8 _ _ pt
  simp only [total_add,total_scale,diagonal,total_const,energyLo] at h
  change _ ≤ 256*576 at h
  change 64 ≤ total 8 mark at count
  exact ⟨by omega,(thirty_each f g split0 (fun a => (cap a).2)).2,by omega⟩

def multiplicity (F : W n → Int) (m : Nat) :=
  total n (fun a => if (F a).natAbs = m then 1 else 0)

private theorem multiplicity_nonneg (F : W n → Int) (m : Nat) : 0 ≤ multiplicity F m := by
  calc
    0 = total n (fun _ => 0) := (total_zero n).symm
    _ ≤ multiplicity F m := total_mono n _ _ (fun a => by
      change (0:Int) ≤ if (F a).natAbs = m then 1 else 0
      split <;> decide)

/-- Exact accounting of the four allowed magnitudes in the high block.
The first budget bound would permit 91 peaks with a deficit of one.
Magnitudes 12 and 4 cost two and three deficit units, respectively. -/
theorem high_peak_budget (f g : Half)
    (axis : supportXor (halves f g) = (true,zero 8))
    (bal : total 9 (fun x => sign (halves f g x)) = 0)
    (cap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28) :
    let N := multiplicity (hi f g)
    8*(countPair f g false + countPair f g true) + 3*N 28 = 1248 + 2*N 12 + 3*N 4 ∧
    92 ≤ N 28 := by
  let mask (m : Nat) (a : W 8) : Int := if (hi f g a).natAbs = m then 1 else 0
  have pt (a : W 8) : hi f g a * hi f g a =
      400 + 384*mask 28 a - 256*mask 12 a - 384*mask 4 a := by
    have h := (cap a).2; have r := (adapted_blocks f g axis bal a).2
    have vals : hi f g a = -28 ∨ hi f g a = -20 ∨ hi f g a = -12 ∨ hi f g a = -4 ∨
        hi f g a = 4 ∨ hi f g a = 12 ∨ hi f g a = 20 ∨ hi f g a = 28 := by omega
    rcases vals with e|e|e|e|e|e|e|e <;> simp [mask,e]
  have h := congrArg (total 8) (funext pt)
  simp only [diffEnergy,total_sub,total_add,total_const,total_scale] at h
  let N := multiplicity (hi f g)
  change 1024 * (256 - _ - _) = 256*400 + 384*N 28 - 256*N 12 - 384*N 4 at h
  obtain ⟨same,_,maxPairs⟩ := equal_pair_range f g axis bal cap
  have n₁ : 0 ≤ N 12 := multiplicity_nonneg _ _
  have n₂ : 0 ≤ N 4 := multiplicity_nonneg _ _
  change _ + 3*N 28 = _ + 2*N 12 + 3*N 4 ∧ 92 ≤ N 28
  constructor
  · omega
  · by_cases pos : 1 ≤ N 12 <;> by_cases pos' : 1 ≤ N 4 <;> omega

#print axioms high_peak_budget
#print axioms shared_cubic_residue
#print axioms quartic_vanishes
#print axioms low_block_witness
#print axioms flat_bound_attained
#print axioms three_slices
#print axioms flat_agreement_obstruction
#print axioms flat_forces_36
#print axioms sixty_four_low
#print axioms equal_pair_range
end Balanced242Blocks
