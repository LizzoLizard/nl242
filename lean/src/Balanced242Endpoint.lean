import Balanced242Sectors

/-! The upper endpoint of the agreement range. All spectra are unnormalized. -/
namespace Balanced242Endpoint
open FrozenShells CandyKnots CollisionLaw MaskRecovery SilentRoom Balanced242Parents
  Balanced242Blocks Balanced242Support Balanced242Sectors

private theorem assocW (n : Nat) (u v x : W n) :
    add n (add n u v) x = add n u (add n v x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [add,ih,Bool.xor_assoc]

private theorem twiceW (n : Nat) (u x : W n) : add n u (add n u x) = x := by
  rw [←assocW,add_self,add_zero_left]

private theorem pull_diff (P : W n → W n) (lin : additive P) (ds : List (W n))
    (F : W n → Int) (a : W n) :
    differences ds (fun x => F (P x)) a = differences (ds.map P) F (P a) := by
  induction ds generalizing F with
  | nil => rfl
  | cons d ds ih =>
    simp only [differences,List.map_cons,lin _ _]
    exact ih (fun b => F (add n (P d) b) - F b)

private def pol (F : W n → Int) (u x : W n) : Bool :=
  decide ((F (add n u x) - F x - F u + F (zero n)) % 2 = 1)

private theorem pol_linear (F : W n → Int)
    (ord : ∀ ds : List (W n), ds.length = 3 → ∀ a, differences ds F a % 2 = 0)
    (u x y : W n) : pol F u (add n x y) = xor (pol F u x) (pol F u y) := by
  have h := ord [u,x,y] rfl (zero n)
  simp only [differences,add_comm n _ (zero n),add_zero_left] at h
  cases hx : pol F u x <;> cases hy : pol F u y <;>
    simp only [pol,decide_eq_true_eq,decide_eq_false_iff_not] at * <;>
    first | (apply decide_eq_true; omega) | (apply decide_eq_false; omega)

private theorem pol_self (F : W n → Int) (u : W n) : pol F u u = false := by
  simp only [pol,add_self]; apply decide_eq_false; omega

private theorem pol_comm (F : W n → Int) (u v : W n) : pol F u v = pol F v u := by
  simp only [pol,add_comm n u v]; congr 3 <;> omega

private theorem polar_pair (F : W 8 → Int) (dc : F (zero 8) % 2 = 1)
    (small : oddCount F < 128) : ∃ u v, pol F u v = true := by
  apply Classical.byContradiction
  intro none
  have vanish (u x : W 8) : (F (add 8 u x) - F x - F u + F (zero 8)) % 2 = 0 := by
    by_cases h : (F (add 8 u x) - F x - F u + F (zero 8)) % 2 = 1
    · exact False.elim (none ⟨u,x,by simpa only [pol,decide_eq_true_eq] using h⟩)
    · omega
  have order2 (ds : List (W 8)) (len : ds.length = 2) (a : W 8) :
      differences ds F a % 2 = 0 := by
    match ds with
    | [p,q] =>
      have h := vanish p (add 8 q a)
      have j := vanish p a
      simp only [differences]; omega
    | [] | [_] | _::_::_::_ => simp at len
  have bound := residue_distance 1 F ⟨_,dc⟩ order2
  change 256 ≤ 2 * oddCount F at bound
  omega

private def move (b : Bool) (v x : W n) := if b then add n v x else x

private theorem move_sum (b c : Bool) (v x y : W n) :
    move (xor b c) v (add n x y) = add n (move b v x) (move c v y) := by
  cases b <;> cases c
  · rfl
  · exact (add_shuffle n v x y).symm
  · exact (assocW n v x y).symm
  · change add n x y = add n (add n v x) (add n v y)
    rw [assocW,add_shuffle n v x y,twiceW]

private def project (F : W n → Int) (u v x : W n) :=
  move (pol F v x) u (move (pol F u x) v x)

private theorem proj_linear (F : W n → Int) (u v : W n)
    (ord : ∀ ds : List (W n), ds.length = 3 → ∀ a, differences ds F a % 2 = 0) :
    additive (project F u v) := by
  intro x y
  simp only [project,pol_linear F ord,move_sum]

private theorem proj_kernel (F : W n → Int) (u v : W n)
    (ord : ∀ ds : List (W n), ds.length = 3 → ∀ a, differences ds F a % 2 = 0)
    (cross : pol F u v = true) (x : W n) :
    pol F u (project F u v x) = false ∧ pol F v (project F u v x) = false := by
  have rev := (pol_comm F v u).trans cross
  cases hu : pol F u x <;> cases hv : pol F v x <;>
    simp [project,move,hu,hv,pol_linear F ord,pol_self,cross,rev]

private def cell (u v : W n) (F : W n → Int) (x : W n) :=
  F x + F (add n u x) + F (add n v x) + F (add n u (add n v x))

private theorem cell_total (Q : W n → Int) (u v : W n) (F : W n → Int) :
    total n (fun x => cell u v F (project Q u v x)) = 4 * total n F := by
  have h (x : W n) : cell u v F (project Q u v x) = cell u v F x := by
    have hu (a : W n) : cell u v F (add n u a) = cell u v F a := by
      have k := add_shuffle n u v a
      simp only [cell,k,twiceW]; omega
    have hv (a : W n) : cell u v F (add n v a) = cell u v F a := by
      simp only [cell,twiceW]; omega
    cases a : pol Q u x <;> cases b : pol Q v x <;> simp [project,move,a,b,hu,hv]
  rw [funext h]
  change total n (fun x => F x + F (add n u x) + F (add n v x) + F (add n u (add n v x))) = _
  simp only [total_add]
  rw [sum_shift n v (fun x => F (add n u x))]
  simp only [sum_shift]; omega

private theorem diff_const (ds : List (W n)) (k : Int) (a : W n) :
    differences ds (fun _ => k) a = if ds.isEmpty then k else 0 := by
  induction ds generalizing k with
  | nil => rfl
  | cons u ds ih => simp only [differences,Int.sub_self,ih]; cases ds <;> rfl

private theorem corner_relations (F : W n → Int) (u v : W n)
    (ord : ∀ ds : List (W n), ds.length = 3 → ∀ a, differences ds F a % 2 = 0)
    (cross : pol F u v = true) (x : W n) :
    let w := project F u v x
    let A := F u - F (zero n)
    let B := F v - F (zero n)
    (F (add n u w) - F w - A) % 2 = 0 ∧
    (F (add n v w) - F w - B) % 2 = 0 ∧
    (F (add n u (add n v w)) - F (add n v w) - A) % 2 = 1 := by
  let w := project F u v x
  obtain ⟨p,q⟩ := proj_kernel F u v ord cross x
  have r : pol F u (add n v w) = true := by rw [pol_linear F ord,cross,p]; rfl
  change pol F u w = false at p
  change pol F v w = false at q
  simp only [pol,decide_eq_true_eq,decide_eq_false_iff_not] at p q r
  dsimp only; change _ ∧ _ ∧ (F (add n u (add n v w)) - F (add n v w) - _) % 2 = 1
  change (F (add n u w) - F w - _) % 2 = 0 ∧ (F (add n v w) - F w - _) % 2 = 0 ∧ _
  exact ⟨by omega,by omega,by omega⟩

/-- A quadratic residue containing zero, with fewer than 96 ones, is a
six-dimensional linear flat. P projects each four-point cell onto its unique one. -/
private theorem small_quadratic (F : W 8 → Int) (dc : F (zero 8) % 2 = 1)
    (ord : ∀ ds : List (W 8), ds.length = 3 → ∀ a, differences ds F a % 2 = 0)
    (small : oddCount F < 96) :
    ∃ u v, pol F u v = true ∧ ∀ x,
      let w := project F u v x
      F w % 2 = 1 ∧ F (add 8 u w) % 2 = 0 ∧ F (add 8 v w) % 2 = 0 ∧
      F (add 8 u (add 8 v w)) % 2 = 0 := by
  obtain ⟨u,v,cross⟩ := polar_pair F dc (by omega)
  let P := project F u v
  have lin : additive P := proj_linear F u v ord
  let A := F u - F (zero 8)
  let B := F v - F (zero 8)
  let minority := A % 2 = 1 ∧ B % 2 = 1
  let Q (x : W 8) := if minority then 1-F (P x) else F (P x)
  have shape (x : W 8) : cell u v (fun a => F a % 2) (P x) = 1 + 2*(Q x % 2) := by
    have ⟨h,j,k⟩ := corner_relations F u v ord cross x
    change (F (add 8 u (P x)) - F (P x) - A) % 2 = 0 at h
    change (F (add 8 v (P x)) - F (P x) - B) % 2 = 0 at j
    change (F (add 8 u (add 8 v (P x))) - F (add 8 v (P x)) - A) % 2 = 1 at k
    simp only [cell,Q,minority]
    split <;> omega
  have mass := cell_total F u v (fun a => F a % 2)
  change total 8 (fun x => cell u v _ (P x)) = 4*oddCount F at mass
  rw [funext shape,total_add,total_scale,total_const] at mass
  change 256*1 + 2*oddCount Q = 4*oddCount F at mass
  have orderQ (ds : List (W 8)) (len : ds.length = 3) (a : W 8) :
      differences ds Q a % 2 = 0 := by
    have h := ord (ds.map P) (by simpa using len) (P a)
    by_cases b : minority
    · simp only [Q,if_pos b,diff_sub,diff_const,pull_diff P lin] 
      have ne : ds.isEmpty = false := by cases ds <;> simp_all
      rw [ne]; simp only [Bool.false_eq_true,if_false]; omega
    · simpa only [Q,if_neg b,pull_diff P lin] using h
  have allZero (x : W 8) : Q x % 2 = 0 := by
    by_cases h : Q x % 2 = 1
    · have bound := residue_distance 2 Q ⟨_,h⟩ orderQ
      change 256 ≤ 4*oddCount Q at bound; omega
    · omega
  have m : minority := by
    have h := allZero (zero 8)
    rw [show Q (zero 8) = (if minority then 1-F (zero 8) else F (zero 8)) by
      simp only [Q,zero_image P lin]] at h
    by_cases b : minority <;> simp_all
  refine ⟨u,v,cross,?_⟩
  intro x
  have z := allZero x
  simp only [Q,if_pos m] at z
  have s := shape x
  rw [allZero] at s
  change F (P x) % 2 + F (add 8 u (P x)) % 2 + F (add 8 v (P x)) % 2 +
      F (add 8 u (add 8 v (P x))) % 2 = 1+2*0 at s
  change F (P x) % 2 = 1 ∧ F (add 8 u (P x)) % 2 = 0 ∧ F (add 8 v (P x)) % 2 = 0 ∧
    F (add 8 u (add 8 v (P x))) % 2 = 0
  refine ⟨?_,?_,?_,?_⟩ <;> omega

private theorem total_dvd_three (H : W n → Int) (h : ∀ x, 3 ∣ H x) : 3 ∣ total n H := by
  induction n with
  | zero => exact h ()
  | succ n ih => exact Int.dvd_add (ih _ (fun x => h (false,x))) (ih _ (fun x => h (true,x)))

/-- Reducing the low spectrum modulo three preserves its linear span.
A missing frequency direction gives integer translation invariance because
0, 2 and -2 are distinct modulo three. -/
theorem low_span_mod_three (f g : Half) (d : W 8)
    (div : ∀ a, dot 8 a d = true → (3:Int) ∣ lo f g a) :
    ∀ a, dot 8 a d = true → lo f g a = 0 := by
  let V := pairSign f g
  have L : lo f g = transform V := lo_transform f g
  have periodV (x : W 8) : V (add 8 d x) = V x := by
    let D (a : W 8) := lo f g a * chr a (add 8 d x) - lo f g a * chr a x
    have each (a : W 8) : 3 ∣ D a := by
      simp only [D,chr,dot_right,signMul]
      cases e : dot 8 a d with
      | false => simp [sign]; exact ⟨0,rfl⟩
      | true =>
        obtain ⟨k,hk⟩ := div a e
        exact ⟨k * (sign true * sign (dot 8 a x) - sign (dot 8 a x)),
          by rw [hk]; simp only [Int.mul_sub,Int.mul_assoc]⟩
    obtain ⟨k,hk⟩ := total_dvd_three D each
    simp only [D,L,total_sub,inversion] at hk
    change 256*V (add 8 d x) - 256*V x = 3*k at hk
    have vals (z : W 8) : V z = 0 ∨ V z = 2 ∨ V z = -2 := by
      cases h : f z <;> cases j : g z <;> simp [V,pairSign,h,j,sign]
    rcases vals (add 8 d x) with h|h|h <;> rcases vals x with e|e|e <;> omega
  intro a ha
  have m := sum_shift 8 d (fun x => V x * chr a x)
  simp only [periodV,chr,dot_right,ha,signMul,show sign true = -1 from rfl] at m
  have neg (x : W 8) : V x * (-1 * sign (dot 8 a x)) = -1 * (V x * sign (dot 8 a x)) := by ac_rfl
  simp only [neg,total_scale] at m
  rw [L]; change total 8 (fun x => V x * sign (dot 8 a x)) = 0; omega

private theorem low_energy (f g : Half) :
    total 8 (fun a => lo f g a * lo f g a) = 1024*agreements f g := by
  have h (x : W 8) : pairSign f g x * pairSign f g x =
      4*(sameBit false (f x) (g x) + sameBit true (f x) (g x)) := by
    cases p : f x <;> cases q : g x <;> simp [pairSign,sign,p,q,sameBit]
  rw [lo_transform,parsevalInt]
  simp only [h,total_scale,total_add]
  unfold agreements countPair
  change 256*(4*(_+_)) = 1024*(_+_); omega

private theorem projected_zeros (f g : Half) (P : W 8 → W 8) (lin : additive P)
    (dc : lo f g (zero 8) = 0) (div : ∀ x, lo f g (P x) % 16 = 0)
    (cap : ∀ a, (lo f g a).natAbs ≤ 24) :
    32 ≤ total 8 (fun x => if lo f g (P x) = 0 then 1 else 0) := by
  let K (x : W 8) := lo f g (P x) / 16 + 1
  have repr (x : W 8) : 16*K x = lo f g (P x) - (-16) := by
    have h := div x; dsimp [K]; omega
  have ord (ds : List (W 8)) (len : ds.length = 4) (a : W 8) :
      differences ds K a % 2 = 0 := by
    have h := diff_scale ds 16 K a
    rw [funext repr,diff_sub,diff_const,pull_diff P lin] at h
    match ds with
    | [p,q,r,s] =>
      obtain ⟨k,hk⟩ := (quartic_vanishes f g (P a) (P p) (P q) (P r) (P s)).1
      simp only [List.map_cons,List.map_nil,List.isEmpty_cons,Bool.false_eq_true,if_false,Int.sub_zero] at h
      omega
    | [] | [_] | [_,_] | [_,_,_] | _::_::_::_::_::_ => simp at len
  have bound := residue_distance 3 K ⟨zero 8,by simp [K,zero_image P lin,dc]⟩ ord
  have pt (x : W 8) : K x % 2 = if lo f g (P x) = 0 then 1 else 0 := by
    have h := div x; have c := cap (P x); simp only [K]; split <;> omega
  simp only [oddCount,pt] at bound
  change 256 ≤ 8 * _ at bound; omega

private theorem recover_corner (F : W n → Int) (u v x : W n) :
    let w := project F u v x
    (pol F v x = false ∧ pol F u x = false ∧ x = w) ∨
    (pol F v x = true ∧ x = add n u w) ∨
    (pol F u x = true ∧ x = add n v w) ∨
    (pol F v x = true ∧ x = add n u (add n v w)) := by
  cases a : pol F u x <;> cases b : pol F v x <;> simp [project,move,a,b,twiceW,add_shuffle n u v (add n v x)]

/-- From 114 agreements upwards, the mod-sixteen zero residue is a flat
of size 64. Its actual zeros and the small peaks outside it satisfy an
exact deficit identity as well as two independent lower bounds. -/
theorem large_support_counts (f g : Half) (dc : lo f g (zero 8) = 0)
    (res : ∀ a, lo f g a % 8 = 0) (cap : ∀ a, (lo f g a).natAbs ≤ 24)
    (large : 114 ≤ agreements f g) :
    let L := lo f g
    total 8 (fun a => if L a % 16 = 0 then 1 else 0) = 64 ∧
    8 ≤ multiplicity L 0 ∧ 6 ≤ multiplicity L 8 ∧
    4*agreements f g + multiplicity L 0 + 2*multiplicity L 8 = 496 ∧
    (agreements f g = 118 → ∃ d, d ≠ zero 8 ∧ total 8 (smallIn f g d) = 4 ∧
      ∀ a, dot 8 a d = true → (L a).natAbs = 8 ∨ (L a).natAbs = 24) := by
  let L := lo f g
  let Q (a : W 8) := L a / 8 + 1
  let Z (a : W 8) : Int := if L a % 16 = 0 then 1 else 0
  let E (a : W 8) : Int := if L a = 0 then 1 else 0
  have bit (a : W 8) : Q a % 2 = Z a := by
    have h : L a % 8 = 0 := res a
    simp only [Q,Z]; split <;> omega
  have budget := low_support_budget f g dc res cap
  change 1024*agreements f g + 320*total 8 Z + 256 ≤ 147456 at budget
  have ord := low_residue_order f g res
  change ∀ ds : List (W 8), ds.length = 3 → ∀ a, differences ds Q a % 2 = 0 at ord
  have qSmall : oddCount Q < 96 := by
    simp only [oddCount,bit]
    change total 8 Z < 96
    omega
  obtain ⟨u,v,cross,corners⟩ := small_quadratic Q (by simp [Q,L,dc]) ord qSmall
  let P := project Q u v
  have lin : additive P := proj_linear Q u v ord
  have levels (x : W 8) : Z (P x) = 1 ∧ Z (add 8 u (P x)) = 0 ∧
      Z (add 8 v (P x)) = 0 ∧ Z (add 8 u (add 8 v (P x))) = 0 := by
    simpa only [bit] using corners x
  have cz (x : W 8) : cell u v Z (P x) = 1 := by
    obtain ⟨a,b,c,d⟩ := levels x
    simp [cell,a,b,c,d]
  have mass := cell_total Q u v Z
  change total 8 (fun x => cell u v Z (P x)) = 4*total 8 Z at mass
  rw [funext cz,total_const] at mass
  change 256*1 = 4 * total 8 Z at mass
  have div (x : W 8) : L (P x) % 16 = 0 := by
    have h := (levels x).1
    unfold Z at h; split at h <;> simp_all
  have zero_bound := projected_zeros f g P lin dc div cap
  change 32 ≤ total 8 (fun x => E (P x)) at zero_bound
  have other (a : W 8) (h : Z a = 0) : E a = 0 := by
    by_cases e : L a = 0 <;> simp_all [Z,E]
  have ce (x : W 8) : cell u v E (P x) = E (P x) := by
    obtain ⟨_,b,c,d⟩ := levels x
    simp [cell,other _ b,other _ c,other _ d]
  have empties := cell_total Q u v E
  change total 8 (fun x => cell u v E (P x)) = 4*total 8 E at empties
  rw [funext ce] at empties
  let p := readMask 8 (pol Q u)
  let q := readMask 8 (pol Q v)
  have hp (a : W 8) : dot 8 a p = pol Q u a := by
    rw [dot_comm]; exact readMask_spec 8 _ (pol_linear Q ord u) a
  have hq (a : W 8) : dot 8 a q = pol Q v a := by
    rw [dot_comm]; exact readMask_spec 8 _ (pol_linear Q ord v) a
  have inside (a : W 8) (yes : Z a = 1) : dot 8 a p = false ∧ dot 8 a q = false := by
    obtain ⟨_,b,c,d⟩ := levels a
    rcases recover_corner Q u v a with ⟨h,j,_⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact ⟨(hp a).trans j,(hq a).trans h⟩
    · have e := (congrArg Z h).trans b; omega
    · have e := (congrArg Z h).trans c; omega
    · have e := (congrArg Z h).trans d; omega
  have hd (d : W 8) (live : ∃ x, dot 8 x d = true)
      (off : ∀ a, Z a = 1 → dot 8 a d = false) :
      let m := total 8 (smallIn f g d)
      (4 ≤ m ∧ (m%2=1 → 7 ≤ m)) ∧ d ≠ zero 8 ∧
      ∀ a, dot 8 a d = true → (L a).natAbs = 8 ∨ (L a).natAbs = 24 := by
    have nz : d ≠ zero 8 := by
      intro dead; obtain ⟨x,hx⟩ := live; rw [dead,dot_zero_right] at hx; contradiction
    have magnitudes (a : W 8) (ha : dot 8 a d = true) : (L a).natAbs = 8 ∨ (L a).natAbs = 24 := by
      have c : (L a).natAbs ≤ 24 := cap a
      have r : L a % 8 = 0 := res a
      have ne : L a % 16 ≠ 0 := by
        intro e; have hh := off a (by simp [Z,e]); rw [ha] at hh; contradiction
      omega
    have counts := halfspace_small_counts f g d nz magnitudes
    exact ⟨⟨counts.1,counts.2.1⟩,nz,magnitudes⟩
  have m₁ := hd p ⟨v,(hp v).trans cross⟩ (fun a h => (inside a h).1)
  have rev := (pol_comm Q v u).trans cross
  have m₂ := hd q ⟨u,(hq u).trans rev⟩ (fun a h => (inside a h).2)
  have m₃ := hd (add 8 p q) ⟨v,by rw [dot_right,hp,hq,cross,pol_self]; rfl⟩
    (fun a h => by rw [dot_right,(inside a h).1,(inside a h).2]; rfl)
  let I (a : W 8) : Int := if (L a).natAbs = 8 then 1 else 0
  have multiplicities (a : W 8) :
      smallIn f g p a + smallIn f g q a + smallIn f g (add 8 p q) a ≤ 2*I a := by
    simp only [smallIn,I,L,dot_right]
    cases dot 8 a p <;> cases dot 8 a q <;> by_cases h : (lo f g a).natAbs = 8 <;> simp [h]
  have smallMasks := total_mono 8 _ _ multiplicities
  simp only [total_add,total_scale] at smallMasks
  have line (a : W 8) : L a * L a + 320*Z a + 256*E a + 512*I a = 576 := by
    have r : L a % 8 = 0 := res a
    have c : (L a).natAbs ≤ 24 := cap a
    have vals : L a = -24 ∨ L a = -16 ∨ L a = -8 ∨ L a = 0 ∨ L a = 8 ∨ L a = 16 ∨ L a = 24 := by omega
    rcases vals with e|e|e|e|e|e|e <;> simp [Z,E,I,e]
  have sum := congrArg (total 8) (funext line)
  simp only [total_add,total_scale,total_const] at sum
  have energy := low_energy f g
  change total 8 (fun a => L a * L a) = 1024*agreements f g at energy
  rw [energy] at sum
  change _ = 256*576 at sum
  have zeros : multiplicity L 0 = total 8 E := by simp [multiplicity,E]
  have lp := m₁.1.1
  have lq := m₂.1.1
  have lr := m₃.1.1
  have exactCount : 4*agreements f g + total 8 E + 2*total 8 I = 496 := by omega
  refine ⟨by change total 8 Z = 64; omega,by rw [zeros]; omega,by change 6 ≤ total 8 I; omega,
    by rw [zeros]; exact exactCount,?_⟩
  intro endpoint
  have gap (m : Int) (lo : 4 ≤ m) (odd : m%2=1 → 7 ≤ m) : m=4 ∨ 6 ≤ m := by
    by_cases five : m=5
    · have h := odd (by rw [five]; decide); omega
    · omega
  have g₁ := gap _ lp m₁.1.2
  have g₂ := gap _ lq m₂.1.2
  have g₃ := gap _ lr m₃.1.2
  have four : total 8 (smallIn f g p) = 4 ∨ total 8 (smallIn f g q) = 4 ∨
      total 8 (smallIn f g (add 8 p q)) = 4 := by omega
  rcases four with h|h|h
  · exact ⟨p,m₁.2.1,h,m₁.2.2⟩
  · exact ⟨q,m₂.2.1,h,m₂.2.2⟩
  · exact ⟨_,m₃.2.1,h,m₃.2.2⟩

/-- A prescribed spectrum for one full half of the low block at the
remaining upper endpoint. The direction may depend on the table. -/
theorem four_mask_at_118 (f g : Half) (dc : lo f g (zero 8) = 0)
    (res : ∀ a, lo f g a % 8 = 0) (cap : ∀ a, (lo f g a).natAbs ≤ 24)
    (t : agreements f g = 118) :
    ∃ d, d ≠ zero 8 ∧ total 8 (smallIn f g d) = 4 ∧
      ∀ a, dot 8 a d = true → (lo f g a).natAbs = 8 ∨ (lo f g a).natAbs = 24 :=
  (large_support_counts f g dc res cap (by omega)).2.2.2.2 t

theorem low_agreements_below_120 (f g : Half) (dc : lo f g (zero 8) = 0)
    (res : ∀ a, lo f g a % 8 = 0) (cap : ∀ a, (lo f g a).natAbs ≤ 24) :
    agreements f g < 120 := by
  by_cases h : 114 ≤ agreements f g
  · obtain ⟨_,z,s,e,_⟩ := large_support_counts f g dc res cap h
    omega
  · omega

/-- In coordinates adapted to the support XOR, the agreement count is even,
at most 118, and at least 102 high masks must have magnitude 28. -/
theorem agreement_and_peak_range (f g : Half)
    (axis : supportXor (halves f g) = (true,zero 8))
    (bal : total 9 (fun x => sign (halves f g x)) = 0)
    (cap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28) :
    64 ≤ agreements f g ∧ agreements f g ≤ 118 ∧ 102 ≤ multiplicity (hi f g) 28 := by
  have split : total 8 (fun x => sign (f x) + sign (g x)) = 0 := by rw [total_add]; exact bal
  have dc : lo f g (zero 8) = 0 := by simpa [lo,spec,transform,chr,dot_zero,sign,total_add] using split
  have res (a : W 8) := (adapted_blocks f g axis bal a).1
  have ub := low_agreements_below_120 f g dc res (fun a => by have := (cap a).1; have := res a; omega)
  have eqv := (equal_pair_range f g axis bal cap).1
  have budget := (high_peak_budget f g axis bal cap).1
  have nonneg (m : Nat) : 0 ≤ multiplicity (hi f g) m := by
    rw [← total_zero 8]; apply total_mono; intro a
    change (0:Int) ≤ if _ then 1 else 0; split <;> decide
  have h₁ := nonneg 4
  have h₂ := nonneg 12
  exact ⟨agreement_floor f g axis bal cap,by unfold agreements at *; omega,by unfold agreements at *; omega⟩

#print axioms low_span_mod_three
#print axioms large_support_counts
#print axioms four_mask_at_118
#print axioms low_agreements_below_120
#print axioms agreement_and_peak_range
end Balanced242Endpoint
