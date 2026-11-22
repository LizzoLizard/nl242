import SilentRoom

/-!
Write x=(b,u) in coordinates where the support XOR is the b-axis. For a
balanced function the Walsh blocks at dual bits 0 and 1 are 0 and 4 mod 8,
respectively, by the support-XOR congruence. The blocks are the sum and
difference of the two eight-variable spectra. This file proves the
count and the update for the inverse two-entry construction in those
coordinates, plus a scalar moment bound for normalized odd slices.

For a weight-254 parent, DC is 4 and every Walsh coefficient is 4
modulo 8. The number of ones on each coordinate-zero face is even,
since twice its sign sum is DC plus the corresponding Walsh coefficient.
These face parities are precisely the ANF coefficients of degree eight.
Even total weight clears the degree-nine coefficient as well.

To check with the existing nl242-lab dependencies, run from that
directory with LEAN_PATH=build lean Balanced242Parents.lean.
-/
namespace Balanced242Parents
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom

theorem parsevalInt (n : Nat) (v : W n → Int) :
    total n (fun a => transform v a * transform v a) =
      many n * total n (fun x => v x * v x) := by
  unfold transform
  simp only [rectangular]
  rw [swap]
  have inner (x : W n) :
      total n (fun a => total n (fun y => (v x * chr a x) * (v y * chr a y))) =
        many n * (v x * v x) := by
    rw [swap]
    have fact (a y : W n) : (v x * chr a x) * (v y * chr a y) =
        (v x * v y) * (chr a x * chr a y) := by ac_rfl
    simp only [fact,total_scale,orthogonal]
    have rearr (y : W n) : (v x * v y) * (many n * hits x y) =
        (many n * v x) * (hits x y * v y) := by ac_rfl
    simp only [rearr,total_scale,select,Int.mul_assoc]
  exact (congrArg (total n) (funext inner)).trans (total_scale ..)

abbrev Half := W 8 → Bool
def spec (f : Half) (a : W 8) := transform (fun x => sign (f x)) a
def lo (f g : Half) (a : W 8) := spec f a + spec g a
def hi (f g : Half) (a : W 8) := spec f a - spec g a

def sameBit (b u v : Bool) : Int := if u == b && v == b then 1 else 0
def countPair (f g : Half) (b : Bool) := total 8 (fun x => sameBit b (f x) (g x))

theorem diffEnergy (f g : Half) :
    total 8 (fun a => hi f g a * hi f g a) =
    1024 * (256 - countPair f g false - countPair f g true) := by
  have line (a : W 8) : hi f g a = transform (fun x => sign (f x) - sign (g x)) a := by
    simp only [hi,spec,transform,Int.sub_mul,total_sub]
  have point (u v : Bool) : (sign u - sign v) * (sign u - sign v) =
      4 * (1 - sameBit false u v - sameBit true u v) := by
    cases u <;> cases v <;> decide
  simp only [line,parsevalInt,point,total_scale,total_sub,total_const,countPair]
  change 256 * (4 * (256*1 - _ - _)) = _
  omega

private theorem sqCap (z : Int) (h : z.natAbs ≤ 28) : z*z ≤ 784 := by
  have h1 : 0 ≤ 28-z := by omega
  have h2 : 0 ≤ 28+z := by omega
  have h3 := Int.mul_nonneg h1 h2
  simp only [Int.sub_mul,Int.mul_add,Int.mul_comm z 28] at h3
  omega

/-- Each type of equal pair occurs at least thirty times. Each pair
is a possible simultaneous flip of both entries on the distinguished axis. -/
theorem thirty_each (f g : Half)
    (bal : total 8 (fun x => sign (f x) + sign (g x)) = 0)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) :
    30 ≤ countPair f g false ∧ 30 ≤ countPair f g true := by
  have point (u v : Bool) : sign u + sign v =
      2 * (sameBit false u v - sameBit true u v) := by cases u <;> cases v <;> decide
  simp only [point,total_scale,total_sub] at bal
  change 2 * (countPair f g false - countPair f g true) = 0 at bal
  have ub := total_mono 8 _ (fun _ => (784:Int)) (fun a => sqCap _ (cap a))
  rw [total_const,diffEnergy] at ub
  change _ ≤ 256*784 at ub
  omega

noncomputable def flipAt (f : Half) (u x : W 8) : Bool := by
  classical
  exact if x = u then !(f x) else f x

private theorem flipSpectrum (f : Half) (u a : W 8) :
    spec (flipAt f u) a = spec f a - 2 * (sign (f u) * chr a u) := by
  classical
  have point (x : W 8) : sign (flipAt f u x) * chr a x =
      sign (f x) * chr a x - 2 * (hits u x * (sign (f x) * chr a x)) := by
    by_cases e : u = x
    · subst x; cases h : f u <;> simp [flipAt,h,hits,sign] <;> omega
    · simp [flipAt,Ne.symm e,hits,e]
  simp only [spec,transform,point,total_sub,total_scale,select]

/-- All difference-block coefficients survive. Sum-block coefficients move
from multiples of eight in [-24,24] to numbers congruent to four modulo
eight in [-28,28]. A peak in the difference block therefore persists. -/
theorem parent_spectrum (f g : Half) (u : W 8) (eqv : f u = g u)
    (hlo : ∀ a, (lo f g a).natAbs ≤ 28 ∧ lo f g a % 8 = 0) (a : W 8) :
    hi (flipAt f u) (flipAt g u) a = hi f g a ∧
    (lo (flipAt f u) (flipAt g u) a).natAbs ≤ 28 ∧
    lo (flipAt f u) (flipAt g u) a % 8 = 4 := by
  have h := hlo a
  unfold lo at h
  unfold lo hi
  rw [flipSpectrum,flipSpectrum,eqv]
  cases hg : g u <;> cases hd : dot 8 a u <;> simp [chr,sign,hd] <;> omega

private def bitI (b : Bool) : Int := if b then 1 else 0

/-- XOR of a vector-valued function over its entire domain. -/
def xorTotal {m : Nat} : (k : Nat) → (W k → W m) → W m
  | 0, v => v ()
  | k+1, v => add m (xorTotal k (fun x => v (false,x))) (xorTotal k (fun x => v (true,x)))

def supportXor {n : Nat} (f : W n → Bool) : W n :=
  xorTotal n (fun x => if f x then x else zero n)

private theorem dotTotal {m : Nat} (a : W m) (k : Nat) (v : W k → W m) :
    total k (fun x => bitI (dot m a (v x))) % 2 = bitI (dot m a (xorTotal k v)) := by
  induction k with
  | zero => cases h : dot m a (v ()) <;> simp [total,xorTotal,bitI,h]
  | succ k ih =>
    rw [total,xorTotal,dot_right]
    have L := ih (fun x => v (false,x))
    have R := ih (fun x => v (true,x))
    have bitXor (p q : Bool) : (bitI p + bitI q) % 2 = bitI (xor p q) := by
      cases p <;> cases q <;> decide
    rw [Int.add_emod,L,R,bitXor]

/-- Unnormalized Walsh residue, with the DC offset retained for an unbalanced half. -/
theorem walsh_residue_offset (f : W n → Bool) (size : 8 ∣ many n) (a : W n) :
    transform (fun x => sign (f x)) a % 8 =
      (total n (fun x => sign (f x)) + 4 * (if dot n a (supportXor f) then 1 else 0)) % 8 := by
  have D := dotTotal a n (fun x => if f x then x else zero n)
  have term (x : W n) : bitI (dot n a (if f x then x else zero n)) =
      bitI (f x && dot n a x) := by cases h : f x <;> simp [dot_zero_right]
  simp only [term] at D
  change _ = bitI (dot n a (supportXor f)) at D
  have base (u v : Bool) : sign u * sign v = sign u + sign v - 1 + 4*bitI (u && v) := by
    cases u <;> cases v <;> decide
  have ch := identity_spectrum n a
  change total n (fun x => sign (dot n a x)) = _ at ch
  simp only [transform,chr,base,total_add,total_sub,total_scale,total_const,ch]
  obtain ⟨k,hk⟩ := size
  rw [hk]
  split <;> cases h : dot n a (supportXor f) <;> rw [h] at D <;> simp only [bitI] at * <;> omega


theorem balanced_residue (f : W 9 → Bool)
    (bal : total 9 (fun x => sign (f x)) = 0) (a : W 9) :
    transform (fun x => sign (f x)) a % 8 = 4 * bitI (dot 9 a (supportXor f)) := by
  have h := walsh_residue_offset f (by decide) a
  cases e : dot 9 a (supportXor f) <;> simpa [bal,e,bitI] using h

def halves (f g : Half) (x : W 9) : Bool := if x.1 then g x.2 else f x.2

/-- The adapted support XOR gives exactly the two mod-eight Walsh blocks
used in the parent argument. -/
theorem adapted_blocks (f g : Half) (s : supportXor (halves f g) = (true,zero 8))
    (bal : total 9 (fun x => sign (halves f g x)) = 0) (a : W 8) :
    lo f g a % 8 = 0 ∧ hi f g a % 8 = 4 := by
  have H (b : Bool) := balanced_residue (halves f g) bal (b,a)
  have L := H false
  have R := H true
  rw [s,head_transform] at L R
  have phase (b : Bool) : dot 9 (b,a) (true,zero 8) = b := by
    change xor (b && true) (dot 8 a (zero 8)) = b
    rw [dot_zero_right]; cases b <;> rfl
  rw [phase] at L R
  simpa [halves,bitI,lo,hi,spec,Int.sub_eq_add_neg] using And.intro L R

private theorem dc (f g : Half) : lo f g (zero 8) =
    total 8 (fun x => sign (f x) + sign (g x)) := by
  simp [lo,spec,transform,chr,dot_zero,sign,total_add]

/-- In support-XOR adapted coordinates, every equal pair of a balanced
242 witness yields another 242 table with a constant Walsh residue of
four mod eight. An original pair of ones gives DC = 4 (weight 254);
a pair of zeros gives DC = -4 (weight 258). -/
theorem balanced_parents (f g : Half)
    (s : supportXor (halves f g) = (true,zero 8))
    (bal : total 9 (fun x => sign (halves f g x)) = 0)
    (cap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28)
    (peak : ∃ a, (lo f g a).natAbs = 28 ∨ (hi f g a).natAbs = 28) :
    30 ≤ countPair f g false ∧ 30 ≤ countPair f g true ∧
    ∀ u, f u = g u →
      lo (flipAt f u) (flipAt g u) (zero 8) = -4 * sign (f u) ∧
      (∃ a, (hi (flipAt f u) (flipAt g u) a).natAbs = 28) ∧
      ∀ a, (lo (flipAt f u) (flipAt g u) a).natAbs ≤ 28 ∧
        (hi (flipAt f u) (flipAt g u) a).natAbs ≤ 28 ∧
        lo (flipAt f u) (flipAt g u) a % 8 = 4 ∧ hi (flipAt f u) (flipAt g u) a % 8 = 4 := by
  have sum0 : total 8 (fun x => sign (f x) + sign (g x)) = 0 := by
    rw [total_add]; exact bal
  have counts := thirty_each f g sum0 (fun a => (cap a).2)
  refine ⟨counts.1,counts.2,?_⟩
  intro u hu
  have update := parent_spectrum f g u hu (fun a => ⟨(cap a).1,(adapted_blocks f g s bal a).1⟩)
  refine ⟨?_,?_,?_⟩
  · have dc0 := (dc f g).trans sum0
    unfold lo at dc0 ⊢
    rw [flipSpectrum,flipSpectrum,← hu]
    simp [chr,dot_zero,sign] at * <;> omega
  · obtain ⟨a,h⟩ := peak
    have mod8 := (adapted_blocks f g s bal a).1
    exact ⟨a, by rw [(update a).1]; rcases h with h|h <;> omega⟩
  · intro a
    rw [(update a).1]
    exact ⟨(update a).2.1,(cap a).2,(update a).2.2,(adapted_blocks f g s bal a).2⟩

/-- Converse test on a weight-254, constant-residue parent. Put the two
chosen zero entries at (false,u) and (true,u) by a linear choice of
coordinates. Their flip balances the table. Its Walsh peak is at most
28 precisely when no sum-block peak is reinforced by both flips. -/
theorem balanced_child_test (f g : Half) (u : W 8) (hf : f u = false) (hg : g u = false)
    (weight254 : lo f g (zero 8) = 4)
    (cap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28)
    (res : ∀ a, lo f g a % 8 = 4) :
    lo (flipAt f u) (flipAt g u) (zero 8) = 0 ∧
    ((∀ a, (lo (flipAt f u) (flipAt g u) a).natAbs ≤ 28 ∧
           (hi (flipAt f u) (flipAt g u) a).natAbs ≤ 28) ↔
     ∀ a, lo f g a * chr a u ≠ -28) := by
  have changeL (a : W 8) : lo (flipAt f u) (flipAt g u) a = lo f g a - 4*chr a u := by
    unfold lo; rw [flipSpectrum,flipSpectrum,hf,hg]; simp [sign]; omega
  have changeR (a : W 8) : hi (flipAt f u) (flipAt g u) a = hi f g a := by
    unfold hi; rw [flipSpectrum,flipSpectrum,hf,hg]; omega
  constructor
  · rw [changeL,weight254]; simp [chr,dot_zero,sign]
  · simp only [changeL,changeR]
    constructor
    · intro H a
      have Ha := (H a).1
      cases d : dot 8 a u <;> simp [chr,d,sign] at * <;> omega
    · intro H a
      refine ⟨?_,(cap a).2⟩
      have Ha := H a
      have P := (cap a).1
      have R := res a
      cases d : dot 8 a u <;> simp [chr,d,sign] at * <;> omega

def top (x y : Int) : Int := if x = 26 ∨ y = 26 then 1 else 0
def matchBit (x y : Int) : Int := if x = y then 1 else 0

private def val (i : Fin 7) : Int := #[-22,-14,-6,2,10,18,26][i.val]!

private theorem residues (x : Int) (hm : x % 8 = 2) (h : x.natAbs ≤ 28) :
    ∃ i : Fin 7, val i = x := by
  have A : x = -22 ∨ x = -14 ∨ x = -6 ∨ x = 2 ∨ x = 10 ∨ x = 18 ∨ x = 26 := by omega
  rcases A with h|h|h|h|h|h|h <;> subst x
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩

private theorem pairBudget : ∀ i j : Fin 7, (val i).natAbs + (val j).natAbs ≤ 28 →
    7*(val i*val i + val j*val j) + 12*(val i + val j) + 896*matchBit (val i) (val j) ≤
    3304 + 1792*top (val i) (val j) := by decide

/-- After translating and possibly complementing each odd slice, the
signed coefficients are 2 mod 8, and each signed sum is ±256. Balance
gives at least one equal normalized pair. Parseval and these signed
moments force at least 38 pairs of magnitudes 26 and 2. -/
theorem thirty_eight_top (U V : W 8 → Int)
    (res : ∀ a, U a % 8 = 2 ∧ V a % 8 = 2)
    (cap : ∀ a, (U a).natAbs + (V a).natAbs ≤ 28)
    (energy : total 8 (fun a => U a*U a + V a*V a) = 131072)
    (moment : -512 ≤ total 8 (fun a => U a + V a))
    (balancedMask : ∃ a, U a = V a) : 38 ≤ total 8 (fun a => top (U a) (V a)) := by
  have point (a : W 8) := cap a
  have B (a : W 8) : 7*(U a*U a + V a*V a) + 12*(U a+V a) + 896*matchBit (U a) (V a) ≤
      3304 + 1792*top (U a) (V a) := by
    obtain ⟨i,hi⟩ := residues (U a) (res a).1 (by have := point a; omega)
    obtain ⟨j,hj⟩ := residues (V a) (res a).2 (by have := point a; omega)
    rw [← hi,← hj]; apply pairBudget; simpa [hi,hj] using cap a
  obtain ⟨z,hz⟩ := balancedMask
  have lb (a : W 8) : hits z a ≤ matchBit (U a) (V a) := by
    by_cases eqv : z = a
    · subst a; simp [hits,matchBit,hz]
    · simp [hits,eqv,matchBit]; split <;> decide
  have M := total_mono 8 _ _ lb
  rw [diagonal] at M
  have H := total_mono 8 _ _ B
  simp only [total_add,total_const,total_scale] at H
  rw [total_add] at energy moment
  have size : many 8 = 256 := by decide
  rw [size] at H
  omega

/-- A multiset satisfying the signed moments, both energies, the zero-mask
test and the pairwise bound, with exactly 38 top pairs. No Boolean inverse
Walsh transform is asserted. The order of the masks is free here. -/
def momentRows : List (Int × Int × Int) :=
  [(-22,-6,68),(-14,-14,1),(-6,-22,68),(2,26,32),
   (10,10,1),(10,18,1),(18,10,79),(26,2,6)]

private def weighted (v : Int → Int → Int) : Int :=
  (momentRows.map (fun (a,b,n) => n * v a b)).sum

theorem moment_example :
    momentRows.all (fun (a,b,n) => decide (0 < n ∧ a%8=2 ∧ b%8=2 ∧ a.natAbs+b.natAbs ≤ 28)) = true ∧
    weighted (fun _ _ => 1) = 256 ∧ weighted (fun a _ => a) = -256 ∧
    weighted (fun _ b => b) = -256 ∧ weighted (fun a _ => a*a) = 65536 ∧
    weighted (fun _ b => b*b) = 65536 ∧ weighted matchBit = 2 ∧ weighted top = 38 := by decide

#print axioms balanced_child_test
#print axioms balanced_parents
#print axioms adapted_blocks
#print axioms moment_example
#print axioms thirty_eight_top

#print axioms thirty_each
#print axioms parent_spectrum
end Balanced242Parents
