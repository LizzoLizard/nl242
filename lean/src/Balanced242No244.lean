/-
  Unconditional exclusion of nonlinearity ≥ 244 (`∀ a, |W_F(a)| ≤ 24`) for balanced
  nine-variable Boolean functions, and elimination of the `peak : ∃ a, |W_F(a)| = 28`
  side condition from all coordinate-free theorems:

    1. `supportXor_ne_zero_of_cap28`: any balanced `F : W 9 → Bool` with `∀ a, |W_F(a)| ≤ 28`
       automatically has `supportXor F ≠ zero 9` (since `supportXor F = 0` forces `8 ∣ W_F`,
       so `|W_F| ≤ 24`, whence quadratic-residue distance gives `#{16 ∣ W_F} ≥ 128` and
       Parseval energy `≤ 253696 < 262144`).
    2. `no_balanced_nl244`: no balanced `F : W 9 → Bool` satisfies `∀ a, |W_F(a)| ≤ 24`
       (after adapting to `supportXor F ≠ 0`, `|hi| ≤ 20` forces `t ≥ 156`, while `|lo| ≤ 24`
       forces `t ≤ 143`).
    3. `peak28_of_cap28`: any balanced `F : W 9 → Bool` with `∀ a, |W_F(a)| ≤ 28` attains
       `|W_F(a)| = 28` at some mask `a`.

  Zero `SectionEnum`, zero Mathlib, zero `Classical.choice` — only `[propext, Quot.sound]`.
-/
import Balanced242Coord
import Balanced242Plateau

namespace Balanced242No244
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Blocks Balanced242Support Balanced242Coord
open Balanced242Plateau (all_false_exists)

/-! ## Constructive Reed–Muller residue distance (`[propext, Quot.sound]`) -/

private theorem constant_mass_c {n : Nat} (F : W n → Int) (live : ∃ a, F a % 2 = 1)
    (flat : ∀ p b, (F (add n p b) - F b) % 2 = 0) : oddCount F = many n := by
  obtain ⟨a, ha⟩ := live
  have allOdd (x : W n) : F x % 2 = 1 := by
    have h := flat (add n x a) a
    have heq : add n (add n x a) a = x := by
      rw [Balanced242Plateau.add_assoc', add_self, Balanced242Plateau.add_zero_right]
    rw [heq] at h
    if h1 : F x % 2 = 1 then exact h1 else exfalso; omega
  unfold oddCount
  have e : (fun x => F x % 2) = fun _ => (1 : Int) := funext allOdd
  rw [e, total_const, Int.mul_one]

private def find_false {α : Type} (p : α → Bool) :
    ∀ l : List α, l.all p = false → { x : α // x ∈ l ∧ p x = false }
  | [], h => Bool.noConfusion h
  | a :: l, h =>
    match ha : p a with
    | false => ⟨a, List.mem_cons_self a l, ha⟩
    | true =>
      let ⟨x, hx, hpx⟩ := find_false p l (by rw [List.all_cons, ha, Bool.true_and] at h; exact h)
      ⟨x, List.mem_cons_of_mem a hx, hpx⟩

private theorem int_mod2_cases (z : Int) : z % 2 = 0 ∨ z % 2 = 1 := by
  if h0 : z % 2 = 0 then exact Or.inl h0
  else if h1 : z % 2 = 1 then exact Or.inr h1
  else exfalso; omega

theorem residue_distance_c {n : Nat} (k : Nat) (F : W n → Int)
    (live : ∃ a, F a % 2 = 1)
    (order : ∀ ds : List (W n), ds.length = k + 1 → ∀ a, differences ds F a % 2 = 0) :
    many n ≤ many k * oddCount F := by
  induction k generalizing F with
  | zero =>
    rw [constant_mass_c F live (fun p b => by simpa [differences] using order [p] rfl b)]
    change many n ≤ 1 * many n
    rw [Int.one_mul]; exact Int.le_refl _
  | succ k ih =>
    cases hflat : (worlds n).all (fun p => (worlds n).all (fun b =>
        decide ((F (add n p b) - F b) % 2 = 0)))
    · let ⟨p, _, hp⟩ := find_false _ _ hflat
      let ⟨b, _, hb⟩ := find_false _ _ hp
      have hodd : (F (add n p b) - F b) % 2 = 1 := by
        simp only [decide_eq_false_iff_not] at hb
        rcases int_mod2_cases (F (add n p b) - F b) with h0 | h1
        · exact absurd h0 hb
        · exact h1
      let D (x : W n) : Int := F (add n p x) - F x
      have bound := ih D ⟨b, hodd⟩
        (fun ds len a => order (p :: ds) (by simp [len]) a)
      have sub : oddCount D ≤ 2 * oddCount F := by
        have hpt (x : W n) : D x % 2 ≤ F (add n p x) % 2 + F x % 2 := by
          dsimp only [D]
          have h1 : (F (add n p x) - F x) % 2 = (F (add n p x) % 2 - F x % 2) % 2 := Int.sub_emod _ _ 2
          rw [h1]
          rcases int_mod2_cases (F (add n p x)) with h1' | h1' <;>
          rcases int_mod2_cases (F x) with h2' | h2' <;> rw [h1', h2'] <;> decide
        have h := total_mono n (fun x => D x % 2) (fun x => F (add n p x) % 2 + F x % 2) hpt
        rw [total_add, MaskRecovery.sum_shift n p (fun x => F x % 2)] at h
        unfold oddCount
        have h2 : total n (fun x => F x % 2) + total n (fun x => F x % 2) =
            2 * total n (fun x => F x % 2) := by
          have := Int.add_mul (1 : Int) 1 (total n (fun x => F x % 2))
          simpa [Int.one_mul] using this.symm
        rw [← h2]; exact h
      have hmn : 0 ≤ many k := Int.le_of_lt (many_pos k)
      have step := Int.mul_le_mul_of_nonneg_left sub hmn
      have hm : many (k + 1) = many k * 2 := by unfold many; rw [Int.pow_succ]
      rw [hm, Int.mul_assoc]
      exact Int.le_trans bound step
    · have flat : ∀ p b, (F (add n p b) - F b) % 2 = 0 := by
        intro p b
        have h1 := List.all_eq_true.mp hflat p (all_worlds n p)
        have h2 := List.all_eq_true.mp h1 b (all_worlds n b)
        exact of_decide_eq_true h2
      rw [constant_mass_c F live flat]
      have hm1 : (1 : Int) ≤ many (k + 1) := Int.add_one_le_iff.mpr (many_pos (k + 1))
      have hmn : 0 ≤ many n := Int.le_of_lt (many_pos n)
      have := Int.mul_le_mul_of_nonneg_right hm1 hmn
      simpa [Int.one_mul] using this

/-! ## Third differences of `booleanSpec F` are divisible by 16 -/

private theorem diff_const_zero {n : Nat} (c : Int) (ds : List (W n)) (len : ds.length = 3)
    (a : W n) : differences ds (fun _ => c) a = 0 := by
  match ds with
  | [_, _, _] => simp [differences]
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => simp at len

theorem diff_spec9_dvd16 (F : W 9 → Bool) (ds : List (W 9)) (len : ds.length = 3) (a : W 9) :
    (16 : Int) ∣ differences ds (booleanSpec F) a := by
  let I : W 9 → Int := fun x => if F x then 1 else 0
  have hspec (b : W 9) : booleanSpec F b = 512 * hits (zero 9) b - 2 * transform I b := by
    have hpt (x : W 9) : sign (F x) = 1 - 2 * I x := by
      dsimp only [I]; cases F x <;> decide
    have h1 : booleanSpec F b = total 9 (fun x => chr b x) - 2 * transform I b := by
      unfold booleanSpec
      rw [funext hpt]
      unfold transform
      have e (x : W 9) : (1 - 2 * I x) * chr b x = chr b x - 2 * (I x * chr b x) := by
        rw [Int.sub_mul, Int.one_mul, Int.mul_assoc]
      simp only [e, total_sub, total_scale]
    have hconst : total 9 (fun x => chr b x) = 512 * hits (zero 9) b := by
      have id := identity_spectrum 9 b
      change total 9 (chr b) = if b = zero 9 then many 9 else 0 at id
      rw [id]
      unfold hits
      if hb : b = zero 9 then
        subst hb; simp [many]
      else
        have hb' : ¬ zero 9 = b := fun h => hb h.symm
        simp [hb, hb']
    rw [h1, hconst]
  rw [funext hspec, diff_sub, diff_scale ds 512 (hits (zero 9)) a,
      diff_scale ds 2 (transform I) a]
  obtain ⟨k2, hk2⟩ := diff_transform_dvd ds I a
  rw [len] at hk2
  change differences ds (transform I) a = 8 * k2 at hk2
  refine ⟨32 * differences ds (hits (zero 9)) a - k2, ?_⟩
  rw [hk2]
  have h16 : (16 : Int) * (32 * differences ds (hits (zero 9)) a - k2) =
      512 * differences ds (hits (zero 9)) a - 2 * (8 * k2) := by
    rw [Int.mul_sub, ← Int.mul_assoc 16 32, ← Int.mul_assoc 2 8]; rfl
  exact h16.symm

/-! ## Main theorems: `supportXor_ne_zero_of_cap28`, `no_balanced_nl244`, `peak28_of_cap28` -/

/-- Any balanced 9-variable Boolean function with `|W_F| ≤ 28` everywhere has `supportXor F ≠ 0`. -/
theorem supportXor_ne_zero_of_cap28 (F : W 9 → Bool)
    (bal : total 9 (fun x => sign (F x)) = 0)
    (cap : ∀ a, (booleanSpec F a).natAbs ≤ 28) :
    supportXor F ≠ zero 9 := by
  intro hz
  have hres (a : W 9) : booleanSpec F a % 8 = 0 := by
    have hr := balanced_residue F bal a
    change booleanSpec F a % 8 = 4 * (if dot 9 a (supportXor F) then 1 else 0) at hr
    rw [hz, dot_zero_right] at hr
    simpa using hr
  have hdc : booleanSpec F (zero 9) = 0 := by
    unfold booleanSpec transform
    have e (x : W 9) : sign (F x) * chr (zero 9) x = sign (F x) := by
      simp [chr, dot_zero, sign]
    rw [funext e]; exact bal
  -- Quadratic residue `G a = booleanSpec F a / 8 + 1` has at least 128 odd masks (`16 ∣ W_F`)
  let G : W 9 → Int := fun a => booleanSpec F a / 8 + 1
  have hord : ∀ ds : List (W 9), ds.length = 3 → ∀ a, differences ds G a % 2 = 0 := by
    intro ds len a
    have repr (b : W 9) : 8 * G b = booleanSpec F b - (-8) := by
      dsimp only [G]
      have hdiv : 8 * (booleanSpec F b / 8) = booleanSpec F b := by
        have h := Int.ediv_add_emod (booleanSpec F b) 8
        rw [hres b, Int.add_zero] at h; exact h
      rw [Int.mul_add, hdiv]; rfl
    have e := diff_scale ds 8 G a
    rw [funext repr, diff_sub, diff_const_zero (-8) ds len a, Int.sub_zero] at e
    obtain ⟨k, hk⟩ := diff_spec9_dvd16 F ds len a
    rw [hk] at e
    have h2k : differences ds G a = 2 * k := by
      apply Int.eq_of_mul_eq_mul_left (by decide : (8 : Int) ≠ 0)
      rw [← e, ← Int.mul_assoc]; rfl
    rw [h2k]; exact Int.mul_emod_right 2 k
  have hdist := residue_distance_c 2 G ⟨zero 9, by simp [G, hdc]⟩ hord
  change 512 ≤ 4 * oddCount G at hdist
  let mark : W 9 → Int := fun a => if booleanSpec F a % 16 = 0 then 1 else 0
  have hmark : oddCount G = total 9 mark := by
    unfold oddCount
    apply congrArg (total 9); funext a
    have hr := hres a; dsimp only [G, mark]
    let q := booleanSpec F a / 16
    let r := booleanSpec F a % 16
    have hqr : 16 * q + r = booleanSpec F a := Int.ediv_add_emod (booleanSpec F a) 16
    have hr0 : r = 0 ∨ r = 8 := by
      if h0 : r = 0 then exact Or.inl h0
      else if h8 : r = 8 then exact Or.inr h8
      else exfalso; omega
    rcases hr0 with h0 | h8
    · rw [if_pos h0]
      have hdiv8 : booleanSpec F a / 8 = 2 * q := by
        apply Int.eq_of_mul_eq_mul_left (by decide : (8 : Int) ≠ 0)
        have h1 := Int.ediv_add_emod (booleanSpec F a) 8
        rw [hr, Int.add_zero] at h1
        rw [h1, ← hqr, h0, Int.add_zero, ← Int.mul_assoc]; rfl
      rw [hdiv8, Int.add_emod, Int.mul_emod_right 2 q]; rfl
    · have hne : r ≠ 0 := by rw [h8]; decide
      rw [if_neg hne]
      have hdiv8 : booleanSpec F a / 8 = 2 * q + 1 := by
        apply Int.eq_of_mul_eq_mul_left (by decide : (8 : Int) ≠ 0)
        have h1 := Int.ediv_add_emod (booleanSpec F a) 8
        rw [hr, Int.add_zero] at h1
        rw [h1, ← hqr, h8, Int.mul_add, ← Int.mul_assoc]; rfl
      rw [hdiv8]
      have h2 : 2 * q + 1 + 1 = 2 * (q + 1) := by rw [Int.mul_add, Int.add_assoc]; rfl
      rw [h2]; exact Int.mul_emod_right 2 (q + 1)
  rw [hmark] at hdist
  -- Pointwise Parseval bound: `W^2 + 320 * mark + 256 * hits 0 ≤ 576`
  have hpt (a : W 9) : booleanSpec F a * booleanSpec F a + 320 * mark a + 256 * hits (zero 9) a ≤ 576 := by
    have hc := cap a
    have hr := hres a
    if ha : a = zero 9 then
      subst ha; simp [hdc, mark, hits]
    else
      have ha' : ¬ zero 9 = a := fun h => ha h.symm
      have hhit : hits (zero 9) a = 0 := by unfold hits; simp [ha']
      rw [hhit, Int.mul_zero, Int.add_zero]
      dsimp only [mark]
      have hvals : booleanSpec F a = -24 ∨ booleanSpec F a = -16 ∨ booleanSpec F a = -8 ∨
          booleanSpec F a = 0 ∨ booleanSpec F a = 8 ∨ booleanSpec F a = 16 ∨
          booleanSpec F a = 24 := by
        if h0 : booleanSpec F a = -24 then exact Or.inl h0
        else if h1 : booleanSpec F a = -16 then exact Or.inr (Or.inl h1)
        else if h2 : booleanSpec F a = -8 then exact Or.inr (Or.inr (Or.inl h2))
        else if h3 : booleanSpec F a = 0 then exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
        else if h4 : booleanSpec F a = 8 then exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
        else if h5 : booleanSpec F a = 16 then exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
        else if h6 : booleanSpec F a = 24 then exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6)))))
        else exfalso; omega
      rcases hvals with h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hsum := total_mono 9 _ _ hpt
  rw [total_add, total_add, total_scale, total_scale, diagonal, total_const] at hsum
  have hpar : total 9 (fun a => booleanSpec F a * booleanSpec F a) = 262144 := by
    unfold booleanSpec
    rw [parsevalInt]
    have h1 (x : W 9) : sign (F x) * sign (F x) = 1 := by cases F x <;> decide
    rw [funext h1, total_const]
    decide
  rw [hpar] at hsum
  have hm512 : many 9 * (576 : Int) = 294912 := by decide
  rw [hm512] at hsum
  omega

/-- Unconditional impossibility of balanced 9-variable nonlinearity ≥ 244 (`|W_F| ≤ 24`). -/
theorem no_balanced_nl244 (F : W 9 → Bool)
    (bal : total 9 (fun x => sign (F x)) = 0)
    (cap24 : ∀ a, (booleanSpec F a).natAbs ≤ 24) : False := by
  have hs := supportXor_ne_zero_of_cap28 F bal (fun a => by have := cap24 a; omega)
  obtain ⟨f, g, haxis, hbal, hlo, hhi, _⟩ := to_adapted F bal hs
  have hlo24 (a : W 8) : (lo f g a).natAbs ≤ 24 := by
    obtain ⟨b, hb⟩ := hlo a; rw [hb]; exact cap24 b
  have hhi20 (a : W 8) : (hi f g a).natAbs ≤ 20 := by
    obtain ⟨b, hb⟩ := hhi a
    have h24 : (hi f g a).natAbs ≤ 24 := by rw [hb]; exact cap24 b
    have hr := (adapted_blocks f g haxis hbal a).2
    omega
  -- Low energy: `1024 * agreements f g ≤ 256 * 576` => `agreements f g ≤ 144`
  have hlo_ub : 1024 * agreements f g ≤ 256 * 576 := by
    have hlo_tr (a : W 8) : lo f g a = transform (fun x => sign (f x) + sign (g x)) a := by
      unfold lo spec transform
      rw [← total_add]
      apply congrArg (total 8); funext x; rw [Int.add_mul]
    have he : total 8 (fun a => lo f g a * lo f g a) = 1024 * agreements f g := by
      have sq (x : W 8) : (sign (f x) + sign (g x)) * (sign (f x) + sign (g x)) =
          4 * (sameBit false (f x) (g x) + sameBit true (f x) (g x)) := by
        cases f x <;> cases g x <;> decide
      simp only [hlo_tr, parsevalInt, sq, total_scale, total_add]
      unfold agreements countPair
      have hm256 : many 8 = 256 := by decide
      rw [hm256, ← Int.mul_assoc]; rfl
    have hpt (a : W 8) : lo f g a * lo f g a ≤ 576 := by
      have h := hlo24 a
      have hnn : 0 ≤ (24 - lo f g a) * (24 + lo f g a) := Int.mul_nonneg (by omega) (by omega)
      have hmul : (24 - lo f g a) * (24 + lo f g a) = 576 - lo f g a * lo f g a := by
        rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm (lo f g a) 24]
        have h1 : (24 : Int) * 24 = 576 := rfl
        rw [h1]
        have hsub (x y z : Int) : (x + y) - (y + z) = x - z := by
          rw [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, ← Int.add_assoc y (-y),
              Int.add_right_neg, Int.zero_add, ← Int.sub_eq_add_neg]
        exact hsub 576 (24 * lo f g a) (lo f g a * lo f g a)
      omega
    have hm := total_mono 8 _ _ hpt
    rw [he, total_const] at hm
    have hm256 : many 8 = 256 := by decide
    rw [hm256] at hm; exact hm
  -- High energy: `1024 * (256 - agreements f g) ≤ 256 * 400` => `156 ≤ agreements f g`
  have hhi_ub : 1024 * (256 - agreements f g) ≤ 256 * 400 := by
    have he := diffEnergy f g
    have hpt (a : W 8) : hi f g a * hi f g a ≤ 400 := by
      have h := hhi20 a
      have hnn : 0 ≤ (20 - hi f g a) * (20 + hi f g a) := Int.mul_nonneg (by omega) (by omega)
      have hmul : (20 - hi f g a) * (20 + hi f g a) = 400 - hi f g a * hi f g a := by
        rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm (hi f g a) 20]
        have h1 : (20 : Int) * 20 = 400 := rfl
        rw [h1]
        have hsub (x y z : Int) : (x + y) - (y + z) = x - z := by
          rw [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, ← Int.add_assoc y (-y),
              Int.add_right_neg, Int.zero_add, ← Int.sub_eq_add_neg]
        exact hsub 400 (20 * hi f g a) (hi f g a * hi f g a)
      omega
    have hm := total_mono 8 _ _ hpt
    rw [he, total_const] at hm
    have hm256 : many 8 = 256 := by decide
    rw [hm256] at hm
    unfold agreements; omega
  omega

/-- Every balanced 9-variable Boolean function with `|W_F| ≤ 28` actually attains `|W_F(a)| = 28`. -/
theorem peak28_of_cap28 (F : W 9 → Bool)
    (bal : total 9 (fun x => sign (F x)) = 0)
    (cap : ∀ a, (booleanSpec F a).natAbs ≤ 28) :
    ∃ a, (booleanSpec F a).natAbs = 28 := by
  cases hall : (worlds 9).all (fun a => decide ((booleanSpec F a).natAbs ≤ 24))
  · obtain ⟨a, _, ha⟩ := all_false_exists _ _ hall
    simp only [decide_eq_false_iff_not] at ha
    have hc := cap a
    have hr := balanced_residue F bal a
    change booleanSpec F a % 8 = 4 * (if dot 9 a (supportXor F) then 1 else 0) at hr
    refine ⟨a, ?_⟩
    if h28 : (booleanSpec F a).natAbs = 28 then exact h28
    else
      exfalso
      cases hdot : dot 9 a (supportXor F) <;> rw [hdot] at hr <;>
        simp only [Bool.false_eq_true, if_false, if_true] at hr <;> omega
  · exfalso
    apply no_balanced_nl244 F bal
    intro a
    exact of_decide_eq_true (List.all_eq_true.mp hall a (all_worlds 9 a))

end Balanced242No244

#print axioms Balanced242No244.residue_distance_c
#print axioms Balanced242No244.diff_spec9_dvd16
#print axioms Balanced242No244.supportXor_ne_zero_of_cap28
#print axioms Balanced242No244.no_balanced_nl244
#print axioms Balanced242No244.peak28_of_cap28
