/-
  Balanced242T104R8.lean — Complete, unconditional, matrix-free zero-Mathlib Lean 4 exclusion of
  rank 8 at `t = 104` (and hence rank 8 for ALL `t ≥ 104`!).

  Zero Mathlib, zero `sorry`, zero `native_decide`, zero `SectionEnum`,
  zero `Classical.choice` (`[propext, Quot.sound]` only!).

  Proof summary (combining `Balanced242LowBlock.low_autocorr_mod32` with an elementary
  bijection/pigeonhole argument on `W 8` — zero binary matrices!):
    1. At `t = 104`, `rr (β8 f g) = 1`: `Zc = 120` (`Zc = 136` exceeds budget for `t ≥ 102`),
       and `low_defect_budget` gives `n0 + 2 * n8 = 10` (`n0 ≤ 10`, `n8 ≥ 0`).
    2. Define the dual sign bit `s u := decide (q8(0) * transform q8 (u ⊕ sx) = -16)`, so
       `16 * sign (s u) = q8(0) * transform q8 (u ⊕ sx)`.
       By Walsh inversion (`involution`), `total 8 (sign ∘ s) = +16` AND
       `|transform (sign ∘ s) x| = 16` for every `x : W 8` (hence `s` has trivial polar radical!).
    3. `low_autocorr_mod32` gives `w u = (10 - transform Dlo u) / 2` is ALWAYS EVEN, and
       `sign (s u) = if (w u / 2) % 2 = 1 then 1 else -1`.
    4. Splitting `Dlo = 1_{Z0} + 2 * 1_{F8}`: any `d` orthogonal to all `a ∈ Z0` satisfies
       `c (d ⊕ v) = c v`, `c d = 0`, and linearity of `m` mod 2 forces `pol s d v = false`
       for all `v`, whence `d = 0`!
    5. Thus `u ↦ L.map (dot 8 u)` is INJECTIVE on `W 8`, where `L` lists the `n0 - 1 ≤ 9`
       nonzero zeros of `lo f g`, and every image has even parity (`c u % 2 = 0`).
    6. A 10-line pigeonhole `W 8 → W 7` rules out `L.length ≤ 8` (`256 ≤ 128`), forcing
       `L.length = 9` (`n0 = 10`, `n8 = 0`)!
    7. Then `φ : W 8 → W 8`, `u ↦ (dot u b0, ..., dot u b7)` is a BIJECTION on `W 8`
       with `w u = wt8 (φ u) + bind (par8 (φ u))`! By bijection summation,
       `total 8 (sign ∘ s) = total 8 (fun x => if ((wt8 x + bind (par8 x)) / 2) % 2 = 1 then 1 else -1) = -16`,
       contradicting `total 8 (sign ∘ s) = +16`!

  Main exported theorems:
    * `no_t104_rank8`: unconditional exclusion of `t = 104` rank 8 (`rr (β8 f g) = 1`).
    * `no_rank8_of_t_ge_104`: unconditional exclusion of rank 8 for EVERY even `t ≥ 104`!
-/
import Balanced242LowBlock

namespace Balanced242T104R8

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Hyperplane Balanced242Reduction
open Balanced242Plateau Balanced242Rank Balanced242Global Balanced242RankCond
open Balanced242SectionFacts Balanced242QuarticHighBlock Balanced242LowBlock

local notation "bind" => Balanced242Plateau.ind

private theorem exists_dot_true8 (u : W 8) (hu : u ≠ zero 8) : ∃ w : W 8, dot 8 w u = true := by
  have aux : ∀ {n : Nat} (r : W n), r ≠ zero n → ∃ w : W n, dot n w r = true := by
    intro n; induction n with
    | zero => intro r hr; exact absurd rfl hr
    | succ m ih =>
      intro r hr; rcases r with ⟨rb, r'⟩
      cases rb
      · have hr' : r' ≠ zero m := fun h => hr (by rw [h]; rfl)
        obtain ⟨w', hw'⟩ := ih r' hr'
        exact ⟨(false, w'), by simp [dot, hw']⟩
      · exact ⟨(true, zero m), by simp [dot, dot_zero]⟩
  exact aux u hu

private theorem hits_comm {n : Nat} (x y : W n) : hits x y = hits y x := by
  unfold hits
  by_cases h : x = y
  · subst h; simp
  · have h' : ¬ y = x := fun e => h e.symm; simp [h, h']

private theorem total_swap_nm {n m : Nat} (F : W n → W m → Int) :
    total n (fun x => total m (fun y => F x y)) = total m (fun y => total n (fun x => F x y)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change total n (fun x => total m (fun y => F (false, x) y)) +
           total n (fun x => total m (fun y => F (true, x) y)) =
           total m (fun y => total n (fun x => F (false, x) y) + total n (fun x => F (true, x) y))
    rw [ih (fun x y => F (false, x) y), ih (fun x y => F (true, x) y), ← total_add]

/-- Constructive fiber-count upper bound `total n (fun u => hits y (φ u)) ≤ 1` for any injective `φ : W n → W m`. -/
private theorem preCount_le_one {n m : Nat} (φ : W n → W m)
    (hinj : ∀ u v, φ u = φ v → u = v) (y : W m) :
    total n (fun u => hits y (φ u)) ≤ 1 := by
  cases h : (worlds n).all (fun u => !decide (φ u = y))
  · obtain ⟨u0, _, hu0⟩ := all_false_exists _ _ h
    have heq : φ u0 = y := by
      by_cases e : φ u0 = y
      · exact e
      · rw [decide_eq_false e] at hu0; exact Bool.noConfusion hu0
    have hpt (u : W n) : hits y (φ u) = hits u0 u := by
      unfold hits
      by_cases hu : u0 = u
      · subst hu; simp [heq]
      · have hne : ¬ y = φ u := fun h' => hu (hinj u0 u (heq.trans h'))
        simp [hu, hne]
    rw [funext hpt, diagonal]; exact Int.le_refl 1
  · rw [List.all_eq_true] at h
    have hpt (u : W n) : hits y (φ u) = 0 := by
      have hu := h u (all_worlds n u)
      have hne : ¬ y = φ u := by
        intro e; rw [← e, decide_eq_true rfl] at hu; exact Bool.noConfusion hu
      unfold hits; simp [hne]
    rw [funext hpt, total_zero]; decide

/-- Pigeonhole on hypercubes: NO injective map `W 8 → W 7` exists (`256 ≤ 128`). -/
private theorem no_inj_8_to_7 (ψ : W 8 → W 7) (hinj : ∀ u v, ψ u = ψ v → u = v) : False := by
  have hle : total 7 (fun y => total 8 (fun u => hits y (ψ u))) ≤ 128 := by
    have hm := total_mono 7 (fun y => total 8 (fun u => hits y (ψ u))) (fun _ => (1 : Int))
      (fun y => preCount_le_one ψ hinj y)
    rw [total_const] at hm
    have hm7 : many 7 = 128 := by decide
    rw [hm7] at hm; omega
  have heq : total 7 (fun y => total 8 (fun u => hits y (ψ u))) = 256 := by
    rw [total_swap_nm]
    have hpt (u : W 8) : total 7 (fun y => hits y (ψ u)) = 1 := by
      have hc : (fun y => hits y (ψ u)) = hits (ψ u) := funext (fun y => hits_comm y (ψ u))
      rw [hc, diagonal]
    rw [funext hpt, total_const]
    have hm8 : many 8 = 256 := by decide
    rw [hm8]; omega
  omega

/-- Bijection summation on `W 8`: if `φ : W 8 → W 8` is injective, then
    `total 8 (fun u => G (φ u)) = total 8 G` (zero `Nodup`, zero `Classical.choice`!). -/
private theorem total8_bijection (φ : W 8 → W 8) (hinj : ∀ u v, φ u = φ v → u = v)
    (G : W 8 → Int) : total 8 (fun u => G (φ u)) = total 8 G := by
  have hpre (y : W 8) : total 8 (fun u => hits y (φ u)) = 1 := by
    have hnn (x : W 8) : 0 ≤ 1 - total 8 (fun u => hits x (φ u)) := by
      have := preCount_le_one φ hinj x; omega
    have hsum : total 8 (fun x => 1 - total 8 (fun u => hits x (φ u))) = 0 := by
      rw [total_sub, total_const, total_swap_nm]
      have hpt (u : W 8) : total 8 (fun x => hits x (φ u)) = 1 := by
        have hc : (fun x => hits x (φ u)) = hits (φ u) := funext (fun x => hits_comm x (φ u))
        rw [hc, diagonal]
      rw [funext hpt, total_const]; omega
    have hp := point_le_total 8 _ hnn y
    rw [hsum] at hp; have h0 := hnn y; omega
  have h1 : total 8 (fun u => G (φ u)) =
      total 8 (fun u => total 8 (fun y => G y * hits y (φ u))) := by
    apply congrArg (total 8); funext u
    have hpt (y : W 8) : G y * hits y (φ u) = G (φ u) * hits (φ u) y := by
      rw [hits_comm]; unfold hits; by_cases h : φ u = y
      · subst h; simp
      · simp [h]
    rw [funext hpt, total_scale, diagonal, Int.mul_one]
  rw [h1, total_swap_nm]
  apply congrArg (total 8); funext y
  rw [total_scale, hpre y, Int.mul_one]

/-- List XOR of Booleans. -/
private def xorList : List Bool → Bool
  | [] => false
  | b :: bs => xor b (xorList bs)

/-- Sum of `bind` over a Boolean list has parity `xorList`. -/
private theorem sum_bind_mod2 (bs : List Bool) :
    (bs.foldl (fun acc b => acc + bind b) (0 : Int)) % 2 = bind (xorList bs) := by
  have aux : ∀ (l : List Bool) (acc : Int),
      (l.foldl (fun a b => a + bind b) acc) % 2 = (acc + bind (xorList l)) % 2 := by
    intro l; induction l with
    | nil => intro acc; simp [xorList, Balanced242Plateau.ind]
    | cons b bs ih =>
      intro acc
      simp only [List.foldl_cons, xorList]
      rw [ih (acc + bind b)]
      cases b <;> cases xorList bs <;> simp [Balanced242Plateau.ind] <;> omega
  have h := aux bs 0
  rw [Int.zero_add] at h
  rw [h]; cases xorList bs <;> decide

/-- Express `total n (fun a => if P a then F a else 0)` as a `foldl` over `(worlds n).filter P`! -/
private theorem foldl_add_shift {α : Type} (l : List α) (f : α → Int) (init : Int) :
    l.foldl (fun acc a => acc + f a) init = init + l.foldl (fun acc a => acc + f a) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [ih (init + f x), ih (f x)]; omega

private theorem foldl_filter_eq {α : Type} (l : List α) (P : α → Bool) (f : α → Int) :
    (l.filter P).foldl (fun acc a => acc + f a) 0 =
      l.foldl (fun acc a => acc + if P a then f a else 0) 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : P x
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, List.foldl_cons, Int.zero_add]; exact ih
    · simp only [hp, ↓reduceIte, List.foldl_cons, Int.zero_add]
      rw [foldl_add_shift (xs.filter P) f (f x),
          foldl_add_shift xs (fun a => if P a then f a else 0) (f x), ih]

private theorem list_sum_eq_foldl {α β : Type} (l : List α) (g : α → β) (f : β → Int) :
    (l.map g).foldl (fun acc b => acc + f b) 0 = l.foldl (fun acc a => acc + f (g a)) 0 := by
  have aux : ∀ (xs : List α) (init : Int),
      (xs.map g).foldl (fun acc b => acc + f b) init = xs.foldl (fun acc a => acc + f (g a)) init := by
    intro xs; induction xs with
    | nil => intro init; rfl
    | cons x xs ih => intro init; simp only [List.map_cons, List.foldl_cons]; exact ih _
  exact aux l 0

private theorem total_eq_foldl_worlds {n : Nat} (f : W n → Int) :
    total n f = (worlds n).foldl (fun acc a => acc + f a) 0 := by
  induction n with
  | zero => change f () = 0 + f (); omega
  | succ n ih =>
    change total n (fun x => f (false, x)) + total n (fun x => f (true, x)) =
      ((worlds n).map (fun x => (false, x)) ++
       (worlds n).map (fun x => (true, x))).foldl (fun acc a => acc + f a) 0
    have h0 := list_sum_eq_foldl (worlds n) (fun x : W n => ((false, x) : W (n + 1))) f
    have h1 := list_sum_eq_foldl (worlds n) (fun x : W n => ((true, x) : W (n + 1))) f
    rw [List.foldl_append, foldl_add_shift]
    congr 1
    · exact (ih (fun x => f (false, x))).trans h0.symm
    · exact (ih (fun x => f (true, x))).trans h1.symm

private theorem total_filter_eq {n : Nat} (P : W n → Bool) (f : W n → Int) :
    total n (fun a => if P a then f a else 0) =
      ((worlds n).filter P).foldl (fun acc a => acc + f a) 0 := by
  rw [foldl_filter_eq, total_eq_foldl_worlds]

private theorem foldl_const_one {α : Type} (l : List α) :
    l.foldl (fun acc _ => acc + (1 : Int)) 0 = (l.length : Int) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, Int.zero_add, List.length_cons]
    rw [foldl_add_shift, ih]
    omega

/-- Pack up to 7 Booleans into `W 7` (injectively on lists of length `≤ 7`). -/
private def pack7 (bs : List Bool) : W 7 :=
  (bs.getD 0 false, (bs.getD 1 false, (bs.getD 2 false, (bs.getD 3 false,
   (bs.getD 4 false, (bs.getD 5 false, (bs.getD 6 false, ())))))))

private theorem pack7_inj (bs cs : List Bool) (hl1 : bs.length = cs.length) (hle : bs.length ≤ 7)
    (heq : pack7 bs = pack7 cs) : bs = cs := by
  have get_eq : ∀ i, i < 7 → bs.getD i false = cs.getD i false := by
    intro i hi
    unfold pack7 at heq
    have h0 : bs.getD 0 false = cs.getD 0 false := congrArg Prod.fst heq
    have h1 : bs.getD 1 false = cs.getD 1 false := congrArg (fun p => p.2.1) heq
    have h2 : bs.getD 2 false = cs.getD 2 false := congrArg (fun p => p.2.2.1) heq
    have h3 : bs.getD 3 false = cs.getD 3 false := congrArg (fun p => p.2.2.2.1) heq
    have h4 : bs.getD 4 false = cs.getD 4 false := congrArg (fun p => p.2.2.2.2.1) heq
    have h5 : bs.getD 5 false = cs.getD 5 false := congrArg (fun p => p.2.2.2.2.2.1) heq
    have h6 : bs.getD 6 false = cs.getD 6 false := congrArg (fun p => p.2.2.2.2.2.2.1) heq
    match i with
    | 0 => exact h0 | 1 => exact h1 | 2 => exact h2 | 3 => exact h3
    | 4 => exact h4 | 5 => exact h5 | 6 => exact h6 | _ + 7 => omega
  apply List.ext_get hl1
  intro i hi1 hi2
  have h := get_eq i (by omega)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] using h

/-- Recursive Hamming weight on `W n`. -/
private def wtN : ∀ {n : Nat}, W n → Nat
  | 0, () => 0
  | _ + 1, (b, x) => (if b then 1 else 0) + wtN x

/-- Binomial sum helper for `total n (fun x => g (wtN x))`. -/
private def sumBinom : Nat → (Nat → Int) → Int
  | 0, g => g 0
  | n + 1, g => sumBinom n g + sumBinom n (fun k => g (k + 1))

private theorem total_wtN : ∀ {n : Nat} (g : Nat → Int),
    total n (fun x => g (wtN x)) = sumBinom n g
  | 0, _ => rfl
  | n + 1, g => by
    change total n (fun x => g (0 + wtN x)) + total n (fun x => g (1 + wtN x)) =
      sumBinom n g + sumBinom n (fun k => g (k + 1))
    have h0 : (fun x : W n => g (0 + wtN x)) = fun x => g (wtN x) := funext (fun x => by simp)
    have h1 : (fun x : W n => g (1 + wtN x)) = fun x => g (wtN x + 1) := funext (fun x => by rw [Nat.add_comm])
    rw [h0, h1, total_wtN g, total_wtN (fun k => g (k + 1))]

/-- Hamming weight of `x : W 8`. -/
private def wt8 (x : W 8) : Int :=
  bind x.1 + bind x.2.1 + bind x.2.2.1 + bind x.2.2.2.1 +
  bind x.2.2.2.2.1 + bind x.2.2.2.2.2.1 + bind x.2.2.2.2.2.2.1 + bind x.2.2.2.2.2.2.2.1

/-- Parity of `x : W 8`. -/
private def par8 (x : W 8) : Bool :=
  xor x.1 (xor x.2.1 (xor x.2.2.1 (xor x.2.2.2.1
    (xor x.2.2.2.2.1 (xor x.2.2.2.2.2.1 (xor x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1))))))

private theorem wt8_eq_wtN (x : W 8) :
    wt8 x = Int.ofNat (wtN x) ∧ bind (par8 x) = Int.ofNat (wtN x % 2) := by
  rcases x with ⟨b0, b1, b2, b3, b4, b5, b6, b7, ⟨⟩⟩
  unfold wt8 par8 wtN Balanced242Plateau.ind
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
  cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> decide

/-- The canonical 9-zero dual sum on `W 8` equals `-16` (pure kernel arithmetic, < 5ms!). -/
private theorem canonical_9zero_sum :
    total 8 (fun x => if ((wt8 x + bind (par8 x)) / 2) % 2 = 1 then (1 : Int) else -1) = -16 := by
  let g (k : Nat) : Int := if ((k + k % 2) / 2) % 2 = 1 then 1 else -1
  have hpt (x : W 8) :
      (if ((wt8 x + bind (par8 x)) / 2) % 2 = 1 then (1 : Int) else -1) = g (wtN x) := by
    have ⟨h1, h2⟩ := wt8_eq_wtN x
    rw [h1, h2]; dsimp only [g]
    have hadd : Int.ofNat (wtN x) + Int.ofNat (wtN x % 2) = Int.ofNat (wtN x + wtN x % 2) := rfl
    have hnat : (Int.ofNat (wtN x) + Int.ofNat (wtN x % 2)) / 2 % 2 =
        Int.ofNat (((wtN x + wtN x % 2) / 2) % 2) := by
      rw [hadd]; rfl
    rw [hnat]
    by_cases h : ((wtN x + wtN x % 2) / 2) % 2 = 1
    · rw [h]; decide
    · have hne : ¬ Int.ofNat (((wtN x + wtN x % 2) / 2) % 2) = 1 := fun e => h (Int.ofNat.inj e)
      simp only [h, hne, if_false]
  rw [funext hpt, total_wtN g]
  decide

/-- **Main Theorem (`no_t104_rank8`)**: Complete, unconditional, matrix-free Lean 4 exclusion
    of rank 8 at `t = 104`! Zero `SectionEnum`, zero covering radius, zero `Classical.choice`! -/
theorem no_t104_rank8 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (ht : agreements f g = 104)
    (hrr : rr (β8 f g) = 1) : False := by
  have hm8 : many 8 = 256 := by decide
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap
  have hZc : Zc f g = 120 := by
    rcases rank_Zc_values f g res dc lores with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hZ | hZ⟩
    · omega
    · omega
    · omega
    · omega
    · exact hZ
    · exfalso; exact no_Zc_136_of_t_ge_102 f g dc lores locap hZ (by omega)
  have htotD : total 8 (Dlo f g) = 10 := by rw [total_Dlo_eq]; omega
  -- Step 1: Dual sign `s u` from `q8(0) * transform q8 (u ⊕ sx) = ±16`.
  have htrq_val (u : W 8) :
      q8 f g (zero 8) * transform (q8 f g) (add 8 u (supportXor g)) = 16 ∨
      q8 f g (zero 8) * transform (q8 f g) (add 8 u (supportXor g)) = -16 := by
    have hgood : good (β8 f g) (add 8 u (supportXor g)) = true := by
      rcases Balanced242Global.global_levels f g res with
        ⟨_, hcnt⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact all_good f g hcnt _
      · omega
      · omega
      · omega
      · omega
    have hsq := spec_good (β8 f g) (cube8 f g res) (add 8 u (supportXor g))
    rw [hrr, hgood, hm8] at hsq
    change transform (q8 f g) (add 8 u (supportXor g)) * transform (q8 f g) (add 8 u (supportXor g)) = 256 * (1 * 1) at hsq
    have htr := sq_cases (transform (q8 f g) (add 8 u (supportXor g))) 16 (by omega)
    have hq0 : q8 f g (zero 8) = 1 ∨ q8 f g (zero 8) = -1 := sign_vals _
    rcases hq0 with h0 | h0 <;> rcases htr with h1 | h1 <;> rw [h0, h1] <;> omega
  let s (u : W 8) : Bool := decide (q8 f g (zero 8) * transform (q8 f g) (add 8 u (supportXor g)) = -16)
  have hs_spec (u : W 8) :
      16 * sign (s u) = q8 f g (zero 8) * transform (q8 f g) (add 8 u (supportXor g)) := by
    dsimp only [s]; rcases htrq_val u with h | h <;> rw [h] <;> decide
  -- Step 2: Walsh inversion gives `transform (sign ∘ s) x = 16 * q8(0) * chr sx x * q8 x`
  --         and in particular `total 8 (sign ∘ s) = 16` AND `transform (sign ∘ s) x ≠ 0`!
  have htr_s (x : W 8) :
      transform (fun u => sign (s u)) x = 16 * (q8 f g (zero 8) * chr (supportXor g) x * q8 f g x) := by
    have h16 : 16 * transform (fun u => sign (s u)) x =
        256 * (q8 f g (zero 8) * chr (supportXor g) x * q8 f g x) := by
      unfold transform; rw [← total_scale]
      have hpt (u : W 8) : 16 * (sign (s u) * chr x u) =
          q8 f g (zero 8) * (transform (q8 f g) (add 8 u (supportXor g)) * chr x u) := by
        rw [← Int.mul_assoc, hs_spec u, Int.mul_assoc]
      rw [funext hpt, total_scale]
      have hsh := sum_shift 8 (supportXor g) (fun v => transform (q8 f g) v * chr x (add 8 v (supportXor g)))
      have hre (u : W 8) : transform (q8 f g) (add 8 u (supportXor g)) * chr x u =
          transform (q8 f g) (add 8 (supportXor g) u) * chr x (add 8 (add 8 (supportXor g) u) (supportXor g)) := by
        rw [add_comm 8 (supportXor g) u, Balanced242Plateau.add_assoc', add_self, add_zero_right]
      rw [funext hre, hsh]
      have hch (v : W 8) : transform (q8 f g) v * chr x (add 8 v (supportXor g)) =
          chr (supportXor g) x * (transform (q8 f g) v * chr x v) := by
        rw [Balanced242Plateau.chr_add, show chr x (supportXor g) = chr (supportXor g) x by unfold chr; rw [dot_comm]]
        ac_rfl
      rw [funext hch, total_scale]
      have hinv := transform_involution (q8 f g) x
      rw [hm8] at hinv
      change q8 f g (zero 8) * (chr (supportXor g) x * transform (transform (q8 f g)) x) = _
      rw [hinv]; ac_rfl
    omega
  have hsum_s : total 8 (fun u => sign (s u)) = 16 := by
    have h0 := htr_s (zero 8)
    have htr0 : transform (fun u => sign (s u)) (zero 8) = total 8 (fun u => sign (s u)) := by
      unfold transform; apply congrArg (total 8); funext u
      unfold chr; rw [dot_zero]; simp [sign]
    have hch0 : chr (supportXor g) (zero 8) = 1 := by unfold chr; rw [dot_zero_right]; rfl
    have hqsq : q8 f g (zero 8) * q8 f g (zero 8) = 1 := sign_sq _
    rw [htr0, hch0, Int.mul_one] at h0
    rw [h0]; have : q8 f g (zero 8) * q8 f g (zero 8) = 1 := hqsq; omega
  have htr_s_ne0 (x : W 8) : transform (fun u => sign (s u)) x ≠ 0 := by
    rw [htr_s x]
    have hq0 : q8 f g (zero 8) = 1 ∨ q8 f g (zero 8) = -1 := sign_vals _
    have hch : chr (supportXor g) x = 1 ∨ chr (supportXor g) x = -1 := sign_vals _
    have hqx : q8 f g x = 1 ∨ q8 f g x = -1 := sign_vals _
    rcases hq0 with a | a <;> rcases hch with b | b <;> rcases hqx with c | c <;>
      rw [a, b, c] <;> decide
  -- Step 3: `low_autocorr_mod32` links `s u` directly to `w u = ∑_a Dlo a * bind (dot u a)`!
  let w (u : W 8) : Int := total 8 (fun a => Dlo f g a * bind (dot 8 u a))
  have hw_eq (u : W 8) : 2 * w u = 10 - transform (Dlo f g) u := by
    dsimp only [w]; unfold transform; rw [← total_scale, ← htotD, ← total_sub]
    apply congrArg (total 8); funext a
    unfold chr Balanced242Plateau.ind; cases dot 8 u a <;> simp [sign] <;> omega
  have hw_mod (u : W 8) :
      w u % 2 = 0 ∧ sign (s u) = if (w u / 2) % 2 = 1 then (1 : Int) else -1 := by
    have hmod := low_autocorr_mod32 f g (by rw [ht]; decide) lores locap u
    have htrZ := transform_Zset_eq f g res dc lores u
    rw [← hs_spec u] at htrZ
    have hZ_eq : transform (fun a => bind (Zset f g a)) u = 128 * hits (zero 8) u + 8 * sign (s u) := by omega
    rw [hZ_eq] at hmod
    have h2w := hw_eq u
    have hw_nn : 0 ≤ w u := total_nonneg _ (fun a => by
      unfold Dlo Balanced242Plateau.ind
      by_cases h0 : lo f g a = 0
      · simp [h0]; cases dot 8 u a <;> decide
      · by_cases h8 : (lo f g a).natAbs = 8
        · simp [h0, h8]; cases dot 8 u a <;> decide
        · simp [h0, h8])
    have hhits : hits (zero 8) u = 0 ∨ hits (zero 8) u = 1 := by
      unfold hits; split <;> omega
    have hT : transform (Dlo f g) u = 10 - 2 * w u := by omega
    rw [hT] at hmod
    cases hs : s u
    · rw [hs] at hmod; simp only [sign, Bool.false_eq_true, if_false] at hmod ⊢
      have h4 : w u % 4 = 2 := by rcases hhits with hh | hh <;> rw [hh] at hmod <;> omega
      have hdiv : (w u / 2) % 2 = 1 := by omega
      simp [hdiv]; omega
    · rw [hs] at hmod; simp only [sign, if_true] at hmod ⊢
      have h4 : w u % 4 = 0 := by rcases hhits with hh | hh <;> rw [hh] at hmod <;> omega
      have hdiv : ¬ (w u / 2) % 2 = 1 := by omega
      simp [hdiv]; omega
  -- Step 4: Split `w u = c u + 2 * m u` where `c` is on `Z0` (`lo = 0`) and `m` is on `F8` (`|lo| = 8`).
  let Z0 (a : W 8) : Bool := decide (lo f g a = 0)
  let F8 (a : W 8) : Bool := decide ((lo f g a).natAbs = 8)
  let c (u : W 8) : Int := total 8 (fun a => bind (Z0 a) * bind (dot 8 u a))
  let m (u : W 8) : Int := total 8 (fun a => bind (F8 a) * bind (dot 8 u a))
  have hw_split (u : W 8) : w u = c u + 2 * m u := by
    dsimp only [w, c, m]; rw [← total_scale, ← total_add]
    apply congrArg (total 8); funext a
    unfold Dlo Z0 F8 Balanced242Plateau.ind
    by_cases h0 : lo f g a = 0
    · rw [h0]; simp
    · by_cases h8 : (lo f g a).natAbs = 8
      · simp [h0, h8]
      · simp [h0, h8]
  have hc_even (u : W 8) : c u % 2 = 0 := by
    have := (hw_mod u).1; have := hw_split u; omega
  -- Step 5: Any `d` orthogonal to all `a ∈ Z0` MUST be `zero 8`!
  have hspan (d : W 8) (horth : ∀ a, Z0 a = true → dot 8 d a = false) : d = zero 8 := by
    by_cases hd : d = zero 8
    · exact hd
    · exfalso
      -- First prove `∀ v, sign (s (d ⊕ v)) = sign (s d) * sign (s (zero 8)) * sign (s v)`!
      -- Wait: `w(d⊕v)/2 - w(d)/2 - w(v)/2 + w(0)/2` is even!
      have hpol (v : W 8) :
          (w (add 8 d v) / 2 - w d / 2 - w v / 2 + w (zero 8) / 2) % 2 = 0 := by
        have hcdv : c (add 8 d v) = c v := by
          dsimp only [c]; apply congrArg (total 8); funext a
          cases hZa : Z0 a
          · simp [Balanced242Plateau.ind]
          · rw [dot_comm 8 (add 8 d v) a, dot_right, dot_comm 8 a d, horth a hZa, dot_comm 8 a v, Bool.false_xor]
        have hcd : c d = 0 := by
          dsimp only [c]; rw [← total_zero 8]; apply congrArg (total 8); funext a
          cases hZa : Z0 a
          · simp [Balanced242Plateau.ind]
          · rw [horth a hZa]; decide
        have hc0 : c (zero 8) = 0 := by
          dsimp only [c]; rw [← total_zero 8]; apply congrArg (total 8); funext a
          rw [dot_zero]; simp [Balanced242Plateau.ind]
        have hm0 : m (zero 8) = 0 := by
          dsimp only [m]; rw [← total_zero 8]; apply congrArg (total 8); funext a
          rw [dot_zero]; simp [Balanced242Plateau.ind]
        have hm_even : (m (add 8 d v) - m d - m v) % 2 = 0 := by
          dsimp only [m]; rw [← total_sub, ← total_sub]
          have hpt (a : W 8) :
              bind (F8 a) * bind (dot 8 (add 8 d v) a) - bind (F8 a) * bind (dot 8 d a) -
              bind (F8 a) * bind (dot 8 v a) =
              2 * (-bind (F8 a) * bind (dot 8 d a && dot 8 v a)) := by
            rw [dot_comm 8 (add 8 d v) a, dot_right, dot_comm 8 a d, dot_comm 8 a v]
            cases F8 a <;> cases dot 8 d a <;> cases dot 8 v a <;> decide
          rw [funext hpt, total_scale]; omega
        have s1 := hw_split (add 8 d v); have s2 := hw_split d
        have s3 := hw_split v; have s4 := hw_split (zero 8)
        have e1 := hc_even (add 8 d v); have e2 := hc_even d
        have e3 := hc_even v; have e4 := hc_even (zero 8)
        omega
      let c0 : Int := sign (s d) * sign (s (zero 8))
      have hshift_s (v : W 8) : sign (s (add 8 d v)) = c0 * sign (s v) := by
        have h1 := (hw_mod (add 8 d v)).2; have h2 := (hw_mod d).2
        have h3 := (hw_mod v).2; have h4 := (hw_mod (zero 8)).2
        have hp := hpol v
        dsimp only [c0]; rw [h1, h2, h3, h4]
        by_cases b1 : (w (add 8 d v) / 2) % 2 = 1 <;>
        by_cases b2 : (w d / 2) % 2 = 1 <;>
        by_cases b3 : (w v / 2) % 2 = 1 <;>
        by_cases b4 : (w (zero 8) / 2) % 2 = 1 <;>
        simp only [b1, b2, b3, b4, if_true, if_false] <;> omega
      -- Pick `x` with `c0 * chr x d = -1`!
      obtain ⟨w0, hw0⟩ := exists_dot_true8 d hd
      have hex_x : ∃ x : W 8, c0 * chr x d = -1 := by
        have hc0v : c0 = 1 ∨ c0 = -1 := by
          dsimp only [c0]; cases s d <;> cases s (zero 8) <;> decide
        rcases hc0v with h1 | hm1
        · exact ⟨w0, by rw [h1]; unfold chr; rw [hw0]; decide⟩
        · exact ⟨zero 8, by rw [hm1]; unfold chr; rw [dot_zero]; decide⟩
      obtain ⟨x, hx⟩ := hex_x
      have htr_neg : transform (fun u => sign (s u)) x = -transform (fun u => sign (s u)) x := by
        have hsh := (sum_shift 8 d (fun v => sign (s v) * chr x v)).symm
        change transform (fun u => sign (s u)) x = total 8 (fun v => sign (s (add 8 d v)) * chr x (add 8 d v)) at hsh
        have hpt (v : W 8) : sign (s (add 8 d v)) * chr x (add 8 d v) =
            (c0 * chr x d) * (sign (s v) * chr x v) := by
          rw [hshift_s v, Balanced242Plateau.chr_add]; ac_rfl
        rw [funext hpt, total_scale, hx] at hsh
        change transform (fun u => sign (s u)) x = (-1) * transform (fun u => sign (s u)) x at hsh
        omega
      have h0 : transform (fun u => sign (s u)) x = 0 := by omega
      exact htr_s_ne0 x h0
  -- Step 6: Build the explicit list `L` of nonzero zeros of `lo f g` (`L.length = n0 - 1 ≤ 9`).
  let P0 (a : W 8) : Bool := decide (a ≠ zero 8) && Z0 a
  obtain ⟨L, hL_def⟩ : ∃ L : List (W 8), L = (worlds 8).filter P0 := ⟨_, rfl⟩
  have hL_len : (L.length : Int) = n0 f g - 1 := by
    rw [← foldl_const_one L, hL_def, ← total_filter_eq P0 (fun _ => (1 : Int))]
    have hdiff : total 8 (fun a => if P0 a then (1 : Int) else 0) + 1 = n0 f g := by
      have h1 : total 8 (fun a => if P0 a then (1 : Int) else 0) + 1 =
          total 8 (fun a => (if P0 a then (1 : Int) else 0) + hits (zero 8) a) := by
        rw [total_add, diagonal 8 (zero 8)]
      rw [h1]; unfold n0
      apply congrArg (total 8); funext a
      dsimp only [P0, Z0]; unfold hits
      by_cases hz : a = zero 8
      · subst hz; simp [dc]
      · have hne : ¬ zero 8 = a := fun e => hz e.symm
        by_cases hl : lo f g a = 0 <;> simp [hz, hne, hl]
    omega
  have hL_c (u : W 8) : (L.map (dot 8 u)).foldl (fun acc b => acc + bind b) 0 = c u := by
    rw [list_sum_eq_foldl, hL_def, ← total_filter_eq P0 (fun a => bind (dot 8 u a))]
    dsimp only [c]; apply congrArg (total 8); funext a
    dsimp only [P0]
    by_cases hz : a = zero 8
    · subst hz; rw [dot_zero_right]; simp [Balanced242Plateau.ind]
    · cases Z0 a <;> simp [hz, Balanced242Plateau.ind]
  have hL_xor (u : W 8) : xorList (L.map (dot 8 u)) = false := by
    have h1 := sum_bind_mod2 (L.map (dot 8 u))
    rw [hL_c u, hc_even u] at h1
    cases hx : xorList (L.map (dot 8 u))
    · rfl
    · rw [hx] at h1; simp [Balanced242Plateau.ind] at h1
  have hL_inj (u v : W 8) (heq : L.map (dot 8 u) = L.map (dot 8 v)) : u = v := by
    have hd : add 8 u v = zero 8 := by
      apply hspan (add 8 u v)
      intro a hZa
      by_cases hz : a = zero 8
      · subst hz; exact dot_zero_right 8 _
      · have hmem : a ∈ L := by
          rw [hL_def]; exact List.mem_filter.mpr ⟨all_worlds 8 a, by simp [P0, hz, hZa]⟩
        -- From `L.map (dot 8 u) = L.map (dot 8 v)` and `a ∈ L`, `dot 8 u a = dot 8 v a`!
        have heq_a : dot 8 u a = dot 8 v a := by
          have aux : ∀ (xs : List (W 8)), xs.map (dot 8 u) = xs.map (dot 8 v) → a ∈ xs → dot 8 u a = dot 8 v a := by
            intro xs; induction xs with
            | nil => intro _ hm; exact absurd hm (List.not_mem_nil _)
            | cons x xs ih =>
              intro hm hmem'
              simp only [List.map_cons, List.cons.injEq] at hm
              rcases List.mem_cons.mp hmem' with rfl | htail
              · exact hm.1
              · exact ih hm.2 htail
          exact aux L heq hmem
        rw [dot_comm 8 (add 8 u v) a, dot_right, dot_comm 8 a u, dot_comm 8 a v, heq_a]
        exact Bool.xor_self _
    have h := congrArg (add 8 u) hd
    rw [← Balanced242Plateau.add_assoc', add_self, add_zero_left, add_zero_right] at h
    exact h.symm
  -- Step 7: Pigeonhole `W 8 → W 7` excludes `L.length ≤ 8`, forcing `L.length = 9` (`n0 = 10, n8 = 0`)!
  have hL_ge9 : 9 ≤ L.length := by
    by_cases hle8 : L.length ≤ 8
    · exfalso
      cases hL : L with
      | nil =>
        have h01 : zero 8 = (true, zero 7) := hL_inj (zero 8) (true, zero 7) (by simp [hL])
        exact Bool.noConfusion (congrArg Prod.fst h01)
      | cons b0 rest =>
        have hrest_le7 : rest.length ≤ 7 := by rw [hL] at hle8; simp at hle8; omega
        let ψ : W 8 → W 7 := fun u => pack7 (rest.map (dot 8 u))
        apply no_inj_8_to_7 ψ
        intro u v hψ
        have hrest_eq : rest.map (dot 8 u) = rest.map (dot 8 v) :=
          pack7_inj _ _ (by simp) (by simpa using hrest_le7) hψ
        have hxu := hL_xor u; have hxv := hL_xor v
        rw [hL, List.map_cons, xorList] at hxu hxv
        rw [hrest_eq] at hxu
        have hb0_eq : dot 8 u b0 = dot 8 v b0 := by
          cases h1 : dot 8 u b0 <;> cases h2 : dot 8 v b0 <;> cases h3 : xorList (rest.map (dot 8 v)) <;>
            rw [h1, h3] at hxu <;> rw [h2, h3] at hxv <;> simp at hxu hxv ⊢
        apply hL_inj u v
        rw [hL, List.map_cons, List.map_cons, hb0_eq, hrest_eq]
    · omega
  have hL_eq9 : L.length = 9 := by omega
  have hn0_10 : n0 f g = 10 := by omega
  have hn8_0 : n8 f g = 0 := by omega
  -- Since `n8 = 0`, `m u = 0` for EVERY `u : W 8`, so `w u = c u`!
  have hw_eq_c (u : W 8) : w u = c u := by
    have hm0 : m u = 0 := by
      have hle : m u ≤ n8 f g := by
        dsimp only [m]; unfold n8
        apply total_mono 8; intro a; dsimp only [F8]; unfold Balanced242Plateau.ind
        by_cases h8 : (lo f g a).natAbs = 8 <;> cases dot 8 u a <;> simp [h8]
      have hge : 0 ≤ m u := total_nonneg _ (fun a => by
        dsimp only [F8]; unfold Balanced242Plateau.ind; cases decide ((lo f g a).natAbs = 8) <;> cases dot 8 u a <;> decide)
      omega
    rw [hw_split u, hm0]; omega
  -- Step 8: Decompose `L = [b0, b1, b2, b3, b4, b5, b6, b7, b8]`, build bijection `φ : W 8 → W 8`!
  match L with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8] =>
    let φ : W 8 → W 8 := fun u =>
      (dot 8 u b0, (dot 8 u b1, (dot 8 u b2, (dot 8 u b3,
       (dot 8 u b4, (dot 8 u b5, (dot 8 u b6, (dot 8 u b7, ()))))))))
    have hb8_par (u : W 8) : dot 8 u b8 = par8 (φ u) := by
      have hx := hL_xor u
      dsimp only [List.map, xorList, par8, φ] at hx ⊢
      rw [Bool.xor_false] at hx
      have hmove : xor (dot 8 u b0) (xor (dot 8 u b1) (xor (dot 8 u b2) (xor (dot 8 u b3)
        (xor (dot 8 u b4) (xor (dot 8 u b5) (xor (dot 8 u b6) (xor (dot 8 u b7) (dot 8 u b8)))))))) =
        xor (xor (dot 8 u b0) (xor (dot 8 u b1) (xor (dot 8 u b2) (xor (dot 8 u b3)
        (xor (dot 8 u b4) (xor (dot 8 u b5) (xor (dot 8 u b6) (dot 8 u b7)))))))) (dot 8 u b8) := by
        simp only [Bool.xor_assoc]
      rw [hmove] at hx
      cases h1 : dot 8 u b8 <;>
        cases h2 : xor (dot 8 u b0) (xor (dot 8 u b1) (xor (dot 8 u b2) (xor (dot 8 u b3)
          (xor (dot 8 u b4) (xor (dot 8 u b5) (xor (dot 8 u b6) (dot 8 u b7))))))) <;>
        rw [h1, h2] at hx <;> simp at hx ⊢
    have hφ_inj (u v : W 8) (heq : φ u = φ v) : u = v := by
      have h0 : dot 8 u b0 = dot 8 v b0 := congrArg Prod.fst heq
      have h1 : dot 8 u b1 = dot 8 v b1 := congrArg (fun p => p.2.1) heq
      have h2 : dot 8 u b2 = dot 8 v b2 := congrArg (fun p => p.2.2.1) heq
      have h3 : dot 8 u b3 = dot 8 v b3 := congrArg (fun p => p.2.2.2.1) heq
      have h4 : dot 8 u b4 = dot 8 v b4 := congrArg (fun p => p.2.2.2.2.1) heq
      have h5 : dot 8 u b5 = dot 8 v b5 := congrArg (fun p => p.2.2.2.2.2.1) heq
      have h6 : dot 8 u b6 = dot 8 v b6 := congrArg (fun p => p.2.2.2.2.2.2.1) heq
      have h7 : dot 8 u b7 = dot 8 v b7 := congrArg (fun p => p.2.2.2.2.2.2.2.1) heq
      have h8 : dot 8 u b8 = dot 8 v b8 := by rw [hb8_par u, hb8_par v, heq]
      apply hL_inj u v
      simp only [List.map_cons, List.map_nil, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    have hw_phi (u : W 8) : w u = wt8 (φ u) + bind (par8 (φ u)) := by
      rw [hw_eq_c u, ← hL_c u, ← hb8_par u]
      dsimp only [List.map, List.foldl, wt8, φ]
      omega
    have hsign_phi (u : W 8) :
        sign (s u) = if ((wt8 (φ u) + bind (par8 (φ u))) / 2) % 2 = 1 then (1 : Int) else -1 := by
      rw [(hw_mod u).2, hw_phi u]
    have htot := total8_bijection φ hφ_inj
      (fun x => if ((wt8 x + bind (par8 x)) / 2) % 2 = 1 then (1 : Int) else -1)
    rw [← funext hsign_phi, hsum_s, canonical_9zero_sum] at htot
    omega
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] |
    [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] | _::_::_::_::_::_::_::_::_::_::_ =>
    simp at hL_eq9

/-- **Corollary (`no_rank8_of_t_ge_104`)**: Unconditional exclusion of rank 8 (`rr (β8 f g) = 1`)
    for EVERY even `t ≥ 104`! Zero `SectionEnum`, zero covering radius, zero `Classical.choice`! -/
theorem no_rank8_of_t_ge_104 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (ht_even : agreements f g % 2 = 0)
    (ht : 104 ≤ agreements f g) (hrr : rr (β8 f g) = 1) : False := by
  by_cases h104 : agreements f g = 104
  · exact no_t104_rank8 f g res dc lores locap h104 hrr
  · by_cases h106 : agreements f g = 106
    · exact no_t106_rank8 f g res dc lores locap h106 hrr
    · have h108 : 108 ≤ agreements f g := by omega
      rcases rank_Zc_values f g res dc lores with
        ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hZ | hZ⟩
      · omega
      · omega
      · omega
      · omega
      · exact no_Zc_120_of_t_ge_108 f g dc lores locap hZ h108
      · exact no_Zc_136_of_t_ge_102 f g dc lores locap hZ (by omega)

end Balanced242T104R8

#print axioms Balanced242T104R8.no_t104_rank8
#print axioms Balanced242T104R8.no_rank8_of_t_ge_104
