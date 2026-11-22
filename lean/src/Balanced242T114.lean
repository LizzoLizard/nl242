/-
  Balanced242T114.lean — Unconditional, covering-radius-free zero-Mathlib Lean 4 exclusion of
  `t = 114` AND the `k = 12` branch of `t = 116`!

  Zero Mathlib, zero `sorry`, zero `native_decide`, zero `SectionEnum`,
  zero `CoveringRadius244`. Both main theorems use `[propext, Classical.choice, Quot.sound]`.

  Proof summary (pure coding theory + `Balanced242Sectors.halfspace_small_counts`):
    1. At `t = 114` (or `t = 116`), `Balanced242LowBlock.t_ge_114_forces_Z64` forces `rr = 64`,
       `Zc = 64`, and `Balanced242Z64Switch.z64_small_masks_ge_9` forces `k = |K| ≥ 9` where
       `K = clsA ∪ clsC`. The phase identity `4 * total (U * Splane) = 2*t - 232 - k` with
       `|total (U * Splane)| ≤ 4` forces `k = 12` at `t = 114`, and `k ∈ {12, 16}` at `t = 116`.
    2. `Balanced242Z64Switch.endpoint_switched_blocks` constructs complementary ternary tables
       `u, v : W 8 → Int` with `|transform u a| = 4` on `K` and `12` outside `K`.
    3. Defining Boolean halves `f' x := decide (v x + u x < 0)` and `g' x := !decide (v x - u x < 0)`
       gives `lo f' g' a = 2 * transform u a`, with `|lo f' g' a| = 8` on `K` and `24` off `K`.
    4. For every nonzero `d : W 8`:
         - `Balanced242Sectors.halfspace_small_counts` on `(f', g')` gives `#{a ∈ K : dot a d = true} ≥ 4`.
         - Picking `a0 : W 8` with `dot a0 d = true` and modulating `(f', g')` by `dot a0 x` shifts
           the spectrum by `a0`, so `halfspace_small_counts` gives `#{a ∈ K : dot a d = false} ≥ 4`.
    5. When `|K| = 12`, listing `K = [a0, ..., a11]` defines a linear map `Φ : W 9 → W 12`,
       `(c0, d) ↦ (xor c0 (dot a_i d))_{i=0..11}`, whose image has minimum Hamming weight `≥ 4`
       on all 511 nonzero inputs (`[12, 9, 4]` binary linear code).
    6. Disjoint radius-1 Hamming balls around the 512 codewords in `W 12` yield
       `512 * (1 + 12) = 6656 ≤ 4096 = |W 12|`, contradiction!

  Main exported theorems:
    * `no_t114`: **UNCONDITIONAL** exclusion of `t = 114` (ZERO `CoveringRadius244`!).
    * `t116_forces_k16`: **UNCONDITIONAL** proof that at `t = 116`, `cnt (clsA f g) + cnt (clsC f g) = 16`.
-/
import Balanced242Z64Switch

namespace Balanced242T114

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Hyperplane Balanced242Reduction
open Balanced242Plateau Balanced242Rank Balanced242Global Balanced242RankCond
open Balanced242SectionFacts Balanced242QuarticHighBlock Balanced242LowBlock
open Balanced242Z64Switch Balanced242Sectors
open Balanced242HighSections (complementary)

local notation "bind" => Balanced242Plateau.ind

/-! ## Section 1: Elementary Hamming Weight & Sphere-Packing Bound on `W 12` -/

private def hamming : ∀ {n : Nat}, W n → Int
  | 0, _ => 0
  | _ + 1, (b, x) => (if b then 1 else 0) + hamming x

private theorem hamming_nonneg {n : Nat} (x : W n) : 0 ≤ hamming x := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ m ih =>
    rcases x with ⟨b, x'⟩
    have h := ih x'
    dsimp only [hamming]
    cases b <;> omega

private theorem hamming_zero_iff {n : Nat} (x : W n) : hamming x = 0 ↔ x = zero n := by
  induction n with
  | zero =>
    rcases x with ⟨⟩
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ m ih =>
    rcases x with ⟨b, x'⟩
    dsimp only [hamming, zero]
    have hnn := hamming_nonneg x'
    constructor
    · intro h
      cases b
      · simp only [Bool.false_eq_true, if_false, Int.zero_add] at h
        rw [(ih x').mp h]
      · simp only [if_true] at h; omega
    · intro h
      have hb : b = false := congrArg Prod.fst h
      have hx : x' = zero m := congrArg Prod.snd h
      rw [hb, (ih x').mpr hx]; rfl

private theorem hamming_tri {n : Nat} (x y : W n) :
    hamming (add n x y) ≤ hamming x + hamming y := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ m ih =>
    rcases x with ⟨bx, x'⟩; rcases y with ⟨by_, y'⟩
    dsimp only [add, hamming]
    have h := ih x' y'
    cases bx <;> cases by_ <;> simp <;> omega

private theorem total_ball1 (n : Nat) :
    total n (fun y => if hamming y ≤ 1 then (1 : Int) else 0) = (n : Int) + 1 := by
  induction n with
  | zero => decide
  | succ m ih =>
    change total m (fun y => if @hamming (m + 1) (false, y) ≤ 1 then (1 : Int) else 0) +
           total m (fun y => if @hamming (m + 1) (true, y) ≤ 1 then (1 : Int) else 0) = ((m + 1 : Nat) : Int) + 1
    have hfalse : (fun y : W m => if @hamming (m + 1) (false, y) ≤ 1 then (1 : Int) else 0) =
        fun y => if hamming y ≤ 1 then (1 : Int) else 0 := by
      funext y; dsimp only [hamming]; rw [if_neg Bool.false_ne_true, Int.zero_add]
    have htrue : (fun y : W m => if @hamming (m + 1) (true, y) ≤ 1 then (1 : Int) else 0) =
        hits (zero m) := by
      funext y; dsimp only [hamming]; unfold hits
      have hnn := hamming_nonneg y
      by_cases hz : zero m = y
      · subst hz; rw [(hamming_zero_iff (zero m)).mpr rfl]; simp
      · have hne : y ≠ zero m := fun e => hz e.symm
        have hpos : ¬ hamming y = 0 := fun h0 => hne ((hamming_zero_iff y).mp h0)
        have hgt : ¬ (if true = true then (1 : Int) else 0) + hamming y ≤ 1 := by simp only [if_true]; omega
        rw [if_neg hgt, if_neg hz]
    rw [hfalse, htrue, ih, diagonal m (zero m)]; omega

private theorem total_swap_nm {n m : Nat} (F : W n → W m → Int) :
    total n (fun x => total m (fun y => F x y)) = total m (fun y => total n (fun x => F x y)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change total n (fun x => total m (fun y => F (false, x) y)) +
           total n (fun x => total m (fun y => F (true, x) y)) =
           total m (fun y => total n (fun x => F (false, x) y) + total n (fun x => F (true, x) y))
    rw [ih (fun x y => F (false, x) y), ih (fun x y => F (true, x) y), ← total_add]

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

/-- **Hamming Sphere-Packing Obstruction**: NO linear map `Φ : W 9 → W 12` has minimum
    Hamming weight `≥ 3` on all nonzero inputs (`512 * 13 = 6656 > 4096 = |W 12|`)! -/
private theorem no_code_12_9_3 (Φ : W 9 → W 12)
    (hadd : ∀ u v : W 9, Φ (add 9 u v) = add 12 (Φ u) (Φ v))
    (hdist : ∀ w : W 9, w ≠ zero 9 → 3 ≤ hamming (Φ w)) : False := by
  let ball1 (c y : W 12) : Int := if hamming (add 12 c y) ≤ 1 then 1 else 0
  -- Each codeword's radius-1 ball has size `13`:
  have hball_size (c : W 12) : total 12 (ball1 c) = 13 := by
    have hsh := sum_shift 12 c (fun y => if hamming y ≤ 1 then (1 : Int) else 0)
    change total 12 (ball1 c) = total 12 (fun y => if hamming y ≤ 1 then (1 : Int) else 0) at hsh
    rw [hsh, total_ball1 12]; decide
  -- For EVERY `y : W 12`, at most ONE `w : W 9` lies in `ball1 (Φ w) y`:
  have hdisj (y : W 12) : total 9 (fun w => ball1 (Φ w) y) ≤ 1 := by
    cases h : (worlds 9).all (fun w => !decide (hamming (add 12 (Φ w) y) ≤ 1))
    · obtain ⟨w0, _, hw0⟩ := all_false_exists _ _ h
      have h0 : hamming (add 12 (Φ w0) y) ≤ 1 := by
        by_cases e : hamming (add 12 (Φ w0) y) ≤ 1 <;> simp [e] at hw0 ⊢
      have hle (w : W 9) : ball1 (Φ w) y ≤ hits w0 w := by
        dsimp only [ball1]; unfold hits
        by_cases e : w0 = w
        · subst e; simp; split <;> decide
        · rw [if_neg e]
          have hne0 : add 9 w0 w ≠ zero 9 := by
            intro hz; apply e
            have h1 := congrArg (add 9 w0) hz
            rw [← Balanced242Plateau.add_assoc', add_self, add_zero_left, add_zero_right] at h1
            exact h1.symm
          have hge3 := hdist (add 9 w0 w) hne0
          have hcancel : Φ (add 9 w0 w) = add 12 (add 12 (Φ w0) y) (add 12 (Φ w) y) := by
            rw [hadd w0 w, add_comm 12 (Φ w) y, Balanced242Plateau.add_assoc',
                ← Balanced242Plateau.add_assoc' 12 y y (Φ w), add_self, add_zero_left]
          have htri := hamming_tri (add 12 (Φ w0) y) (add 12 (Φ w) y)
          rw [← hcancel] at htri
          have hgt1 : ¬ hamming (add 12 (Φ w) y) ≤ 1 := by omega
          rw [if_neg hgt1]; decide
      have hm := total_mono 9 _ _ hle
      rw [diagonal 9 w0] at hm; exact hm
    · rw [List.all_eq_true] at h
      have h0 : total 9 (fun w => ball1 (Φ w) y) = 0 := by
        refine Eq.trans ?_ (total_zero 9)
        apply congrArg (total 9); funext w
        have hw := h w (all_worlds 9 w)
        dsimp only [ball1]
        have hgt1 : ¬ hamming (add 12 (Φ w) y) ≤ 1 := fun e => by
          rw [decide_eq_true e] at hw; exact Bool.noConfusion hw
        rw [if_neg hgt1]
      omega
  -- Double-count `∑_{w : W 9} ∑_{y : W 12} ball1 (Φ w) y`: `6656 ≤ 4096`!
  have hlb : total 9 (fun w => total 12 (fun y => ball1 (Φ w) y)) = 6656 := by
    have h1 : (fun w : W 9 => total 12 (fun y => ball1 (Φ w) y)) = fun _ => (13 : Int) :=
      funext (fun w => hball_size (Φ w))
    rw [h1, total_const]; decide
  have hub : total 12 (fun y => total 9 (fun w => ball1 (Φ w) y)) ≤ 4096 := by
    have hm := total_mono 12 (fun y => total 9 (fun w => ball1 (Φ w) y)) (fun _ => (1 : Int)) hdisj
    rw [total_const] at hm
    have hm12 : many 12 = 4096 := by decide
    rw [hm12] at hm; omega
  rw [total_swap_nm] at hlb
  omega

/-! ## Section 2: Filtering `worlds 8` to Extract the 12 Explicit Masks of `K` -/

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

private theorem total_eq_foldl_worlds : ∀ (n : Nat) (f : W n → Int),
    total n f = (worlds n).foldl (fun acc a => acc + f a) 0 := by
  intro n; induction n with
  | zero => intro f; simp [total, worlds]
  | succ m ih =>
    intro f
    have hmap : ∀ (b : Bool) (l : List (W m)) (init : Int),
        (l.map (fun x => (b, x))).foldl (fun acc a => acc + f a) init =
        l.foldl (fun acc x => acc + f (b, x)) init := by
      intro b l; induction l with
      | nil => intro init; rfl
      | cons x xs ih' => intro init; simp only [List.map_cons, List.foldl_cons]; exact ih' _
    change total m (fun x => f (false, x)) + total m (fun x => f (true, x)) =
      ((worlds m).map (fun x => (false, x)) ++ (worlds m).map (fun x => (true, x))).foldl
        (fun acc a => acc + f a) 0
    rw [List.foldl_append, hmap false, hmap true,
        foldl_add_shift (worlds m) (fun x => f (true, x)), ← ih, ← ih]

private theorem foldl_const1 {α : Type} (l : List α) :
    l.foldl (fun acc _ => acc + (1 : Int)) 0 = (l.length : Int) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, Int.zero_add, List.length_cons]
    rw [foldl_add_shift xs (fun _ => (1 : Int)) 1, ih]; omega

private theorem filter_worlds_sum (K : W 8 → Bool) (F : W 8 → Int) :
    ((worlds 8).filter K).foldl (fun acc a => acc + F a) 0 =
      total 8 (fun a => if K a then F a else 0) := by
  rw [foldl_filter_eq, total_eq_foldl_worlds]

/-! ## Section 3: Excluding `|K| = 12` via `halfspace_small_counts` + Hamming Bound -/

/-- No complementary pair of ternary tables `(u, v)` on `W 8` can have `|transform u a| = 4`
    on a 12-element set `K` and `|transform u a| = 12` everywhere else! -/
private theorem no_switched_high_k12 (u v : W 8 → Int) (K : W 8 → Bool)
    (hcomp : ∀ x, complementary (v x) (u x))
    (hspec : ∀ a, (transform u a).natAbs = if K a then 4 else 12)
    (hk12 : total 8 (fun a => bind (K a)) = 12) : False := by
  -- Construct Boolean halves `f'`, `g'` with `lo f' g' a = 2 * transform u a`!
  let f' (x : W 8) : Bool := decide (v x + u x < 0)
  let g' (x : W 8) : Bool := !decide (v x - u x < 0)
  have hsum_fg (x : W 8) : sign (f' x) + sign (g' x) = 2 * u x := by
    rcases hcomp x with ⟨p, h | h⟩ | ⟨p, h | h⟩ <;> simp [f', g', p, h, sign]
  have hlo_eq (a : W 8) : lo f' g' a = 2 * transform u a := by
    unfold lo spec transform
    rw [← total_add]
    have hpt (x : W 8) : sign (f' x) * chr a x + sign (g' x) * chr a x = 2 * (u x * chr a x) := by
      rw [← Int.add_mul, hsum_fg x, Int.mul_assoc]
    rw [funext hpt, total_scale]
  -- Every nonzero `d : W 8` has `≥ 4` masks in `K` with `dot a d = true`:
  have htrue_ge4 (d : W 8) (hd : d ≠ zero 8) :
      4 ≤ total 8 (fun a => if K a && dot 8 a d then (1 : Int) else 0) := by
    have hlev (a : W 8) (_ : dot 8 a d = true) :
        (lo f' g' a).natAbs = 8 ∨ (lo f' g' a).natAbs = 24 := by
      rw [hlo_eq a]
      have hu := hspec a
      cases hK : K a <;> rw [hK] at hu <;> simp at hu <;> omega
    have h4 := (halfspace_small_counts f' g' d hd hlev).1
    have hpt (a : W 8) : smallIn f' g' d a = if K a && dot 8 a d then (1 : Int) else 0 := by
      unfold smallIn; rw [hlo_eq a]
      have hu := hspec a
      cases hK : K a <;> cases hd' : dot 8 a d <;> rw [hK] at hu <;> simp at hu ⊢ <;> omega
    rw [funext hpt] at h4; exact h4
  -- Every nonzero `d : W 8` ALSO has `≥ 4` masks in `K` with `dot a d = false`
  -- (by modulating `(f', g')` with `dot a0 x` where `dot a0 d = true`!):
  have hfalse_ge4 (d : W 8) (hd : d ≠ zero 8) :
      4 ≤ total 8 (fun a => if K a && !dot 8 a d then (1 : Int) else 0) := by
    obtain ⟨a0, ha0⟩ := exists_dot_true8 d hd
    let f2 (x : W 8) : Bool := xor (f' x) (dot 8 a0 x)
    let g2 (x : W 8) : Bool := xor (g' x) (dot 8 a0 x)
    have hlo2 (a : W 8) : lo f2 g2 a = lo f' g' (add 8 a a0) := by
      unfold lo spec transform
      rw [← total_add, ← total_add]
      apply congrArg (total 8); funext x
      have h1 : sign (f2 x) = sign (f' x) * chr a0 x := by
        dsimp only [f2]; unfold chr; exact signMul (f' x) (dot 8 a0 x)
      have h2 : sign (g2 x) = sign (g' x) * chr a0 x := by
        dsimp only [g2]; unfold chr; exact signMul (g' x) (dot 8 a0 x)
      have h3 : chr (add 8 a a0) x = chr a x * chr a0 x := by
        unfold chr; rw [dot_comm 8 (add 8 a a0) x, dot_right, dot_comm 8 x a, dot_comm 8 x a0]
        exact signMul (dot 8 a x) (dot 8 a0 x)
      dsimp only; rw [h1, h2, h3]; ac_rfl
    have hlev (a : W 8) (_ : dot 8 a d = true) :
        (lo f2 g2 a).natAbs = 8 ∨ (lo f2 g2 a).natAbs = 24 := by
      rw [hlo2 a, hlo_eq (add 8 a a0)]
      have hu := hspec (add 8 a a0)
      cases hK : K (add 8 a a0) <;> rw [hK] at hu <;> simp at hu <;> omega
    have h4 := (halfspace_small_counts f2 g2 d hd hlev).1
    have hpt (a : W 8) : smallIn f2 g2 d a =
        if K (add 8 a0 a) && !dot 8 (add 8 a0 a) d then (1 : Int) else 0 := by
      unfold smallIn; rw [hlo2 a, hlo_eq, add_comm 8 a a0]
      have hu := hspec (add 8 a0 a)
      have hdot : dot 8 (add 8 a0 a) d = !dot 8 a d := by
        rw [dot_comm 8 (add 8 a0 a) d, dot_right, dot_comm 8 d a0, dot_comm 8 d a, ha0]
        cases dot 8 a d <;> rfl
      rw [hdot]
      cases hK : K (add 8 a0 a) <;> cases hd' : dot 8 a d <;> rw [hK] at hu <;> simp at hu ⊢ <;> omega
    rw [funext hpt, sum_shift 8 a0 (fun a => if K a && !dot 8 a d then (1 : Int) else 0)] at h4
    exact h4
  -- Extract the 12 explicit elements of `L = (worlds 8).filter K` (keeping `L` opaque to avoid WHNF blowup!):
  obtain ⟨L, hL_def⟩ : ∃ L : List (W 8), L = (worlds 8).filter K := ⟨_, rfl⟩
  have hL_len : L.length = 12 := by
    have h1 := filter_worlds_sum K (fun _ => (1 : Int))
    rw [← hL_def, foldl_const1] at h1
    have h2 : total 8 (fun a => if K a then (1 : Int) else 0) = 12 := by
      simpa only [Balanced242Plateau.ind] using hk12
    omega
  have hL_sum (F : W 8 → Int) : L.foldl (fun acc a => acc + F a) 0 = total 8 (fun a => if K a then F a else 0) := by
    rw [hL_def]; exact filter_worlds_sum K F
  match L, hL_len, hL_sum with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], _, hsum =>
    let Φ : W 9 → W 12 := fun (c0, d) =>
      (xor c0 (dot 8 a0 d), (xor c0 (dot 8 a1 d), (xor c0 (dot 8 a2 d),
      (xor c0 (dot 8 a3 d), (xor c0 (dot 8 a4 d), (xor c0 (dot 8 a5 d),
      (xor c0 (dot 8 a6 d), (xor c0 (dot 8 a7 d), (xor c0 (dot 8 a8 d),
      (xor c0 (dot 8 a9 d), (xor c0 (dot 8 a10 d), (xor c0 (dot 8 a11 d), ()))))))))))))
    apply no_code_12_9_3 Φ
    · intro ⟨c1, d1⟩ ⟨c2, d2⟩
      have hbit (a : W 8) : xor (xor c1 c2) (dot 8 a (add 8 d1 d2)) =
          xor (xor c1 (dot 8 a d1)) (xor c2 (dot 8 a d2)) := by
        rw [dot_right]
        cases c1 <;> cases c2 <;> cases dot 8 a d1 <;> cases dot 8 a d2 <;> rfl
      change (xor (xor c1 c2) (dot 8 a0 (add 8 d1 d2)), (xor (xor c1 c2) (dot 8 a1 (add 8 d1 d2)),
             (xor (xor c1 c2) (dot 8 a2 (add 8 d1 d2)), (xor (xor c1 c2) (dot 8 a3 (add 8 d1 d2)),
             (xor (xor c1 c2) (dot 8 a4 (add 8 d1 d2)), (xor (xor c1 c2) (dot 8 a5 (add 8 d1 d2)),
             (xor (xor c1 c2) (dot 8 a6 (add 8 d1 d2)), (xor (xor c1 c2) (dot 8 a7 (add 8 d1 d2)),
             (xor (xor c1 c2) (dot 8 a8 (add 8 d1 d2)), (xor (xor c1 c2) (dot 8 a9 (add 8 d1 d2)),
             (xor (xor c1 c2) (dot 8 a10 (add 8 d1 d2)), (xor (xor c1 c2) (dot 8 a11 (add 8 d1 d2)), ())))))))))))) = _
      simp only [hbit]; rfl
    · intro ⟨c0, d⟩ hne
      by_cases hd0 : d = zero 8
      · subst hd0
        cases c0
        · exact absurd rfl hne
        · simp only [Φ, hamming, dot_zero_right]; decide
      · -- `hamming (Φ (c0, d))` equals `total 8 (fun a => if K a && xor c0 (dot a d) then 1 else 0) ≥ 4`!
        have hwt : hamming (Φ (c0, d)) =
            total 8 (fun a => if K a && xor c0 (dot 8 a d) then (1 : Int) else 0) := by
          have h1 := hsum (fun a => if xor c0 (dot 8 a d) then (1 : Int) else 0)
          have h2 : total 8 (fun a => if K a then (if xor c0 (dot 8 a d) then (1 : Int) else 0) else 0) =
              total 8 (fun a => if K a && xor c0 (dot 8 a d) then (1 : Int) else 0) := by
            apply congrArg (total 8); funext a; cases K a <;> cases xor c0 (dot 8 a d) <;> rfl
          rw [h2] at h1; rw [← h1]
          dsimp only [Φ, hamming, List.foldl]
          omega
        rw [hwt]
        cases c0
        · have hge := htrue_ge4 d hd0
          have heq : (fun a => if K a && xor false (dot 8 a d) then (1 : Int) else 0) =
              fun a => if K a && dot 8 a d then (1 : Int) else 0 := by
            funext a; simp
          rw [heq]; omega
        · have hge := hfalse_ge4 d hd0
          have heq : (fun a => if K a && xor true (dot 8 a d) then (1 : Int) else 0) =
              fun a => if K a && !dot 8 a d then (1 : Int) else 0 := by
            funext a; simp
          rw [heq]; omega

/-! ## Section 4: Main Unconditional Theorems (`no_t114` and `t116_forces_k16`) -/

private theorem z64_phase_k_values (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (ht : agreements f g = 114 ∨ agreements f g = 116) :
    (agreements f g = 114 → cnt (clsA f g) + cnt (clsC f g) = 12) ∧
    (agreements f g = 116 → cnt (clsA f g) + cnt (clsC f g) = 12 ∨ cnt (clsA f g) + cnt (clsC f g) = 16) := by
  obtain ⟨hrr, _⟩ := t_ge_114_forces_Z64 f g res dc lores locap (by omega)
  have hk9 := z64_small_masks_ge_9 f g res cap hrr
  have hph := phase_identity f g res cap
  have hm8 : many 8 = 256 := by decide
  have hMM : (128 : Int) * 128 = many 8 * rr (β8 f g) := by rw [hm8, hrr]; decide
  have hSmul (x : W 8) : transform (q8 f g) x = 128 * Splane f g x := by
    have hv := Balanced242Rank.spec_values (β8 f g) (cube8 f g res) 128 hMM x
    cases hg : good (β8 f g) x
    · have h := hv.2 hg; change transform (q8 f g) x = 0 at h; unfold Splane; rw [h]; decide
    · rcases hv.1 hg with h | h <;> change transform (q8 f g) x = _ at h <;> unfold Splane <;> rw [h] <;> decide
  have hph128 : total 8 (fun x => U f g x * transform (q8 f g) x) =
      128 * total 8 (fun x => U f g x * Splane f g x) := by
    rw [← total_scale]; apply congrArg (total 8); funext x; rw [hSmul x]; ac_rfl
  rw [hph128] at hph
  have hcnt4 : total 8 (fun x => bind (good (β8 f g) x)) = 4 := by
    have hrg := rr_good (β8 f g) (cube8 f g res)
    rw [hrr, hm8] at hrg; omega
  have hlb : -4 ≤ total 8 (fun x => U f g x * Splane f g x) := by
    have hpt (x : W 8) : -bind (good (β8 f g) x) ≤ U f g x * Splane f g x := by
      have hv := Balanced242Rank.spec_values (β8 f g) (cube8 f g res) 128 hMM x
      have hU := U_bound f g x
      cases hg : good (β8 f g) x
      · have h := hv.2 hg; change transform (q8 f g) x = 0 at h
        unfold Splane; rw [h]; simp [Balanced242Plateau.ind]
      · simp only [Balanced242Plateau.ind, if_true]
        rcases hv.1 hg with h | h <;> change transform (q8 f g) x = _ at h <;>
          unfold Splane <;> rw [h] <;> omega
    have hm := total_mono 8 _ _ hpt
    have hneg : total 8 (fun x => -bind (good (β8 f g) x)) = -total 8 (fun x => bind (good (β8 f g) x)) := by
      have h1 : (fun x => -bind (good (β8 f g) x)) = fun x => (-1 : Int) * bind (good (β8 f g) x) :=
        funext (fun x => by omega)
      rw [h1, total_scale]; omega
    rw [hneg, hcnt4] at hm; exact hm
  constructor
  · intro h114; omega
  · intro h116; omega

private theorem clsAC_sum_eq (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) :
    total 8 (fun a => bind (clsA f g a || clsC f g a)) = cnt (clsA f g) + cnt (clsC f g) := by
  unfold cnt; rw [← total_add]
  apply congrArg (total 8); funext a
  unfold clsA clsC Balanced242Reduction.ind Balanced242Plateau.ind; dsimp only
  rcases hi_values f g res cap a with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

/-- **Main Theorem 1 (`no_t114`)**: 100% UNCONDITIONAL, covering-radius-free Lean 4
    exclusion of `t = 114` (`agreements f g ≠ 114`)! -/
theorem no_t114 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (ht : agreements f g = 114) : False := by
  have hk12 := (z64_phase_k_values f g res cap dc lores locap (Or.inl ht)).1 ht
  obtain ⟨u, v, hcomp, _, hu⟩ := endpoint_switched_blocks f g res cap dc lores locap (Or.inl ht)
  exact no_switched_high_k12 u v (fun a => clsA f g a || clsC f g a) hcomp hu
    (by rw [clsAC_sum_eq f g res cap, hk12])

/-- **Main Theorem 2 (`t116_forces_k16`)**: 100% UNCONDITIONAL, covering-radius-free Lean 4
    proof that at `t = 116`, the `k = 12` branch is impossible and `k = 16` is forced! -/
theorem t116_forces_k16 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (ht : agreements f g = 116) : cnt (clsA f g) + cnt (clsC f g) = 16 := by
  rcases (z64_phase_k_values f g res cap dc lores locap (Or.inr ht)).2 ht with hk12 | hk16
  · exfalso
    obtain ⟨u, v, hcomp, _, hu⟩ := endpoint_switched_blocks f g res cap dc lores locap (Or.inr ht)
    exact no_switched_high_k12 u v (fun a => clsA f g a || clsC f g a) hcomp hu
      (by rw [clsAC_sum_eq f g res cap, hk12])
  · exact hk16

end Balanced242T114

#print axioms Balanced242T114.no_t114
#print axioms Balanced242T114.t116_forces_k16
