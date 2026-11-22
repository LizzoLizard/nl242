/-
  Balanced242T118.lean — 100% UNCONDITIONAL, low-block-only, zero-Mathlib Lean 4 exclusion of
  `t = 118` via the four-cell affine-subspace obstruction (`check_t118.py` / `AGREEMENT_RANGE.md`).

  Zero Mathlib, zero `sorry`, zero `native_decide`, zero `SectionEnum`,
  zero `CoveringRadius244`, zero custom axioms!

  Proof summary (uses ONLY `dc`, `lores`, `locap`, `agreements f g = 118` — no `hi` needed!):
    1. By `Balanced242Endpoint.large_support_counts` at `t = 118`:
       `|Z| = #{a : lo f g a % 16 = 0} = 64` and `n8 = #{a : |lo f g a| = 8} ≤ 8`.
    2. Using `Balanced242Support.low_residue_order` and `Balanced242Rank` on the quadratic
       indicator `β a := decide (lo f g a % 16 ≠ 0)`, `Z` is an exact linear 6-flat
       `{a : dot 8 a p = false ∧ dot 8 a q = false}` with orthogonal 2-plane `K = {0, p, q, p⊕q}`.
    3. Applying `Balanced242Sectors.halfspace_small_counts` to `p, q, p⊕q` and permuting the
       three nonzero sectors `{1, 2, 3}` forces the sorted sector counts `(c1, c2, c3)` to be
       one of `(2, 2, 2)`, `(1, 3, 3)`, `(0, 4, 4)`, or `(2, 2, 4)`.
    4. On each 4-point cell `x + K`, the Walsh transforms of `z_s(x) = ∑_{y ∈ K} H_{s,y} V(x ⊕ y)`
       are supported on sector `s` with value `2 * lo f g a`, giving:
         * `z_s(x) ≡ j_s(x) (mod 3)` for `s ∈ {1, 2, 3}` (determining `v_0..v_3` up to `z_0 % 3`),
         * exact global sums of all 8 cell moments `(∑ v^2, z_1^2, z_2^2, z_3^2, z_1 j_1, z_2 j_2,
           z_3 j_3, z_0)` equal to `4 * (118, 144 - 2 c_s, 4 c_s, 0)`,
         * invariance of all 8 moments and the empty-cell indicator `v = (0,0,0,0)` on every `x + K`.
    5. Translating each `x` within `x + K` zeroes the two pivot bits (last mask of sector 2 and
       last mask of sector 3), giving an affine map `Φ : W 8 → W (k - 2)` whose image is an
       affine subspace of `W (k - 2)` with uniform fiber size `4 * (64 / |V|)` on which every
       intra-sector mask difference is nonconstant.
    6. A pure kernel-checked enumeration (`decide +kernel`) over all RREF affine subspaces of
       `W 4`, `W 5`, `W 6` refutes every admissible subspace via the linear cuts of `check_t118.py`
       (plus the 2 integer-rounding bounds on the empty-cell count `N_empty` for the 19 surviving
       subspaces of `(0, 4, 4)`).

  Main exported theorem:
    * `no_t118`: **UNCONDITIONAL** exclusion of `agreements f g = 118` (low-block only!).
-/
import Balanced242Endpoint
import Balanced242LowBlock

namespace Balanced242T118

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Blocks Balanced242Support Balanced242Hyperplane Balanced242Reduction
open Balanced242Plateau Balanced242Rank Balanced242Global Balanced242RankCond
open Balanced242SectionFacts Balanced242QuarticHighBlock Balanced242LowBlock
open Balanced242Sectors Balanced242Endpoint

local notation "bind" => Balanced242Plateau.ind

/-! ## Section 1: Elementary `W n` & `worlds` Helpers -/

private theorem add_assoc_w {n : Nat} (a b c : W n) :
    add n (add n a b) c = add n a (add n b c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨ba, a⟩; rcases b with ⟨bb, b⟩; rcases c with ⟨bc, c⟩
    simp only [add, Bool.xor_assoc, ih]

private theorem add_cancel_l {n : Nat} (a b : W n) :
    add n a (add n a b) = b := by
  rw [← add_assoc_w, add_self, add_zero_left]

private theorem add_cancel_r {n : Nat} (a b : W n) :
    add n (add n a b) b = a := by
  rw [add_assoc_w, add_self, add_zero_right]

private theorem dot_add_l {n : Nat} (a b x : W n) :
    dot n (add n a b) x = xor (dot n a x) (dot n b x) := by
  rw [dot_comm n (add n a b) x, dot_right, dot_comm n x a, dot_comm n x b]

private theorem exists_dot_true {n : Nat} (d : W n) (hd : d ≠ zero n) :
    ∃ x : W n, dot n d x = true := by
  induction n with
  | zero => cases d; exact absurd rfl hd
  | succ n ih =>
    rcases d with ⟨b, d'⟩
    cases b with
    | true => exact ⟨(true, zero n), by simp [dot, dot_zero_right]⟩
    | false =>
      have hd' : d' ≠ zero n := fun h => hd (by rw [h]; rfl)
      obtain ⟨x', hx'⟩ := ih d' hd'
      exact ⟨(false, x'), by simp [dot, hx']⟩

private theorem worlds_nodup : ∀ (n : Nat), (worlds n).Nodup
  | 0 => by decide
  | m + 1 => by
    show ((worlds m).map (fun x => (false, x)) ++ (worlds m).map (fun x => (true, x))).Nodup
    have ih := worlds_nodup m
    have h0 : ((worlds m).map (fun x => (false, x))).Nodup :=
      List.Pairwise.map (fun x => (false, x)) (fun _ _ hab h => hab (Prod.mk.inj h).2) ih
    have h1 : ((worlds m).map (fun x => (true, x))).Nodup :=
      List.Pairwise.map (fun x => (true, x)) (fun _ _ hab h => hab (Prod.mk.inj h).2) ih
    unfold List.Nodup
    rw [List.pairwise_append]
    refine ⟨h0, h1, ?_⟩
    intro a ha b hb hab
    rw [List.mem_map] at ha hb
    rcases ha with ⟨_, _, rfl⟩
    rcases hb with ⟨_, _, rfl⟩
    exact Bool.noConfusion (Prod.mk.inj hab).1

private theorem foldl_add_shift {α : Type} (L : List α) (f : α → Int) (init : Int) :
    L.foldl (fun acc x => acc + f x) init = init + L.foldl (fun acc x => acc + f x) 0 := by
  induction L generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [ih (init + f a), ih (f a)]
    omega

private theorem foldl_append_add {α : Type} (L1 L2 : List α) (f : α → Int) :
    (L1 ++ L2).foldl (fun acc x => acc + f x) 0 =
      L1.foldl (fun acc x => acc + f x) 0 + L2.foldl (fun acc x => acc + f x) 0 := by
  rw [List.foldl_append, foldl_add_shift]

private theorem total_eq_foldl_worlds : ∀ (n : Nat) (f : W n → Int),
    total n f = (worlds n).foldl (fun acc x => acc + f x) 0
  | 0, f => by simp [total, worlds]
  | n + 1, f => by
    simp only [total, worlds]
    rw [foldl_append_add, List.foldl_map, List.foldl_map,
        total_eq_foldl_worlds n (fun x => f (false, x)),
        total_eq_foldl_worlds n (fun x => f (true, x))]

private theorem foldl_filter_eq {α : Type} (L : List α) (p : α → Bool) (f : α → Int) :
    (L.filter p).foldl (fun acc x => acc + f x) 0 =
      L.foldl (fun acc x => acc + if p x then f x else 0) 0 := by
  induction L with
  | nil => simp
  | cons a t ih =>
    cases hp : p a
    · simp only [List.filter_cons, hp, Bool.false_eq_true, if_false, List.foldl_cons, Int.zero_add]
      exact ih
    · simp only [List.filter_cons, hp, if_true, List.foldl_cons, Int.zero_add]
      rw [foldl_add_shift _ _ (f a), foldl_add_shift _ _ (f a), ih]

private theorem foldl_ones_eq_length {α : Type} (L : List α) :
    L.foldl (fun acc _ => acc + (1 : Int)) 0 = (L.length : Int) := by
  induction L with
  | nil => rfl
  | cons _ t ih =>
    simp only [List.foldl_cons, Int.zero_add, List.length_cons]
    rw [foldl_add_shift, ih]; omega

private theorem filter_worlds_length (P : W 8 → Bool) :
    (((worlds 8).filter P).length : Int) = total 8 (fun a => if P a then (1 : Int) else 0) := by
  rw [total_eq_foldl_worlds, ← foldl_filter_eq, foldl_ones_eq_length]

private theorem filter_worlds_sum (P : W 8 → Bool) (F : W 8 → Int) :
    ((worlds 8).filter P).foldl (fun acc a => acc + F a) 0 =
      total 8 (fun a => if P a then F a else 0) := by
  rw [total_eq_foldl_worlds, ← foldl_filter_eq]

private theorem total_single_eq {n : Nat} (y : W n) (f : W n → Int) :
    total n (fun z => if z = y then f z else 0) = f y := by
  induction n with
  | zero =>
    cases y; simp [total]
  | succ n ih =>
    rcases y with ⟨by_, y'⟩
    simp only [total]
    cases by_
    · have hT : total n (fun z => if (true, z) = (false, y') then f (true, z) else 0) = 0 := by
        refine Eq.trans ?_ (total_zero n)
        apply congrArg (total n); funext z; simp
      have hF : total n (fun z => if (false, z) = (false, y') then f (false, z) else 0) = f (false, y') := by
        have := ih y' (fun z => f (false, z))
        simpa only [Prod.mk.injEq, true_and] using this
      rw [hF, hT]; omega
    · have hF : total n (fun z => if (false, z) = (true, y') then f (false, z) else 0) = 0 := by
        refine Eq.trans ?_ (total_zero n)
        apply congrArg (total n); funext z; simp
      have hT : total n (fun z => if (true, z) = (true, y') then f (true, z) else 0) = f (true, y') := by
        have := ih y' (fun z => f (true, z))
        simpa only [Prod.mk.injEq, true_and] using this
      rw [hF, hT]; omega

private theorem total_nonneg_int {n : Nat} (f : W n → Int) (h : ∀ x, 0 ≤ f x) :
    0 ≤ total n f := by
  rw [← total_zero n]; exact total_mono n _ _ h

private theorem total_pos_exists {n : Nat} (p : W n → Bool)
    (hpos : 0 < total n (fun x => if p x then (1 : Int) else 0)) :
    ∃ x : W n, p x = true := by
  cases hall : (worlds n).all (fun x => !p x)
  · obtain ⟨x, _, hx⟩ := all_false_exists _ _ hall
    exact ⟨x, by revert hx; cases p x <;> decide⟩
  · exfalso
    rw [List.all_eq_true] at hall
    have hz : total n (fun x => if p x then (1 : Int) else 0) = 0 := by
      refine Eq.trans ?_ (total_zero n)
      apply congrArg (total n); funext x
      have hx := hall x (all_worlds n x)
      cases hp : p x <;> rw [hp] at hx <;> simp_all
    omega

/-! ## Section 2: Memoized `BTree`, `cosetSum`, and Complete RREF Affine Subspaces -/

/-- Complete binary tree of depth `m`, memoizing a function `W m → α` for fast kernel lookup. -/
private inductive BTree (α : Type) : Nat → Type where
  | leaf : α → BTree α 0
  | node {m : Nat} : BTree α m → BTree α m → BTree α (m + 1)

private def BTree.ofFn {α : Type} : ∀ {m : Nat}, (W m → α) → BTree α m
  | 0, f => BTree.leaf (f ())
  | _ + 1, f => BTree.node (BTree.ofFn fun x => f (false, x)) (BTree.ofFn fun x => f (true, x))

private def BTree.get {α : Type} : ∀ {m : Nat}, BTree α m → W m → α
  | 0, BTree.leaf v, _ => v
  | _ + 1, BTree.node l _, (false, x) => BTree.get l x
  | _ + 1, BTree.node _ r, (true, x) => BTree.get r x

private theorem BTree.get_ofFn {α : Type} :
    ∀ {m : Nat} (f : W m → α) (x : W m), BTree.get (BTree.ofFn f) x = f x
  | 0, _, () => rfl
  | _ + 1, f, (false, x) => BTree.get_ofFn (fun y => f (false, y)) x
  | _ + 1, f, (true, x) => BTree.get_ofFn (fun y => f (true, y)) x

/-- Sum of `f` over the affine coset `sh ⊕ span(B)`. -/
private def cosetSum {m : Nat} (f : W m → Int) : List (W m) → W m → Int
  | [], sh => f sh
  | b :: bs, sh => cosetSum f bs sh + cosetSum f bs (add m sh b)

/-- Fast tree-backed `Nat` version of `cosetSum` for `decide +kernel` (pure GMP `Nat.add`). -/
private def cosetSumNat {m : Nat} (t : BTree Nat m) : List (W m) → W m → Nat
  | [], sh => t.get sh
  | b :: bs, sh => cosetSumNat t bs sh + cosetSumNat t bs (add m sh b)

private theorem cosetSumNat_eq {m : Nat} (t : BTree Nat m) (f : W m → Int) (C : Int)
    (ht : ∀ y : W m, f y + C = (t.get y : Int)) (B : List (W m)) (sh : W m) :
    (cosetSumNat t B sh : Int) = cosetSum f B sh + (2 : Int) ^ B.length * C := by
  induction B generalizing sh with
  | nil =>
    simp only [cosetSumNat, cosetSum, List.length_nil, Int.pow_zero, Int.one_mul]
    exact (ht sh).symm
  | cons b bs ih =>
    simp only [cosetSumNat, cosetSum, List.length_cons, Int.pow_succ, Int.natCast_add]
    rw [ih sh, ih (add m sh b)]
    have hmul : (2 : Int) ^ bs.length * 2 * C = (2 : Int) ^ bs.length * C + (2 : Int) ^ bs.length * C := by
      have h1 : (2 : Int) ^ bs.length * 2 = (2 : Int) ^ bs.length + (2 : Int) ^ bs.length := by omega
      rw [h1, Int.add_mul]
    omega

private theorem cosetSum_nonneg {m : Nat} (f : W m → Int) (hf : ∀ x, 0 ≤ f x)
    (B : List (W m)) (sh : W m) : 0 ≤ cosetSum f B sh := by
  induction B generalizing sh with
  | nil => exact hf sh
  | cons b bs ih =>
    simp only [cosetSum]
    have h1 := ih sh; have h2 := ih (add m sh b); omega

private theorem cosetSum_head_le {m : Nat} (f : W m → Int) (hf : ∀ x, 0 ≤ f x)
    (B : List (W m)) (sh : W m) : f sh ≤ cosetSum f B sh := by
  induction B generalizing sh with
  | nil => simp [cosetSum]
  | cons b bs ih =>
    simp only [cosetSum]
    have h1 := ih sh
    have h2 := cosetSum_nonneg f hf bs (add m sh b)
    omega

private theorem cosetSum_const {m : Nat} (B : List (W m)) (sh : W m) :
    cosetSum (fun _ => (1 : Int)) B sh = (2 : Int) ^ B.length := by
  induction B generalizing sh with
  | nil => rfl
  | cons b bs ih =>
    simp only [cosetSum, ih, List.length_cons, Int.pow_succ]
    omega

private theorem cosetSum_map_lift {m : Nat} (f : W (m + 1) → Int) (B : List (W m))
    (sb : Bool) (sh : W m) :
    cosetSum f (B.map fun b => (false, b)) (sb, sh) = cosetSum (fun y => f (sb, y)) B sh := by
  induction B generalizing sh with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, cosetSum, add, Bool.xor_false, ih]

private theorem cosetSum_shift {m : Nat} (f : W m → Int) (B : List (W m)) (u sh : W m) :
    cosetSum f B (add m sh u) = cosetSum (fun y => f (add m y u)) B sh := by
  induction B generalizing sh with
  | nil => rfl
  | cons b bs ih =>
    simp only [cosetSum]
    have h1 := ih sh
    have h2 : add m (add m sh u) b = add m (add m sh b) u := by
      rw [add_assoc_w, add_comm m u b, ← add_assoc_w]
    rw [h1, h2, ih (add m sh b)]

/-- Continuation-passing RREF enumeration of every linear subspace `B` of `W m` together with
    its canonical coset shifts `shs` (vectors supported on non-pivot coordinates).
    Zero flat-list allocation; maximum recursion depth ≤ 69 for `m = 6`. -/
private def rrefAll : (m : Nat) → (List (W m) → List (W m) → Bool) → Bool
  | 0, P => P [] [()]
  | m + 1, P =>
    rrefAll m fun B0 shs0 =>
      let B_lift := B0.map fun b => (false, b)
      let shs_false := shs0.map fun s => (false, s)
      let shs_both := shs_false ++ shs0.map fun s => (true, s)
      P B_lift shs_both && shs0.all fun u0 => P ((true, u0) :: B_lift) shs_false

/-- Completeness of `rrefAll`: if `rrefAll m P = true`, EVERY linear subspace `V ⊆ W m` has
    some RREF witness `(B, shs)` with `P B shs = true`, exact coset summation, and exact
    orthogonal-functional witness property. -/
private theorem exists_rref : ∀ (m : Nat) (V : W m → Bool),
    V (zero m) = true →
    (∀ x y, V x = true → V y = true → V (add m x y) = true) →
    ∀ (P : List (W m) → List (W m) → Bool),
    rrefAll m P = true →
    ∃ B shs, P B shs = true ∧
      B.length ≤ m ∧
      (∀ d : W m, (∀ b ∈ B, dot m d b = false) → ∀ v : W m, V v = true → dot m d v = false) ∧
      (∀ s : W m, ∃ sh ∈ shs, ∀ f : W m → Int,
        cosetSum f B sh = total m (fun y => if V (add m y s) then f y else 0))
  | 0, V, h0, _, P, hP => by
    refine ⟨[], [()], hP, by decide, ?_, ?_⟩
    · intro d _ v _; cases d; cases v; rfl
    · intro s; refine ⟨(), by simp, fun f => ?_⟩
      cases s; simp only [cosetSum, total, add]
      have hv : V () = true := h0
      simp [hv]
  | m + 1, V, h0, hadd, P, hP => by
    let V0 : W m → Bool := fun y => V (false, y)
    have hV0_zero : V0 (zero m) = true := h0
    have hV0_add : ∀ x y, V0 x = true → V0 y = true → V0 (add m x y) = true := by
      intro x y hx hy
      have := hadd (false, x) (false, y) hx hy
      simpa only [V0, add, Bool.false_xor] using this
    let Q : List (W m) → List (W m) → Bool := fun B0 shs0 =>
      let B_lift := B0.map fun b => (false, b)
      let shs_false := shs0.map fun s => (false, s)
      let shs_both := shs_false ++ shs0.map fun s => (true, s)
      P B_lift shs_both && shs0.all fun u0 => P ((true, u0) :: B_lift) shs_false
    obtain ⟨B0, shs0, hQ0, hlen0, hspan0, hcos0⟩ := exists_rref m V0 hV0_zero hV0_add Q hP
    simp only [Q, Bool.and_eq_true, List.all_eq_true] at hQ0
    have hP_case1 := hQ0.1
    have hP_case2 := hQ0.2
    have hV_add_iff (x y : W (m + 1)) (hx : V x = true) : V (add (m + 1) x y) = V y := by
      cases hy : V y
      · cases hxy : V (add (m + 1) x y)
        · rfl
        · have := hadd x (add (m + 1) x y) hx hxy
          rw [add_cancel_l] at this; rw [this] at hy; exact absurd hy (by decide)
      · exact hadd x y hx hy
    cases hall : (worlds m).all (fun u => !V (true, u))
    · -- Case 2: some `u : W m` has `V (true, u) = true`
      obtain ⟨u, _, hu_neg⟩ := all_false_exists _ _ hall
      have hu : V (true, u) = true := by revert hu_neg; cases V (true, u) <;> decide
      obtain ⟨u0, hu0_mem, hu0_cos⟩ := hcos0 u
      -- Prove `V0 (add m u0 u) = true` from `cosetSum` on the complement indicator
      have hu0_V0 : V0 (add m u0 u) = true := by
        let g : W m → Int := fun y => if V0 (add m y u) then 0 else 1
        have htot0 : total m (fun y => if V0 (add m y u) then g y else 0) = 0 := by
          refine Eq.trans ?_ (total_zero m)
          apply congrArg (total m); funext y
          dsimp only [g]; cases V0 (add m y u) <;> rfl
        have hcs0 : cosetSum g B0 u0 = 0 := (hu0_cos g).trans htot0
        have hle := cosetSum_head_le g (fun y => by dsimp only [g]; split <;> omega) B0 u0
        rw [hcs0] at hle
        dsimp only [g] at hle
        cases hv : V0 (add m u0 u)
        · rw [hv] at hle; simp at hle
        · rfl
      have hu0_V : V (true, u0) = true := by
        have h := hadd (true, u) (false, add m u0 u) hu hu0_V0
        simp only [add, Bool.xor_false] at h
        rw [add_comm m u0 u, add_cancel_l] at h
        exact h
      have hV_true_eq (z : W m) : V (true, z) = V0 (add m z u0) := by
        have h := hV_add_iff (true, u0) (true, z) hu0_V
        simp only [add, Bool.xor_self] at h
        rw [add_comm m u0 z] at h
        exact h.symm
      let B_lift := B0.map fun b => (false, b)
      let shs_false := shs0.map fun s => (false, s)
      refine ⟨(true, u0) :: B_lift, shs_false, hP_case2 u0 hu0_mem, ?_, ?_, ?_⟩
      · simp only [List.length_cons, B_lift, List.length_map]; omega
      · intro d hd v hv
        rcases d with ⟨db, d0⟩; rcases v with ⟨vb, v0⟩
        have hdu0 : dot (m + 1) (db, d0) (true, u0) = false := hd _ (List.mem_cons_self _ _)
        have hd0 : ∀ b ∈ B0, dot m d0 b = false := by
          intro b hb
          have h := hd (false, b) (List.mem_cons_of_mem _ (List.mem_map_of_mem _ hb))
          simpa only [dot, Bool.and_false, Bool.false_xor] using h
        cases vb with
        | false =>
          simp only [dot, Bool.and_false, Bool.false_xor]
          exact hspan0 d0 hd0 v0 hv
        | true =>
          have hv0' : V0 (add m v0 u0) = true := by rw [← hV_true_eq]; exact hv
          have hdot_sum := hspan0 d0 hd0 (add m v0 u0) hv0'
          rw [dot_right] at hdot_sum
          simp only [dot, Bool.and_true] at hdu0 ⊢
          revert hdu0 hdot_sum
          cases db <;> cases dot m d0 v0 <;> cases dot m d0 u0 <;> decide
      · intro s
        rcases s with ⟨sb, s0⟩
        let s' := if sb then add m s0 u0 else s0
        obtain ⟨sh0, hsh0_mem, hsh0_cos⟩ := hcos0 s'
        refine ⟨(false, sh0), List.mem_map_of_mem _ hsh0_mem, fun f => ?_⟩
        simp only [cosetSum, add, Bool.false_xor]
        rw [cosetSum_map_lift f B0 false sh0,
            cosetSum_map_lift f B0 true (add m sh0 u0),
            cosetSum_shift (fun y => f (true, y)) B0 u0 sh0,
            hsh0_cos (fun y => f (false, y)),
            hsh0_cos (fun y => f (true, add m y u0))]
        have hsh_sum := sum_shift m u0 (fun y => if V0 (add m y s') then f (true, add m y u0) else 0)
        simp only [add_assoc_w, add_self, add_zero_right] at hsh_sum
        -- Note: `add m (add m u0 y) u0 = y`
        have hsh2 : total m (fun y => if V0 (add m y s') then f (true, add m y u0) else 0) =
            total m (fun y => if V0 (add m (add m y u0) s') then f (true, y) else 0) := by
          rw [← sum_shift m u0 (fun y => if V0 (add m y s') then f (true, add m y u0) else 0)]
          apply congrArg (total m); funext y
          rw [add_comm m u0 y, add_cancel_r]
        rw [hsh2]
        simp only [total, add]
        have hF : total m (fun y => if V0 (add m y s') then f (false, y) else 0) =
            total m (fun y => if V (xor false sb, add m y s0) then f (false, y) else 0) := by
          apply congrArg (total m); funext y
          cases sb with
          | false => rfl
          | true =>
            simp only [s', if_true, Bool.false_xor, hV_true_eq, add_assoc_w]
        have hT : total m (fun y => if V0 (add m (add m y u0) s') then f (true, y) else 0) =
            total m (fun y => if V (xor true sb, add m y s0) then f (true, y) else 0) := by
          apply congrArg (total m); funext y
          cases sb with
          | false =>
            simp only [s', Bool.false_eq_true, if_false, Bool.xor_false, hV_true_eq]
            rw [add_assoc_w, add_comm m u0 s0, ← add_assoc_w]
          | true =>
            simp only [s', if_true, Bool.xor_self]
            have heq : add m (add m y u0) (add m s0 u0) = add m y s0 := by
              rw [add_assoc_w, ← add_assoc_w u0 s0 u0, add_comm m u0 s0,
                  add_assoc_w s0 u0 u0, add_self, add_zero_right]
            rw [heq]
        rw [hF, hT]
    · -- Case 1: `∀ u : W m, V (true, u) = false`
      rw [List.all_eq_true] at hall
      have hV_true_false (u : W m) : V (true, u) = false := by
        have h := hall u (all_worlds m u)
        revert h; cases V (true, u) <;> decide
      let B_lift := B0.map fun b => (false, b)
      let shs_false := shs0.map fun s => (false, s)
      let shs_both := shs_false ++ shs0.map fun s => (true, s)
      refine ⟨B_lift, shs_both, hP_case1, ?_, ?_, ?_⟩
      · simp only [B_lift, List.length_map]; omega
      · intro d hd v hv
        rcases d with ⟨db, d0⟩; rcases v with ⟨vb, v0⟩
        cases vb with
        | true => rw [hV_true_false v0] at hv; exact absurd hv (by decide)
        | false =>
          have hd0 : ∀ b ∈ B0, dot m d0 b = false := by
            intro b hb
            have h := hd (false, b) (List.mem_map_of_mem _ hb)
            simpa only [dot, Bool.and_false, Bool.false_xor] using h
          simp only [dot, Bool.and_false, Bool.false_xor]
          exact hspan0 d0 hd0 v0 hv
      · intro s
        rcases s with ⟨sb, s0⟩
        obtain ⟨sh0, hsh0_mem, hsh0_cos⟩ := hcos0 s0
        have hsh_mem : (sb, sh0) ∈ shs_both := by
          cases sb
          · exact List.mem_append_left _ (List.mem_map_of_mem _ hsh0_mem)
          · exact List.mem_append_right _ (List.mem_map_of_mem _ hsh0_mem)
        refine ⟨(sb, sh0), hsh_mem, fun f => ?_⟩
        rw [cosetSum_map_lift f B0 sb sh0, hsh0_cos (fun y => f (sb, y))]
        simp only [total, add]
        cases sb with
        | false =>
          have hT : total m (fun y => if V (true, add m y s0) then f (true, y) else 0) = 0 := by
            refine Eq.trans ?_ (total_zero m)
            apply congrArg (total m); funext y; simp [hV_true_false]
          simp only [Bool.false_xor, Bool.xor_false, hT, Int.add_zero]
        | true =>
          have hF : total m (fun y => if V (true, add m y s0) then f (false, y) else 0) = 0 := by
            refine Eq.trans ?_ (total_zero m)
            apply congrArg (total m); funext y; simp [hV_true_false]
          simp only [Bool.false_xor, Bool.xor_self, hF, Int.zero_add]

private def multOfLenNat : Nat → Nat
  | 0 => 64
  | 1 => 32
  | 2 => 16
  | 3 => 8
  | 4 => 4
  | 5 => 2
  | _ => 1

private def multOfLen (k : Nat) : Int := (multOfLenNat k : Int)

private theorem pow2_mul_multOfLen (k : Nat) (hk : k ≤ 6) :
    (2 : Int) ^ k * multOfLen k = 64 := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => decide
  | k + 7 => omega

/-- For any linear map `L : W 8 → W m` (`m ≤ 6`) and offset `shift : W m`, whenever
    `rrefAll m P = true`, there exists a canonical RREF witness `(B, shs)` with `P B shs = true`
    and `sh ∈ shs` such that for EVERY function `f : W m → Int`,
    `total 8 (f ∘ Φ) = 4 * multOfLen B.length * cosetSum f B sh`,
    and every linear functional nonconstant on `Im(L)` is nonzero on some `b ∈ B`. -/
private theorem affine_image_rref {m : Nat} (hm : m ≤ 6) (L : W 8 → W m)
    (hL : ∀ x y, L (add 8 x y) = add m (L x) (L y)) (shift : W m)
    (P : List (W m) → List (W m) → Bool) (hP : rrefAll m P = true) :
    ∃ B shs sh, P B shs = true ∧ sh ∈ shs ∧ B.length ≤ m ∧
      (∀ d : W m, (∃ x : W 8, dot m d (L x) = true) → B.any (fun b => dot m d b) = true) ∧
      (∀ f : W m → Int,
        total 8 (fun x => f (add m shift (L x))) =
          4 * multOfLen B.length * cosetSum f B sh) := by
  have hL0 : L (zero 8) = zero m := by
    have h := hL (zero 8) (zero 8)
    rw [add_self] at h
    have h2 := congrArg (add m (L (zero 8))) h
    rw [add_self, add_zero_right] at h2
    exact h2.symm
  let V : W m → Bool := fun y => (worlds 8).any (fun x => decide (L x = y))
  have hV_spec (y : W m) : V y = true ↔ ∃ x : W 8, L x = y := by
    simp only [V, List.any_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨x, _, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, all_worlds 8 x, hx⟩⟩
  have hV0 : V (zero m) = true := (hV_spec _).2 ⟨zero 8, hL0⟩
  have hVadd : ∀ y1 y2, V y1 = true → V y2 = true → V (add m y1 y2) = true := by
    intro y1 y2 h1 h2
    obtain ⟨x1, rfl⟩ := (hV_spec _).1 h1
    obtain ⟨x2, rfl⟩ := (hV_spec _).1 h2
    exact (hV_spec _).2 ⟨add 8 x1 x2, hL x1 x2⟩
  obtain ⟨B, shs, hmem, hlen, hspan, hcos⟩ := exists_rref m V hV0 hVadd P hP
  obtain ⟨sh, hsh_mem, hsh_cos⟩ := hcos shift
  let K : Int := total 8 (fun x => if L x = zero m then (1 : Int) else 0)
  have hfiber (y : W m) :
      total 8 (fun x => if L x = y then (1 : Int) else 0) = if V y then K else 0 := by
    cases hvy : V y with
    | false =>
      simp only [Bool.false_eq_true, if_false]
      refine Eq.trans ?_ (total_zero 8)
      apply congrArg (total 8); funext x
      have hne : L x ≠ y := fun h => by
        have := (hV_spec y).2 ⟨x, h⟩; rw [hvy] at this; exact absurd this (by decide)
      simp [hne]
    | true =>
      simp only [if_true]
      obtain ⟨x0, hx0⟩ := (hV_spec y).1 hvy
      rw [← sum_shift 8 x0 (fun x => if L x = y then (1 : Int) else 0)]
      apply congrArg (total 8); funext x
      rw [hL x0 x, hx0]
      have hiff : add m y (L x) = y ↔ L x = zero m := by
        constructor
        · intro h
          have h2 := congrArg (add m y) h
          rw [add_cancel_l, add_self] at h2; exact h2
        · intro h; rw [h, add_zero_right]
      by_cases h : L x = zero m
      · rw [if_pos (hiff.2 h), if_pos h]
      · rw [if_neg (fun e => h (hiff.1 e)), if_neg h]
  have hpush (f : W m → Int) :
      total 8 (fun x => f (add m shift (L x))) = K * cosetSum f B sh := by
    have h1 : total 8 (fun x => f (add m shift (L x))) =
        total 8 (fun x => total m (fun y => if y = add m shift (L x) then f y else 0)) := by
      apply congrArg (total 8); funext x
      exact (total_single_eq (add m shift (L x)) f).symm
    rw [h1, swap]
    have h2 : total m (fun y => total 8 (fun x => if y = add m shift (L x) then f y else 0)) =
        total m (fun y => K * (if V (add m y shift) then f y else 0)) := by
      apply congrArg (total m); funext y
      have hpt (x : W 8) : (if y = add m shift (L x) then f y else 0) =
          f y * (if L x = add m y shift then (1 : Int) else 0) := by
        have hiff : y = add m shift (L x) ↔ L x = add m y shift := by
          constructor
          · intro h
            have h2 := congrArg (add m shift) h
            rw [add_cancel_l, add_comm m shift y] at h2; exact h2.symm
          · intro h; rw [h, add_comm m shift (add m y shift), add_cancel_r]
        by_cases h : L x = add m y shift
        · rw [if_pos (hiff.2 h), if_pos h, Int.mul_one]
        · rw [if_neg (fun e => h (hiff.1 e)), if_neg h, Int.mul_zero]
      rw [funext hpt, total_scale, hfiber (add m y shift)]
      cases V (add m y shift) <;> simp [Int.mul_comm]
    rw [h2, total_scale, hsh_cos f]
  have hK_eq : K = 4 * multOfLen B.length := by
    have h1 := hpush (fun _ => (1 : Int))
    rw [total_const, cosetSum_const] at h1
    change (256 : Int) * 1 = K * (2 : Int) ^ B.length at h1
    have hpm := pow2_mul_multOfLen B.length (by omega)
    have hpow_pos : (0 : Int) < (2 : Int) ^ B.length := by
      have : ∀ k, (0 : Int) < (2 : Int) ^ k := fun k => by
        induction k with
        | zero => decide
        | succ k ih => rw [Int.pow_succ]; omega
      exact this B.length
    have hmul : K * (2 : Int) ^ B.length = (4 * multOfLen B.length) * (2 : Int) ^ B.length := by
      calc K * (2 : Int) ^ B.length = 256 := by omega
        _ = 4 * ((2 : Int) ^ B.length * multOfLen B.length) := by rw [hpm]; decide
        _ = (4 * multOfLen B.length) * (2 : Int) ^ B.length := by ac_rfl
    exact Int.eq_of_mul_eq_mul_right (by omega) hmul
  refine ⟨B, shs, sh, hmem, hsh_mem, hlen, ?_, ?_⟩
  · intro d ⟨x, hx⟩
    cases hany : B.any (fun b => dot m d b)
    · exfalso
      have hall : ∀ b ∈ B, dot m d b = false := by
        intro b hb
        cases hdb : dot m d b
        · rfl
        · have : B.any (fun b => dot m d b) = true := List.any_eq_true.2 ⟨b, hb, hdb⟩
          rw [hany] at this; exact absurd this (by decide)
      have hfalse := hspan d hall (L x) ((hV_spec (L x)).2 ⟨x, rfl⟩)
      rw [hx] at hfalse; exact absurd hfalse (by decide)
    · rfl
  · intro f; rw [hpush f, hK_eq]

/-! ## Section 3: Four-Cell Moment Table & Pure `decide +kernel` Refutation of All 4 Triples -/

private def mods3 (z : Int) : Int :=
  if z % 3 = 1 then 1 else if z % 3 = 2 then -1 else 0

private theorem mods3_eq_of_ternary (u z : Int) (hu : u = -1 ∨ u = 0 ∨ u = 1)
    (hmod : (u - z) % 3 = 0) : u = mods3 z := by
  unfold mods3
  have hm : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
  rcases hu with rfl | rfl | rfl <;> rcases hm with h | h | h <;> rw [h] <;> simp <;> omega

private abbrev CellRow := Int × Int × Int × Int × Int × Int × Int × Int

private def dot8 (w r : CellRow) : Int :=
  w.1 * r.1 + w.2.1 * r.2.1 + w.2.2.1 * r.2.2.1 + w.2.2.2.1 * r.2.2.2.1 +
  w.2.2.2.2.1 * r.2.2.2.2.1 + w.2.2.2.2.2.1 * r.2.2.2.2.2.1 +
  w.2.2.2.2.2.2.1 * r.2.2.2.2.2.2.1 + w.2.2.2.2.2.2.2 * r.2.2.2.2.2.2.2

private def cellValsOfJ (j1 j2 j3 off : Int) : Int × Int × Int × Int :=
  (mods3 (j1 + j2 + j3 + off),
   mods3 (-j1 + j2 - j3 + off),
   mods3 (j1 - j2 - j3 + off),
   mods3 (-j1 - j2 + j3 + off))

private def cellRowOfJ (j1 j2 j3 off : Int) : CellRow :=
  let (v0, v1, v2, v3) := cellValsOfJ j1 j2 j3 off
  let z0 := v0 + v1 + v2 + v3
  let z1 := v0 - v1 + v2 - v3
  let z2 := v0 + v1 - v2 - v3
  let z3 := v0 - v1 - v2 + v3
  (v0 * v0 + v1 * v1 + v2 * v2 + v3 * v3,
   z1 * z1, z2 * z2, z3 * z3,
   z1 * j1, z2 * j2, z3 * j3, z0)

private def isEmptyOfJ (j1 j2 j3 off : Int) : Int :=
  let (v0, v1, v2, v3) := cellValsOfJ j1 j2 j3 off
  if v0 = 0 && v1 = 0 && v2 = 0 && v3 = 0 then 1 else 0

private def max3 (a b c : Int) : Int :=
  let ab := if a ≥ b then a else b
  if ab ≥ c then ab else c

private def min3 (a b c : Int) : Int :=
  let ab := if a ≤ b then a else b
  if ab ≤ c then ab else c

private theorem le_max3 (a b c : Int) : a ≤ max3 a b c ∧ b ≤ max3 a b c ∧ c ≤ max3 a b c := by
  unfold max3; dsimp only; split <;> split <;> omega

private theorem min3_le (a b c : Int) : min3 a b c ≤ a ∧ min3 a b c ≤ b ∧ min3 a b c ≤ c := by
  unfold min3; dsimp only; split <;> split <;> omega

private def cutMaxFn {m : Nat} (jFn : W m → Int × Int × Int) (w : CellRow) (y : W m) : Int :=
  let (j1, j2, j3) := jFn y
  max3 (dot8 w (cellRowOfJ j1 j2 j3 0))
       (dot8 w (cellRowOfJ j1 j2 j3 1))
       (dot8 w (cellRowOfJ j1 j2 j3 2))

private def intMinFn {m : Nat} (jFn : W m → Int × Int × Int) (cEmp : Int) (w : CellRow) (y : W m) : Int :=
  let (j1, j2, j3) := jFn y
  min3 (cEmp * isEmptyOfJ j1 j2 j3 0 - dot8 w (cellRowOfJ j1 j2 j3 0))
       (cEmp * isEmptyOfJ j1 j2 j3 1 - dot8 w (cellRowOfJ j1 j2 j3 1))
       (cEmp * isEmptyOfJ j1 j2 j3 2 - dot8 w (cellRowOfJ j1 j2 j3 2))

private abbrev CutCert (m : Nat) := BTree Nat m × CellRow × Int × Nat
private abbrev IntCert (m : Nat) :=
  BTree Nat m × CellRow × Int × Int × BTree Nat m × CellRow × Int × Int

private def treeMatchesFn {m : Nat} (t : BTree Nat m) (f : W m → Int) (C : Int) : Bool :=
  (worlds m).all fun y => decide (f y + C = (t.get y : Int))

private def treesValid {m : Nat} (jFn : W m → Int × Int × Int) (target : CellRow)
    (cuts : List (CutCert m)) (intOpt : Option (IntCert m)) : Bool :=
  cuts.all (fun (t, w, C, reqNat) =>
    treeMatchesFn t (cutMaxFn jFn w) C && decide ((reqNat : Int) = dot8 w target + 64 * C)) &&
  match intOpt with
  | none => true
  | some (tLo, wLo, cLo, reqLo, tHi, wHi, cHi, reqHi) =>
    treeMatchesFn tLo (intMinFn jFn 288 wLo) cLo &&
    decide (reqLo = dot8 wLo target) &&
    treeMatchesFn tHi (intMinFn jFn (-144) wHi) cHi &&
    decide (reqHi = dot8 wHi target)

private def checkLinearSpaceFast {m : Nat} (diffs : List (W m))
    (cuts : List (CutCert m)) (intOpt : Option (IntCert m))
    (B : List (W m)) (shs : List (W m)) : Bool :=
  if !(diffs.all fun d => B.any fun b => dot m d b) then true
  else
    let multN := multOfLenNat B.length
    shs.all fun sh =>
      if cuts.any fun (t, _, _, reqNat) => multN * cosetSumNat t B sh < reqNat then true
      else match intOpt with
      | none => false
      | some (tLo, _, cLo, reqLo, tHi, _, cHi, reqHi) =>
        let multI : Int := (multN : Int)
        let bLo := reqLo + multI * (cosetSumNat tLo B sh : Int) - 64 * cLo
        let bHi := reqHi + multI * (cosetSumNat tHi B sh : Int) - 64 * cHi
        288 * ((-bHi).ediv 144) < bLo

private def checkAllSpacesFast {m : Nat} (diffs : List (W m))
    (cuts : List (CutCert m)) (intOpt : Option (IntCert m)) : Bool :=
  rrefAll m fun B shs => checkLinearSpaceFast diffs cuts intOpt B shs

/-! ### Exact Specifications & Precomputed Shifted-`Nat` Lookup Trees for All 4 Triples -/

-- Triple 1: (2, 2, 2), m = 4
private def j222 (y : W 4) : Int × Int × Int :=
  let (b0, (b1, (b2, (b3, _)))) := y
  (sign b0 + sign b1, sign b2 + 1, sign b3 + 1)

private def diffs222 : List (W 4) := [
  (true,  (true,  (false, (false, ())))),
  (false, (false, (true,  (false, ())))),
  (false, (false, (false, (true,  ()))))
]

private def target222 : CellRow := (118, 140, 140, 140, 8, 8, 8, 0)

-- Triple 2: (1, 3, 3), m = 5
private def j133 (y : W 5) : Int × Int × Int :=
  let (b0, (b1, (b2, (b3, (b4, _))))) := y
  (sign b0, sign b1 + sign b2 + 1, sign b3 + sign b4 + 1)

private def diffs133 : List (W 5) := [
  (false, (true,  (false, (false, (false, ()))))),
  (false, (false, (true,  (false, (false, ()))))),
  (false, (true,  (true,  (false, (false, ()))))),
  (false, (false, (false, (true,  (false, ()))))),
  (false, (false, (false, (false, (true,  ()))))),
  (false, (false, (false, (true,  (true,  ())))))
]

private def target133 : CellRow := (118, 142, 138, 138, 4, 12, 12, 0)

-- Triple 3: (0, 4, 4), m = 6
private def j044 (y : W 6) : Int × Int × Int :=
  let (b0, (b1, (b2, (b3, (b4, (b5, _)))))) := y
  (0, sign b0 + sign b1 + sign b2 + 1, sign b3 + sign b4 + sign b5 + 1)

private def diffs044 : List (W 6) := [
  (true,  (false, (false, (false, (false, (false, ())))))),
  (false, (true,  (false, (false, (false, (false, ())))))),
  (false, (false, (true,  (false, (false, (false, ())))))),
  (true,  (true,  (false, (false, (false, (false, ())))))),
  (true,  (false, (true,  (false, (false, (false, ())))))),
  (false, (true,  (true,  (false, (false, (false, ())))))),
  (false, (false, (false, (true,  (false, (false, ())))))),
  (false, (false, (false, (false, (true,  (false, ())))))),
  (false, (false, (false, (false, (false, (true,  ())))))),
  (false, (false, (false, (true,  (true,  (false, ())))))),
  (false, (false, (false, (true,  (false, (true,  ())))))),
  (false, (false, (false, (false, (true,  (true,  ()))))))
]

private def target044 : CellRow := (118, 144, 136, 136, 0, 16, 16, 0)

-- Triple 4: (2, 2, 4), m = 6
private def j224 (y : W 6) : Int × Int × Int :=
  let (b0, (b1, (b2, (b3, (b4, (b5, _)))))) := y
  (sign b0 + sign b1, sign b2 + 1, sign b3 + sign b4 + sign b5 + 1)

private def diffs224 : List (W 6) := [
  (true,  (true,  (false, (false, (false, (false, ())))))),
  (false, (false, (true,  (false, (false, (false, ())))))),
  (false, (false, (false, (true,  (false, (false, ())))))),
  (false, (false, (false, (false, (true,  (false, ())))))),
  (false, (false, (false, (false, (false, (true,  ())))))),
  (false, (false, (false, (true,  (true,  (false, ())))))),
  (false, (false, (false, (true,  (false, (true,  ())))))),
  (false, (false, (false, (false, (true,  (true,  ()))))))
]

private def target224 : CellRow := (118, 140, 140, 136, 8, 8, 16, 0)

private def cutTree_222_0 : BTree Nat 4 := (.node (.node (.node (.node (.leaf 26) (.leaf 4)) (.node (.leaf 4) (.leaf 0))) (.node (.node (.leaf 4) (.leaf 0)) (.node (.leaf 0) (.leaf 32)))) (.node (.node (.node (.leaf 4) (.leaf 0)) (.node (.leaf 0) (.leaf 32))) (.node (.node (.leaf 26) (.leaf 4)) (.node (.leaf 4) (.leaf 0)))))
private def cutTree_222_1 : BTree Nat 4 := (.node (.node (.node (.node (.leaf 4) (.leaf 12)) (.node (.leaf 4) (.leaf 24))) (.node (.node (.leaf 10) (.leaf 0)) (.node (.leaf 16) (.leaf 0)))) (.node (.node (.node (.leaf 10) (.leaf 0)) (.node (.leaf 16) (.leaf 0))) (.node (.node (.leaf 4) (.leaf 12)) (.node (.leaf 4) (.leaf 24)))))
private def cutTree_222_2 : BTree Nat 4 := (.node (.node (.node (.node (.leaf 93) (.leaf 117)) (.node (.leaf 117) (.leaf 0))) (.node (.node (.leaf 44) (.leaf 176)) (.node (.leaf 176) (.leaf 56)))) (.node (.node (.node (.leaf 44) (.leaf 176)) (.node (.leaf 176) (.leaf 56))) (.node (.node (.leaf 93) (.leaf 117)) (.node (.leaf 117) (.leaf 0)))))
private def cutTree_222_3 : BTree Nat 4 := (.node (.node (.node (.node (.leaf 4) (.leaf 4)) (.node (.leaf 12) (.leaf 24))) (.node (.node (.leaf 10) (.leaf 16)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 10) (.leaf 16)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 4) (.leaf 4)) (.node (.leaf 12) (.leaf 24)))))
private def cutCerts_222 : List (CutCert 4) :=
  [(cutTree_222_0, (-18, 2, 2, 2, -1, -1, -1, 0), 32, 740),
   (cutTree_222_1, (0, 1, 0, 1, -1, 0, 0, 0), 0, 272),
   (cutTree_222_2, (-6, -5, 6, 6, -6, -6, -6, 0), 56, 3712),
   (cutTree_222_3, (0, 1, 1, 0, -1, 0, 0, 0), 0, 272)]

private def cutTree_133_0 : BTree Nat 5 := (.node (.node (.node (.node (.node (.leaf 0) (.leaf 12)) (.node (.leaf 12) (.leaf 12))) (.node (.node (.leaf 12) (.leaf 6)) (.node (.leaf 6) (.leaf 6)))) (.node (.node (.node (.leaf 12) (.leaf 6)) (.node (.leaf 6) (.leaf 6))) (.node (.node (.leaf 12) (.leaf 6)) (.node (.leaf 6) (.leaf 6))))) (.node (.node (.node (.node (.leaf 0) (.leaf 12)) (.node (.leaf 12) (.leaf 12))) (.node (.node (.leaf 12) (.leaf 6)) (.node (.leaf 6) (.leaf 6)))) (.node (.node (.node (.leaf 12) (.leaf 6)) (.node (.leaf 6) (.leaf 6))) (.node (.node (.leaf 12) (.leaf 6)) (.node (.leaf 6) (.leaf 6))))))
private def cutTree_133_1 : BTree Nat 5 := (.node (.node (.node (.node (.node (.leaf 20) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2)))) (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2))))) (.node (.node (.node (.node (.leaf 20) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2)))) (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2))))))
private def cutCerts_133 : List (CutCert 5) :=
  [(cutTree_133_0, (-9, 2, 3, 3, -1, 0, 0, 0), 8, 558),
   (cutTree_133_1, (0, 1, 0, 0, 1, 0, 0, 0), 0, 146)]

private def cutTree_044_0 : BTree Nat 6 := (.node (.node (.node (.node (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 0))) (.node (.node (.leaf 12) (.leaf 0)) (.node (.leaf 0) (.leaf 12)))) (.node (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 0))) (.node (.node (.leaf 12) (.leaf 0)) (.node (.leaf 0) (.leaf 12))))) (.node (.node (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 0))) (.node (.node (.leaf 12) (.leaf 0)) (.node (.leaf 0) (.leaf 12)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 24))) (.node (.node (.leaf 0) (.leaf 24)) (.node (.leaf 24) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 0))) (.node (.node (.leaf 12) (.leaf 0)) (.node (.leaf 0) (.leaf 12)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 24))) (.node (.node (.leaf 0) (.leaf 24)) (.node (.leaf 24) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 24))) (.node (.node (.leaf 0) (.leaf 24)) (.node (.leaf 24) (.leaf 0)))) (.node (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 0))) (.node (.node (.leaf 12) (.leaf 0)) (.node (.leaf 0) (.leaf 12)))))))
private def cutTree_044_1 : BTree Nat 6 := (.node (.node (.node (.node (.node (.node (.leaf 46) (.leaf 46)) (.node (.leaf 46) (.leaf 0))) (.node (.node (.leaf 46) (.leaf 0)) (.node (.leaf 0) (.leaf 46)))) (.node (.node (.node (.leaf 46) (.leaf 46)) (.node (.leaf 46) (.leaf 0))) (.node (.node (.leaf 46) (.leaf 0)) (.node (.leaf 0) (.leaf 46))))) (.node (.node (.node (.node (.leaf 46) (.leaf 46)) (.node (.leaf 46) (.leaf 0))) (.node (.node (.leaf 46) (.leaf 0)) (.node (.leaf 0) (.leaf 46)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 8))) (.node (.node (.leaf 0) (.leaf 8)) (.node (.leaf 8) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 46) (.leaf 46)) (.node (.leaf 46) (.leaf 0))) (.node (.node (.leaf 46) (.leaf 0)) (.node (.leaf 0) (.leaf 46)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 8))) (.node (.node (.leaf 0) (.leaf 8)) (.node (.leaf 8) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 8))) (.node (.node (.leaf 0) (.leaf 8)) (.node (.leaf 8) (.leaf 0)))) (.node (.node (.node (.leaf 46) (.leaf 46)) (.node (.leaf 46) (.leaf 0))) (.node (.node (.leaf 46) (.leaf 0)) (.node (.leaf 0) (.leaf 46)))))))
private def cutTree_044_2 : BTree Nat 6 := (.node (.node (.node (.node (.node (.node (.leaf 24) (.leaf 60)) (.node (.leaf 60) (.leaf 36))) (.node (.node (.leaf 60) (.leaf 36)) (.node (.leaf 36) (.leaf 60)))) (.node (.node (.node (.leaf 42) (.leaf 24)) (.node (.leaf 24) (.leaf 72))) (.node (.node (.leaf 24) (.leaf 72)) (.node (.leaf 72) (.leaf 24))))) (.node (.node (.node (.node (.leaf 42) (.leaf 24)) (.node (.leaf 24) (.leaf 72))) (.node (.node (.leaf 24) (.leaf 72)) (.node (.leaf 72) (.leaf 24)))) (.node (.node (.node (.leaf 96) (.leaf 24)) (.node (.leaf 24) (.leaf 0))) (.node (.node (.leaf 24) (.leaf 0)) (.node (.leaf 0) (.leaf 24)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 24)) (.node (.leaf 24) (.leaf 72))) (.node (.node (.leaf 24) (.leaf 72)) (.node (.leaf 72) (.leaf 24)))) (.node (.node (.node (.leaf 96) (.leaf 24)) (.node (.leaf 24) (.leaf 0))) (.node (.node (.leaf 24) (.leaf 0)) (.node (.leaf 0) (.leaf 24))))) (.node (.node (.node (.node (.leaf 96) (.leaf 24)) (.node (.leaf 24) (.leaf 0))) (.node (.node (.leaf 24) (.leaf 0)) (.node (.leaf 0) (.leaf 24)))) (.node (.node (.node (.leaf 42) (.leaf 24)) (.node (.leaf 24) (.leaf 72))) (.node (.node (.leaf 24) (.leaf 72)) (.node (.leaf 72) (.leaf 24)))))))
private def cutCerts_044 : List (CutCert 6) :=
  [(cutTree_044_0, (-18, 4, 3, 3, -18, 0, 0, 0), 24, 804),
   (cutTree_044_1, (-6, 6, 1, 1, -6, 0, 0, 0), 8, 940),
   (cutTree_044_2, (0, 2, 3, 3, -3, -3, 3, 0), 0, 1104)]

private def intTree_044_lo : BTree Nat 6 := (.node (.node (.node (.node (.node (.node (.leaf 264) (.leaf 264)) (.node (.leaf 264) (.leaf 456))) (.node (.node (.leaf 264) (.leaf 456)) (.node (.leaf 456) (.leaf 264)))) (.node (.node (.node (.leaf 192) (.leaf 300)) (.node (.leaf 300) (.leaf 384))) (.node (.node (.leaf 300) (.leaf 384)) (.node (.leaf 384) (.leaf 300))))) (.node (.node (.node (.node (.leaf 192) (.leaf 300)) (.node (.leaf 300) (.leaf 384))) (.node (.node (.leaf 300) (.leaf 384)) (.node (.leaf 384) (.leaf 300)))) (.node (.node (.node (.leaf 216) (.leaf 0)) (.node (.leaf 0) (.leaf 552))) (.node (.node (.leaf 0) (.leaf 552)) (.node (.leaf 552) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 192) (.leaf 300)) (.node (.leaf 300) (.leaf 384))) (.node (.node (.leaf 300) (.leaf 384)) (.node (.leaf 384) (.leaf 300)))) (.node (.node (.node (.leaf 216) (.leaf 0)) (.node (.leaf 0) (.leaf 552))) (.node (.node (.leaf 0) (.leaf 552)) (.node (.leaf 552) (.leaf 0))))) (.node (.node (.node (.node (.leaf 216) (.leaf 0)) (.node (.leaf 0) (.leaf 552))) (.node (.node (.leaf 0) (.leaf 552)) (.node (.leaf 552) (.leaf 0)))) (.node (.node (.node (.leaf 192) (.leaf 300)) (.node (.leaf 300) (.leaf 384))) (.node (.node (.leaf 300) (.leaf 384)) (.node (.leaf 384) (.leaf 300)))))))
private def intTree_044_hi : BTree Nat 6 := (.node (.node (.node (.node (.node (.node (.leaf 144) (.leaf 108)) (.node (.leaf 108) (.leaf 72))) (.node (.node (.leaf 108) (.leaf 72)) (.node (.leaf 72) (.leaf 108)))) (.node (.node (.node (.leaf 126) (.leaf 144)) (.node (.leaf 144) (.leaf 0))) (.node (.node (.leaf 144) (.leaf 0)) (.node (.leaf 0) (.leaf 144))))) (.node (.node (.node (.node (.leaf 126) (.leaf 144)) (.node (.leaf 144) (.leaf 0))) (.node (.node (.leaf 144) (.leaf 0)) (.node (.leaf 0) (.leaf 144)))) (.node (.node (.node (.leaf 168) (.leaf 132)) (.node (.leaf 132) (.leaf 24))) (.node (.node (.leaf 132) (.leaf 24)) (.node (.leaf 24) (.leaf 132)))))) (.node (.node (.node (.node (.node (.leaf 126) (.leaf 144)) (.node (.leaf 144) (.leaf 0))) (.node (.node (.leaf 144) (.leaf 0)) (.node (.leaf 0) (.leaf 144)))) (.node (.node (.node (.leaf 168) (.leaf 132)) (.node (.leaf 132) (.leaf 24))) (.node (.node (.leaf 132) (.leaf 24)) (.node (.leaf 24) (.leaf 132))))) (.node (.node (.node (.node (.leaf 168) (.leaf 132)) (.node (.leaf 132) (.leaf 24))) (.node (.node (.leaf 132) (.leaf 24)) (.node (.leaf 24) (.leaf 132)))) (.node (.node (.node (.leaf 126) (.leaf 144)) (.node (.leaf 144) (.leaf 0))) (.node (.node (.leaf 144) (.leaf 0)) (.node (.leaf 0) (.leaf 144)))))))
private def intCert_044 : IntCert 6 :=
  (intTree_044_lo, (-72, 16, 0, 30, 0, 6, -9, 0), 264, -2160,
   intTree_044_hi, (36, -8, 0, -12, 0, -3, 3, 0), 168, 1464)

private def cutTree_224_0 : BTree Nat 6 := (.node (.node (.node (.node (.node (.node (.leaf 16) (.leaf 22)) (.node (.leaf 22) (.leaf 36))) (.node (.node (.leaf 22) (.leaf 36)) (.node (.leaf 36) (.leaf 22)))) (.node (.node (.node (.leaf 32) (.leaf 20)) (.node (.leaf 20) (.leaf 16))) (.node (.node (.leaf 20) (.leaf 16)) (.node (.leaf 16) (.leaf 20))))) (.node (.node (.node (.node (.leaf 32) (.leaf 20)) (.node (.leaf 20) (.leaf 16))) (.node (.node (.leaf 20) (.leaf 16)) (.node (.leaf 16) (.leaf 20)))) (.node (.node (.node (.leaf 12) (.leaf 0)) (.node (.leaf 0) (.leaf 32))) (.node (.node (.leaf 0) (.leaf 32)) (.node (.leaf 32) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 32) (.leaf 20)) (.node (.leaf 20) (.leaf 16))) (.node (.node (.leaf 20) (.leaf 16)) (.node (.leaf 16) (.leaf 20)))) (.node (.node (.node (.leaf 12) (.leaf 0)) (.node (.leaf 0) (.leaf 32))) (.node (.node (.leaf 0) (.leaf 32)) (.node (.leaf 32) (.leaf 0))))) (.node (.node (.node (.node (.leaf 16) (.leaf 22)) (.node (.leaf 22) (.leaf 36))) (.node (.node (.leaf 22) (.leaf 36)) (.node (.leaf 36) (.leaf 22)))) (.node (.node (.node (.leaf 32) (.leaf 20)) (.node (.leaf 20) (.leaf 16))) (.node (.node (.leaf 20) (.leaf 16)) (.node (.leaf 16) (.leaf 20)))))))
private def cutTree_224_1 : BTree Nat 6 := (.node (.node (.node (.node (.node (.node (.leaf 36) (.leaf 36)) (.node (.leaf 36) (.leaf 0))) (.node (.node (.leaf 36) (.leaf 0)) (.node (.leaf 0) (.leaf 36)))) (.node (.node (.node (.leaf 4) (.leaf 4)) (.node (.leaf 4) (.leaf 4))) (.node (.node (.leaf 4) (.leaf 4)) (.node (.leaf 4) (.leaf 4))))) (.node (.node (.node (.node (.leaf 4) (.leaf 4)) (.node (.leaf 4) (.leaf 4))) (.node (.node (.leaf 4) (.leaf 4)) (.node (.leaf 4) (.leaf 4)))) (.node (.node (.node (.leaf 8) (.leaf 8)) (.node (.leaf 8) (.leaf 44))) (.node (.node (.leaf 8) (.leaf 44)) (.node (.leaf 44) (.leaf 8)))))) (.node (.node (.node (.node (.node (.leaf 4) (.leaf 4)) (.node (.leaf 4) (.leaf 4))) (.node (.node (.leaf 4) (.leaf 4)) (.node (.leaf 4) (.leaf 4)))) (.node (.node (.node (.leaf 8) (.leaf 8)) (.node (.leaf 8) (.leaf 44))) (.node (.node (.leaf 8) (.leaf 44)) (.node (.leaf 44) (.leaf 8))))) (.node (.node (.node (.node (.leaf 36) (.leaf 36)) (.node (.leaf 36) (.leaf 0))) (.node (.node (.leaf 36) (.leaf 0)) (.node (.leaf 0) (.leaf 36)))) (.node (.node (.node (.leaf 4) (.leaf 4)) (.node (.leaf 4) (.leaf 4))) (.node (.node (.leaf 4) (.leaf 4)) (.node (.leaf 4) (.leaf 4)))))))
private def cutTree_224_2 : BTree Nat 6 := (.node (.node (.node (.node (.node (.node (.leaf 20) (.leaf 8)) (.node (.leaf 8) (.leaf 22))) (.node (.node (.leaf 8) (.leaf 22)) (.node (.leaf 22) (.leaf 8)))) (.node (.node (.node (.leaf 16) (.leaf 22)) (.node (.leaf 22) (.leaf 0))) (.node (.node (.leaf 22) (.leaf 0)) (.node (.leaf 0) (.leaf 22))))) (.node (.node (.node (.node (.leaf 20) (.leaf 8)) (.node (.leaf 8) (.leaf 40))) (.node (.node (.leaf 8) (.leaf 40)) (.node (.leaf 40) (.leaf 8)))) (.node (.node (.node (.leaf 16) (.leaf 40)) (.node (.leaf 40) (.leaf 0))) (.node (.node (.leaf 40) (.leaf 0)) (.node (.leaf 0) (.leaf 40)))))) (.node (.node (.node (.node (.node (.leaf 20) (.leaf 8)) (.node (.leaf 8) (.leaf 40))) (.node (.node (.leaf 8) (.leaf 40)) (.node (.leaf 40) (.leaf 8)))) (.node (.node (.node (.leaf 16) (.leaf 40)) (.node (.leaf 40) (.leaf 0))) (.node (.node (.leaf 40) (.leaf 0)) (.node (.leaf 0) (.leaf 40))))) (.node (.node (.node (.node (.leaf 20) (.leaf 8)) (.node (.leaf 8) (.leaf 22))) (.node (.node (.leaf 8) (.leaf 22)) (.node (.leaf 22) (.leaf 8)))) (.node (.node (.node (.leaf 16) (.leaf 22)) (.node (.leaf 22) (.leaf 0))) (.node (.node (.leaf 22) (.leaf 0)) (.node (.leaf 0) (.leaf 22)))))))
private def cutTree_224_3 : BTree Nat 6 := (.node (.node (.node (.node (.node (.node (.leaf 20) (.leaf 8)) (.node (.leaf 8) (.leaf 22))) (.node (.node (.leaf 8) (.leaf 22)) (.node (.leaf 22) (.leaf 8)))) (.node (.node (.node (.leaf 20) (.leaf 8)) (.node (.leaf 8) (.leaf 40))) (.node (.node (.leaf 8) (.leaf 40)) (.node (.leaf 40) (.leaf 8))))) (.node (.node (.node (.node (.leaf 16) (.leaf 22)) (.node (.leaf 22) (.leaf 0))) (.node (.node (.leaf 22) (.leaf 0)) (.node (.leaf 0) (.leaf 22)))) (.node (.node (.node (.leaf 16) (.leaf 40)) (.node (.leaf 40) (.leaf 0))) (.node (.node (.leaf 40) (.leaf 0)) (.node (.leaf 0) (.leaf 40)))))) (.node (.node (.node (.node (.node (.leaf 16) (.leaf 22)) (.node (.leaf 22) (.leaf 0))) (.node (.node (.leaf 22) (.leaf 0)) (.node (.leaf 0) (.leaf 22)))) (.node (.node (.node (.leaf 16) (.leaf 40)) (.node (.leaf 40) (.leaf 0))) (.node (.node (.leaf 40) (.leaf 0)) (.node (.leaf 0) (.leaf 40))))) (.node (.node (.node (.node (.leaf 20) (.leaf 8)) (.node (.leaf 8) (.leaf 22))) (.node (.node (.leaf 8) (.leaf 22)) (.node (.leaf 22) (.leaf 8)))) (.node (.node (.node (.leaf 20) (.leaf 8)) (.node (.leaf 8) (.leaf 40))) (.node (.node (.leaf 8) (.leaf 40)) (.node (.leaf 40) (.leaf 8)))))))
private def cutTree_224_4 : BTree Nat 6 := (.node (.node (.node (.node (.node (.node (.leaf 10) (.leaf 4)) (.node (.leaf 4) (.leaf 20))) (.node (.node (.leaf 4) (.leaf 20)) (.node (.leaf 20) (.leaf 4)))) (.node (.node (.node (.leaf 8) (.leaf 20)) (.node (.leaf 20) (.leaf 0))) (.node (.node (.leaf 20) (.leaf 0)) (.node (.leaf 0) (.leaf 20))))) (.node (.node (.node (.node (.leaf 8) (.leaf 20)) (.node (.leaf 20) (.leaf 0))) (.node (.node (.leaf 20) (.leaf 0)) (.node (.leaf 0) (.leaf 20)))) (.node (.node (.node (.leaf 24) (.leaf 0)) (.node (.leaf 0) (.leaf 16))) (.node (.node (.leaf 0) (.leaf 16)) (.node (.leaf 16) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 8) (.leaf 20)) (.node (.leaf 20) (.leaf 0))) (.node (.node (.leaf 20) (.leaf 0)) (.node (.leaf 0) (.leaf 20)))) (.node (.node (.node (.leaf 24) (.leaf 0)) (.node (.leaf 0) (.leaf 16))) (.node (.node (.leaf 0) (.leaf 16)) (.node (.leaf 16) (.leaf 0))))) (.node (.node (.node (.node (.leaf 10) (.leaf 4)) (.node (.leaf 4) (.leaf 20))) (.node (.node (.leaf 4) (.leaf 20)) (.node (.leaf 20) (.leaf 4)))) (.node (.node (.node (.leaf 8) (.leaf 20)) (.node (.leaf 20) (.leaf 0))) (.node (.node (.leaf 20) (.leaf 0)) (.node (.leaf 0) (.leaf 20)))))))
private def cutTree_224_5 : BTree Nat 6 := (.node (.node (.node (.node (.node (.node (.leaf 42) (.leaf 90)) (.node (.leaf 90) (.leaf 16))) (.node (.node (.leaf 90) (.leaf 16)) (.node (.leaf 16) (.leaf 90)))) (.node (.node (.node (.leaf 96) (.leaf 0)) (.node (.leaf 0) (.leaf 52))) (.node (.node (.leaf 0) (.leaf 52)) (.node (.leaf 52) (.leaf 0))))) (.node (.node (.node (.node (.leaf 96) (.leaf 0)) (.node (.leaf 0) (.leaf 52))) (.node (.node (.leaf 0) (.leaf 52)) (.node (.leaf 52) (.leaf 0)))) (.node (.node (.node (.leaf 132) (.leaf 54)) (.node (.leaf 54) (.leaf 106))) (.node (.node (.leaf 54) (.leaf 106)) (.node (.leaf 106) (.leaf 54)))))) (.node (.node (.node (.node (.node (.leaf 96) (.leaf 0)) (.node (.leaf 0) (.leaf 52))) (.node (.node (.leaf 0) (.leaf 52)) (.node (.leaf 52) (.leaf 0)))) (.node (.node (.node (.leaf 132) (.leaf 54)) (.node (.leaf 54) (.leaf 106))) (.node (.node (.leaf 54) (.leaf 106)) (.node (.leaf 106) (.leaf 54))))) (.node (.node (.node (.node (.leaf 42) (.leaf 90)) (.node (.leaf 90) (.leaf 16))) (.node (.node (.leaf 90) (.leaf 16)) (.node (.leaf 16) (.leaf 90)))) (.node (.node (.node (.leaf 96) (.leaf 0)) (.node (.leaf 0) (.leaf 52))) (.node (.node (.leaf 0) (.leaf 52)) (.node (.leaf 52) (.leaf 0)))))))
private def cutTree_224_6 : BTree Nat 6 := (.node (.node (.node (.node (.node (.node (.leaf 36) (.leaf 30)) (.node (.leaf 30) (.leaf 16))) (.node (.node (.leaf 30) (.leaf 16)) (.node (.leaf 16) (.leaf 30)))) (.node (.node (.node (.leaf 54) (.leaf 48)) (.node (.leaf 48) (.leaf 88))) (.node (.node (.leaf 48) (.leaf 88)) (.node (.leaf 88) (.leaf 48))))) (.node (.node (.node (.node (.leaf 54) (.leaf 48)) (.node (.leaf 48) (.leaf 88))) (.node (.node (.leaf 48) (.leaf 88)) (.node (.leaf 88) (.leaf 48)))) (.node (.node (.node (.leaf 0) (.leaf 12)) (.node (.leaf 12) (.leaf 16))) (.node (.node (.leaf 12) (.leaf 16)) (.node (.leaf 16) (.leaf 12)))))) (.node (.node (.node (.node (.node (.leaf 54) (.leaf 48)) (.node (.leaf 48) (.leaf 88))) (.node (.node (.leaf 48) (.leaf 88)) (.node (.leaf 88) (.leaf 48)))) (.node (.node (.node (.leaf 0) (.leaf 12)) (.node (.leaf 12) (.leaf 16))) (.node (.node (.leaf 12) (.leaf 16)) (.node (.leaf 16) (.leaf 12))))) (.node (.node (.node (.node (.leaf 36) (.leaf 30)) (.node (.leaf 30) (.leaf 16))) (.node (.node (.leaf 30) (.leaf 16)) (.node (.leaf 16) (.leaf 30)))) (.node (.node (.node (.leaf 54) (.leaf 48)) (.node (.leaf 48) (.leaf 88))) (.node (.node (.leaf 48) (.leaf 88)) (.node (.leaf 88) (.leaf 48)))))))
private def cutCerts_224 : List (CutCert 6) :=
  [(cutTree_224_0, (-18, 4, 4, 2, 1, 1, -1, 0), 32, 1316),
   (cutTree_224_1, (-18, 1, 1, 0, -2, -2, 0, 0), 44, 940),
   (cutTree_224_2, (0, 0, 2, 2, 0, -1, -1, 0), 0, 528),
   (cutTree_224_3, (0, 2, 0, 2, -1, 0, -1, 0), 0, 528),
   (cutTree_224_4, (-18, 4, 4, 4, 1, 1, 1, 0), 16, 596),
   (cutTree_224_5, (-9, -9, -9, -5, 0, 0, -8, 0), 106, 2394),
   (cutTree_224_6, (0, 3, 3, -2, -3, -3, 1, 0), 16, 1560)]

/-! ### Kernel-Verified Certificate Theorems (ZERO `native_decide`!) -/

private theorem trees_222_ok : treesValid j222 target222 cutCerts_222 none = true := by decide +kernel
private theorem trees_133_ok : treesValid j133 target133 cutCerts_133 none = true := by decide +kernel
private theorem trees_044_ok : treesValid j044 target044 cutCerts_044 (some intCert_044) = true := by decide +kernel
private theorem trees_224_ok : treesValid j224 target224 cutCerts_224 none = true := by decide +kernel

private theorem check_222_ok : checkAllSpacesFast diffs222 cutCerts_222 none = true := by decide +kernel
private theorem check_133_ok : checkAllSpacesFast diffs133 cutCerts_133 none = true := by decide +kernel
private theorem check_044_ok : checkAllSpacesFast diffs044 cutCerts_044 (some intCert_044) = true := by decide +kernel
private theorem check_224_ok : checkAllSpacesFast diffs224 cutCerts_224 none = true := by decide +kernel

/-- Soundness of `treesValid` + `checkAllSpacesFast`: no affine realization with matching
    moment totals and divisible `emp` total can exist. -/
private theorem refute_from_check {m : Nat} (hm : m ≤ 6)
    (jFn : W m → Int × Int × Int) (diffs : List (W m))
    (cutCerts : List (CutCert m)) (intOpt : Option (IntCert m))
    (target : CellRow)
    (htrees : treesValid jFn target cutCerts intOpt = true)
    (hcheck : checkAllSpacesFast diffs cutCerts intOpt = true)
    (L : W 8 → W m) (hL : ∀ x y, L (add 8 x y) = add m (L x) (L y))
    (shift : W m)
    (hdiffs : ∀ d ∈ diffs, ∃ x : W 8, dot m d (L x) = true)
    (M : W 8 → CellRow) (emp : W 8 → Int)
    (hM_tot : ∀ w : CellRow, total 8 (fun x => dot8 w (M x)) = 4 * dot8 w target)
    (hemp_div4 : ∃ N : Int, total 8 emp = 4 * N)
    (hpt : ∀ x : W 8, ∃ off : Int, (off = 0 ∨ off = 1 ∨ off = 2) ∧
      let (j1, j2, j3) := jFn (add m shift (L x))
      M x = cellRowOfJ j1 j2 j3 off ∧ emp x = isEmptyOfJ j1 j2 j3 off) : False := by
  obtain ⟨B, shs, sh, hB, hsh_mem, hBlen, hspan, hsum⟩ :=
    affine_image_rref hm L hL shift (fun B shs => checkLinearSpaceFast diffs cutCerts intOpt B shs) hcheck
  have hpm := pow2_mul_multOfLen B.length (by omega)
  dsimp only [checkLinearSpaceFast] at hB
  have hdiff_ok : diffs.all (fun d => B.any (fun b => dot m d b)) = true := by
    rw [List.all_eq_true]
    intro d hd
    exact hspan d (hdiffs d hd)
  rw [hdiff_ok] at hB
  simp only [Bool.not_true, Bool.false_eq_true, if_false, List.all_eq_true] at hB
  have hsh := hB sh hsh_mem
  unfold treesValid at htrees
  simp only [Bool.and_eq_true, List.all_eq_true] at htrees
  obtain ⟨hcuts_valid, hint_valid⟩ := htrees
  cases hcut : cutCerts.any (fun (t, _, _, reqNat) => multOfLenNat B.length * cosetSumNat t B sh < reqNat) with
  | true =>
    rw [List.any_eq_true] at hcut
    obtain ⟨⟨t, w, C, reqNat⟩, hmem_c, hlt⟩ := hcut
    rw [decide_eq_true_eq] at hlt
    have hv := hcuts_valid (t, w, C, reqNat) hmem_c
    simp only [Bool.and_eq_true, treeMatchesFn, List.all_eq_true, decide_eq_true_eq] at hv
    obtain ⟨ht_match, hreq_eq⟩ := hv
    have hcs_eq := cosetSumNat_eq t (cutMaxFn jFn w) C (fun y => ht_match y (all_worlds m y)) B sh
    have hpt_le (x : W 8) : dot8 w (M x) ≤ cutMaxFn jFn w (add m shift (L x)) := by
      obtain ⟨off, hoff, hMx, _⟩ := hpt x
      rw [hMx]; unfold cutMaxFn
      have ⟨h0, h1, h2⟩ := le_max3
        (dot8 w (cellRowOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 0))
        (dot8 w (cellRowOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 1))
        (dot8 w (cellRowOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 2))
      rcases hoff with rfl | rfl | rfl <;> assumption
    have htot_le := total_mono 8 _ _ hpt_le
    rw [hM_tot w, hsum (cutMaxFn jFn w), Int.mul_assoc] at htot_le
    have hlt_int : multOfLen B.length * (cosetSumNat t B sh : Int) < (reqNat : Int) := by
      unfold multOfLen
      have h := Int.ofNat_lt.2 hlt
      simpa only [Int.ofNat_mul] using h
    rw [hcs_eq, Int.mul_add, hreq_eq] at hlt_int
    have h64C : multOfLen B.length * ((2 : Int) ^ B.length * C) = 64 * C := by
      calc multOfLen B.length * ((2 : Int) ^ B.length * C)
          = ((2 : Int) ^ B.length * multOfLen B.length) * C := by ac_rfl
        _ = 64 * C := by rw [hpm]
    rw [h64C] at hlt_int
    omega
  | false =>
    simp only [hcut, Bool.false_eq_true, if_false] at hsh
    cases intOpt with
    | none => simp only at hsh; exact absurd hsh (by decide)
    | some cert =>
      rcases cert with ⟨tLo, wLo, cLo, reqLo, tHi, wHi, cHi, reqHi⟩
      simp only [Bool.and_eq_true, treeMatchesFn, List.all_eq_true, decide_eq_true_eq] at hint_valid
      obtain ⟨⟨⟨htLo_m, hreqLo⟩, htHi_m⟩, hreqHi⟩ := hint_valid
      rw [decide_eq_true_eq] at hsh
      have hcsLo := cosetSumNat_eq tLo (intMinFn jFn 288 wLo) cLo (fun y => htLo_m y (all_worlds m y)) B sh
      have hcsHi := cosetSumNat_eq tHi (intMinFn jFn (-144) wHi) cHi (fun y => htHi_m y (all_worlds m y)) B sh
      obtain ⟨N, hN⟩ := hemp_div4
      have hlo_pt (x : W 8) :
          intMinFn jFn 288 wLo (add m shift (L x)) ≤ 288 * emp x - dot8 wLo (M x) := by
        obtain ⟨off, hoff, hMx, hex⟩ := hpt x
        rw [hMx, hex]; unfold intMinFn
        have ⟨h0, h1, h2⟩ := min3_le
          (288 * isEmptyOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 0 -
            dot8 wLo (cellRowOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 0))
          (288 * isEmptyOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 1 -
            dot8 wLo (cellRowOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 1))
          (288 * isEmptyOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 2 -
            dot8 wLo (cellRowOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 2))
        rcases hoff with rfl | rfl | rfl <;> assumption
      have hhi_pt (x : W 8) :
          intMinFn jFn (-144) wHi (add m shift (L x)) ≤ -144 * emp x - dot8 wHi (M x) := by
        obtain ⟨off, hoff, hMx, hex⟩ := hpt x
        rw [hMx, hex]; unfold intMinFn
        have ⟨h0, h1, h2⟩ := min3_le
          (-144 * isEmptyOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 0 -
            dot8 wHi (cellRowOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 0))
          (-144 * isEmptyOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 1 -
            dot8 wHi (cellRowOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 1))
          (-144 * isEmptyOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 2 -
            dot8 wHi (cellRowOfJ (jFn (add m shift (L x))).1 (jFn (add m shift (L x))).2.1 (jFn (add m shift (L x))).2.2 2))
        rcases hoff with rfl | rfl | rfl <;> assumption
      have hlo_tot := total_mono 8 _ _ hlo_pt
      have hhi_tot := total_mono 8 _ _ hhi_pt
      rw [hsum, Int.mul_assoc, total_sub, total_scale, hN, hM_tot wLo, ← hreqLo] at hlo_tot
      rw [hsum, Int.mul_assoc, total_sub, total_scale, hN, hM_tot wHi, ← hreqHi] at hhi_tot
      have h64 (c : Int) : multOfLen B.length * ((2 : Int) ^ B.length * c) = 64 * c := by
        calc multOfLen B.length * ((2 : Int) ^ B.length * c)
            = ((2 : Int) ^ B.length * multOfLen B.length) * c := by ac_rfl
          _ = 64 * c := by rw [hpm]
      have hbLo_eq : reqLo + (multOfLenNat B.length : Int) * (cosetSumNat tLo B sh : Int) - 64 * cLo =
          reqLo + multOfLen B.length * cosetSum (intMinFn jFn 288 wLo) B sh := by
        change reqLo + multOfLen B.length * (cosetSumNat tLo B sh : Int) - 64 * cLo = _
        rw [hcsLo, Int.mul_add, h64 cLo]; omega
      have hbHi_eq : reqHi + (multOfLenNat B.length : Int) * (cosetSumNat tHi B sh : Int) - 64 * cHi =
          reqHi + multOfLen B.length * cosetSum (intMinFn jFn (-144) wHi) B sh := by
        change reqHi + multOfLen B.length * (cosetSumNat tHi B sh : Int) - 64 * cHi = _
        rw [hcsHi, Int.mul_add, h64 cHi]; omega
      rw [hbLo_eq, hbHi_eq] at hsh
      let bLo := reqLo + multOfLen B.length * cosetSum (intMinFn jFn 288 wLo) B sh
      let bHi := reqHi + multOfLen B.length * cosetSum (intMinFn jFn (-144) wHi) B sh
      have hN_lo : bLo ≤ 288 * N := by dsimp only [bLo]; omega
      have hN_hi : 144 * N ≤ -bHi := by dsimp only [bHi]; omega
      have hed := Int.ediv_add_emod (-bHi) 144
      have hrem_nn := Int.emod_nonneg (-bHi) (show (144 : Int) ≠ 0 by decide)
      have hrem_lt := Int.emod_lt_of_pos (-bHi) (show (0 : Int) < 144 by decide)
      have hN_le_q : N ≤ -bHi / 144 := by omega
      change 288 * (-bHi / 144) < bLo at hsh
      omega

/-! ## Section 4: Extracting the Linear 6-Flat `Z` and Sorted Sector Pair `(p, q)` -/

private theorem low_residue_cube (f g : Half) (lores : ∀ a, lo f g a % 8 = 0) :
    Cube (fun a : W 8 => decide (lo f g a % 16 ≠ 0)) := by
  intro u v w a
  have hord := low_residue_order f g lores [u, v, w] rfl a
  simp only [differences] at hord
  let Q (x : W 8) : Int := lo f g x / 8 + 1
  have heq (x : W 8) : (if decide (lo f g x % 16 ≠ 0) then (1 : Int) else 0) = 1 - Q x % 2 := by
    have hr := lores x; dsimp only [Q]
    by_cases h : lo f g x % 16 = 0
    · have hq : (lo f g x / 8 + 1) % 2 = 1 := by omega
      simp [h, hq]
    · have hq : (lo f g x / 8 + 1) % 2 = 0 := by omega
      simp [h, hq]
  have hparity (p1 p2 p3 p4 p5 p6 p7 p8 : Bool)
      (hsum : ((if p1 then (1:Int) else 0) + (if p2 then 1 else 0) + (if p3 then 1 else 0) +
               (if p4 then 1 else 0) + (if p5 then 1 else 0) + (if p6 then 1 else 0) +
               (if p7 then 1 else 0) + (if p8 then 1 else 0)) % 2 = 0) :
      xor (xor (xor p1 p2) (xor p3 p4)) (xor (xor p5 p6) (xor p7 p8)) = false := by
    cases p1 <;> cases p2 <;> cases p3 <;> cases p4 <;>
    cases p5 <;> cases p6 <;> cases p7 <;> cases p8 <;> simp_all
  exact hparity
    (decide (lo f g (add 8 u (add 8 v (add 8 w a))) % 16 ≠ 0))
    (decide (lo f g (add 8 v (add 8 w a)) % 16 ≠ 0))
    (decide (lo f g (add 8 u (add 8 w a)) % 16 ≠ 0))
    (decide (lo f g (add 8 w a) % 16 ≠ 0))
    (decide (lo f g (add 8 u (add 8 v a)) % 16 ≠ 0))
    (decide (lo f g (add 8 v a) % 16 ≠ 0))
    (decide (lo f g (add 8 u a) % 16 ≠ 0))
    (decide (lo f g a % 16 ≠ 0))
    (by
      simp only [heq]
      change (((Q (add 8 u (add 8 v (add 8 w a))) - Q (add 8 v (add 8 w a))) -
               (Q (add 8 u (add 8 w a)) - Q (add 8 w a))) -
              ((Q (add 8 u (add 8 v a)) - Q (add 8 v a)) -
               (Q (add 8 u a) - Q a))) % 2 = 0 at hord
      omega)

/-- Extract orthogonal basis `(p, q)` of `K = Z^⊥` so `lo(a) % 16 = 0 ↔ dot a p = false ∧ dot a q = false`. -/
private theorem extract_flat_pq (f g : Half) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (ht : agreements f g = 118) :
    ∃ p q : W 8, p ≠ zero 8 ∧ q ≠ zero 8 ∧ p ≠ q ∧
      (∀ a : W 8, lo f g a % 16 = 0 ↔ dot 8 a p = false ∧ dot 8 a q = false) := by
  obtain ⟨hZ64, _, _, _, _⟩ := large_support_counts f g dc lores locap (by omega)
  let β : W 8 → Bool := fun a => decide (lo f g a % 16 ≠ 0)
  have hCube : Cube β := low_residue_cube f g lores
  have hβ0 : β (zero 8) = false := by simp [β, dc]
  have htr0 : transform (fun a => sign (β a)) (zero 8) = -128 := by
    have hpt (a : W 8) : sign (β a) * chr (zero 8) a =
        2 * (if lo f g a % 16 = 0 then (1 : Int) else 0) - 1 := by
      simp only [chr, dot_zero, sign, β]
      by_cases h : lo f g a % 16 = 0 <;> simp [h]
    unfold transform
    rw [funext hpt, total_sub, total_scale, total_const, hZ64]
    change 2 * 64 - 256 * 1 = -128; decide
  have hsq0 := spec_good β hCube (zero 8)
  rw [htr0] at hsq0
  change (-128) * (-128) = 256 * (rr β * bind (good β (zero 8))) at hsq0
  have hgood0 : good β (zero 8) = true := by
    cases hg : good β (zero 8)
    · rw [hg] at hsq0; simp [Balanced242Plateau.ind] at hsq0
    · rfl
  have hrr64 : rr β = 64 := by
    rw [hgood0] at hsq0; simp only [Balanced242Plateau.ind, if_true, Int.mul_one] at hsq0; omega
  have hgood_eq_perp (y : W 8) : good β y = perp β y := by
    cases hy : perp β y
    · cases hg : good β y
      · rfl
      · have hp := good_perp β hgood0 hg
        rw [add_zero_left] at hp; rw [hp] at hy; exact absurd hy (by decide)
    · have hg := good_shift β hgood0 hy
      rwa [add_zero_left] at hg
  have hperp_tot : total 8 (fun w => bind (perp β w)) = 4 := by
    have hp := rr_perp β
    rw [hrr64] at hp; change 64 * total 8 (fun w => bind (perp β w)) = 256 at hp; omega
  have hperp0 : perp β (zero 8) = true := by rw [← hgood_eq_perp]; exact hgood0
  have hperp_add (u v : W 8) (hu : perp β u = true) (hv : perp β v = true) :
      perp β (add 8 u v) = true := by
    rw [perp_spec] at hu hv ⊢
    intro e he; rw [dot_add_l, hu e he, hv e he]; rfl
  -- Pick `p ≠ 0` in `perp β`
  have hex_p : ∃ p : W 8, perp β p = true ∧ p ≠ zero 8 := by
    have hpos : 0 < total 8 (fun w => if perp β w && decide (w ≠ zero 8) then (1 : Int) else 0) := by
      have hsplit : total 8 (fun w => bind (perp β w)) =
          total 8 (fun w => if w = zero 8 then bind (perp β w) else 0) +
          total 8 (fun w => if perp β w && decide (w ≠ zero 8) then (1 : Int) else 0) := by
        rw [← total_add]; apply congrArg (total 8); funext w
        by_cases hz : w = zero 8
        · subst hz; simp [hperp0, Balanced242Plateau.ind]
        · cases perp β w <;> simp [hz, Balanced242Plateau.ind]
      rw [total_single_eq (zero 8), hperp0, hperp_tot] at hsplit
      simp only [Balanced242Plateau.ind, if_true] at hsplit
      omega
    obtain ⟨p, hp⟩ := total_pos_exists _ hpos
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨p, hp.1, hp.2⟩
  obtain ⟨p, hp_perp, hp_ne⟩ := hex_p
  -- Pick `q ∉ {0, p}` in `perp β`
  have hex_q : ∃ q : W 8, perp β q = true ∧ q ≠ zero 8 ∧ q ≠ p := by
    have hpos : 0 < total 8 (fun w =>
        if perp β w && decide (w ≠ zero 8) && decide (w ≠ p) then (1 : Int) else 0) := by
      have hsplit : total 8 (fun w => bind (perp β w)) =
          total 8 (fun w => if w = zero 8 then (1 : Int) else 0) +
          total 8 (fun w => if w = p then (1 : Int) else 0) +
          total 8 (fun w => if perp β w && decide (w ≠ zero 8) && decide (w ≠ p) then (1 : Int) else 0) := by
        rw [← total_add, ← total_add]; apply congrArg (total 8); funext w
        by_cases h0 : w = zero 8
        · subst h0; simp [hperp0, hp_ne.symm, Balanced242Plateau.ind]
        · by_cases hp' : w = p
          · subst hp'; simp [hp_perp, h0, Balanced242Plateau.ind]
          · cases perp β w <;> simp [h0, hp', Balanced242Plateau.ind]
      rw [total_single_eq (zero 8), total_single_eq p] at hsplit; omega
    obtain ⟨q, hq⟩ := total_pos_exists _ hpos
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    exact ⟨q, hq.1.1, hq.1.2, hq.2⟩
  obtain ⟨q, hq_perp, hq_ne, hqp_ne⟩ := hex_q
  have hpq_perp : perp β (add 8 p q) = true := hperp_add p q hp_perp hq_perp
  have hpq_ne0 : add 8 p q ≠ zero 8 := fun h => hqp_ne (by
    have h2 := congrArg (add 8 p) h; rw [add_cancel_l, add_zero_right] at h2; exact h2)
  have hpq_nep : add 8 p q ≠ p := fun h => hq_ne (by
    have h2 := congrArg (add 8 p) h; rw [add_cancel_l, add_self] at h2; exact h2)
  have hpq_neq : add 8 p q ≠ q := fun h => hp_ne (by
    have h2 := congrArg (fun z => add 8 z q) h; dsimp only at h2; rw [add_cancel_r, add_self] at h2; exact h2)
  -- `perp β` has size 4 and already contains `{0, p, q, p⊕q}`, so nothing else is in `perp β`!
  have hperp_only (w : W 8) (hw : perp β w = true) :
      w = zero 8 ∨ w = p ∨ w = q ∨ w = add 8 p q := by
    by_cases h : w = zero 8 ∨ w = p ∨ w = q ∨ w = add 8 p q
    · exact h
    · exfalso
      have hge5 : 5 ≤ total 8 (fun u => bind (perp β u)) := by
        have hpt (u : W 8) :
            (if u = zero 8 then (1 : Int) else 0) +
            (if u = p then 1 else 0) +
            (if u = q then 1 else 0) +
            (if u = add 8 p q then 1 else 0) +
            (if u = w then 1 else 0) ≤ bind (perp β u) := by
          have hnw0 : w ≠ zero 8 := fun e => h (Or.inl e)
          have hnwp : w ≠ p := fun e => h (Or.inr (Or.inl e))
          have hnwq : w ≠ q := fun e => h (Or.inr (Or.inr (Or.inl e)))
          have hnwpq : w ≠ add 8 p q := fun e => h (Or.inr (Or.inr (Or.inr e)))
          by_cases h1 : u = zero 8
          · subst h1; simp [hperp0, hp_ne.symm, hq_ne.symm, hpq_ne0.symm, hnw0.symm, Balanced242Plateau.ind]
          · by_cases h2 : u = p
            · subst h2; simp [hp_perp, h1, hqp_ne.symm, hpq_nep.symm, hnwp.symm, Balanced242Plateau.ind]
            · by_cases h3 : u = q
              · subst h3; simp [hq_perp, h1, h2, hpq_neq.symm, hnwq.symm, Balanced242Plateau.ind]
              · by_cases h4 : u = add 8 p q
                · subst h4; simp [hpq_perp, h1, h2, h3, hnwpq.symm, Balanced242Plateau.ind]
                · by_cases h5 : u = w
                  · subst h5; simp [hw, h1, h2, h3, h4, Balanced242Plateau.ind]
                  · simp [h1, h2, h3, h4, h5]; exact ind_nonneg _
        have htot := total_mono 8 _ _ hpt
        simp only [total_add, total_single_eq] at htot; omega
      omega
  -- For every `y`, compute `transform (sign ∘ β) y`
  have htr_val (y : W 8) :
      (perp β y = false → transform (fun a => sign (β a)) y = 0) ∧
      (perp β y = true → transform (fun a => sign (β a)) y = 128 ∨
                         transform (fun a => sign (β a)) y = -128) := by
    have hsq := spec_good β hCube y
    rw [hgood_eq_perp, hrr64] at hsq
    constructor
    · intro hf; rw [hf] at hsq; simp [Balanced242Plateau.ind] at hsq
      have h0 := sq_cases (transform (fun a => sign (β a)) y) 0 (by omega)
      rcases h0 with h | h <;> omega
    · intro ht'; rw [ht'] at hsq; simp only [Balanced242Plateau.ind, if_true, Int.mul_one] at hsq
      change transform (fun a => sign (β a)) y * transform (fun a => sign (β a)) y = 128 * 128 at hsq
      exact sq_cases _ 128 hsq
  -- Expansion of `inversion` over the 4 elements `{0, p, q, p⊕q}`
  have hinv_4 (a : W 8) :
      256 * sign (β a) =
        transform (fun b => sign (β b)) (zero 8) +
        transform (fun b => sign (β b)) p * chr p a +
        transform (fun b => sign (β b)) q * chr q a +
        transform (fun b => sign (β b)) (add 8 p q) * chr (add 8 p q) a := by
    have hinv := inversion (fun b => sign (β b)) a
    change total 8 (fun y => transform (fun b => sign (β b)) y * chr y a) = 256 * sign (β a) at hinv
    rw [← hinv]
    have hsplit : total 8 (fun y => transform (fun b => sign (β b)) y * chr y a) =
        total 8 (fun y => if y = zero 8 then transform (fun b => sign (β b)) y * chr y a else 0) +
        total 8 (fun y => if y = p then transform (fun b => sign (β b)) y * chr y a else 0) +
        total 8 (fun y => if y = q then transform (fun b => sign (β b)) y * chr y a else 0) +
        total 8 (fun y => if y = add 8 p q then transform (fun b => sign (β b)) y * chr y a else 0) := by
      rw [← total_add, ← total_add, ← total_add]
      apply congrArg (total 8); funext y
      by_cases h1 : y = zero 8
      · subst h1; simp [hp_ne.symm, hq_ne.symm, hpq_ne0.symm]
      · by_cases h2 : y = p
        · subst h2; simp [h1, hqp_ne.symm, hpq_nep.symm]
        · by_cases h3 : y = q
          · subst h3; simp [h1, h2, hpq_neq.symm]
          · by_cases h4 : y = add 8 p q
            · subst h4; simp [h1, h2, h3]
            · have hpf : perp β y = false := by
                cases hpy : perp β y
                · rfl
                · rcases hperp_only y hpy with e | e | e | e <;> contradiction
              rw [(htr_val y).1 hpf]; simp [h1, h2, h3, h4]
    rw [hsplit, total_single_eq (zero 8), total_single_eq p, total_single_eq q, total_single_eq (add 8 p q)]
    have hc0a : chr (zero 8) a = 1 := by simp [chr, dot_zero, sign]
    rw [hc0a, Int.mul_one]
  -- At `a = zero 8`: all three of `p, q, p⊕q` must have transform `+128`!
  have hinv0 := hinv_4 (zero 8)
  rw [hβ0, htr0] at hinv0
  have hs0 : sign false = 1 := rfl
  have hc0 (d : W 8) : chr d (zero 8) = 1 := by simp [chr, dot_zero_right, sign]
  rw [hs0, hc0 p, hc0 q, hc0 (add 8 p q)] at hinv0
  simp only [Int.mul_one] at hinv0
  have hp128 := (htr_val p).2 hp_perp
  have hq128 := (htr_val q).2 hq_perp
  have hpq128 := (htr_val (add 8 p q)).2 hpq_perp
  have htp : transform (fun b => sign (β b)) p = 128 := by
    rcases hp128 with h | h <;> rcases hq128 with h' | h' <;> rcases hpq128 with h'' | h'' <;> omega
  have htq : transform (fun b => sign (β b)) q = 128 := by
    rcases hp128 with h | h <;> rcases hq128 with h' | h' <;> rcases hpq128 with h'' | h'' <;> omega
  have htpq : transform (fun b => sign (β b)) (add 8 p q) = 128 := by
    rcases hp128 with h | h <;> rcases hq128 with h' | h' <;> rcases hpq128 with h'' | h'' <;> omega
  refine ⟨p, q, hp_ne, hq_ne, hqp_ne.symm, fun a => ?_⟩
  have ha := hinv_4 a
  rw [htr0, htp, htq, htpq] at ha
  simp only [chr, dot_comm 8 p a, dot_comm 8 q a, dot_comm 8 (add 8 p q) a, dot_right] at ha
  have hsf : sign false = 1 := rfl
  have hst : sign true = -1 := rfl
  cases h1 : dot 8 a p <;> cases h2 : dot 8 a q <;>
    simp only [h1, h2, Bool.false_xor, Bool.true_xor, Bool.xor_false, Bool.xor_self, hsf, hst] at ha
  · by_cases hz : lo f g a % 16 = 0
    · simp [hz]
    · have hβt : β a = true := by simp [β, hz]
      rw [hβt, hst] at ha; omega
  · by_cases hz : lo f g a % 16 = 0
    · have hβf : β a = false := by simp [β, hz]
      rw [hβf, hsf] at ha; omega
    · simp [hz]
  · by_cases hz : lo f g a % 16 = 0
    · have hβf : β a = false := by simp [β, hz]
      rw [hβf, hsf] at ha; omega
    · simp [hz]
  · by_cases hz : lo f g a % 16 = 0
    · have hβf : β a = false := by simp [β, hz]
      rw [hβf, hsf] at ha; omega
    · simp [hz]

/-- Sector label `∈ {0, 1, 2, 3}` of frequency `a` relative to `(p, q)`. -/
private def secOf (p q a : W 8) : Nat :=
  (if dot 8 a p then 1 else 0) + (if dot 8 a q then 2 else 0)

/-- Number of magnitude-8 low masks in sector `s ∈ {1, 2, 3}`. -/
private def secCount (f g : Half) (p q : W 8) (s : Nat) : Int :=
  total 8 (fun a => if secOf p q a == s && decide ((lo f g a).natAbs = 8) then (1 : Int) else 0)

/-- Permuting `(p, q)` among the 6 ordered pairs of distinct nonzero elements of `{p, q, p⊕q}`
    sorts the three sector counts so `c1 ≤ c2 ≤ c3` and forces one of the 4 exact triples! -/
private theorem extract_sorted_pq (f g : Half) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (ht : agreements f g = 118) :
    ∃ p q : W 8, p ≠ zero 8 ∧ q ≠ zero 8 ∧ p ≠ q ∧
      (∀ a : W 8, lo f g a % 16 = 0 ↔ dot 8 a p = false ∧ dot 8 a q = false) ∧
      ((secCount f g p q 1 = 2 ∧ secCount f g p q 2 = 2 ∧ secCount f g p q 3 = 2) ∨
       (secCount f g p q 1 = 1 ∧ secCount f g p q 2 = 3 ∧ secCount f g p q 3 = 3) ∨
       (secCount f g p q 1 = 0 ∧ secCount f g p q 2 = 4 ∧ secCount f g p q 3 = 4) ∨
       (secCount f g p q 1 = 2 ∧ secCount f g p q 2 = 2 ∧ secCount f g p q 3 = 4)) := by
  obtain ⟨p0, q0, hp0, hq0, hpq0, hZ0⟩ := extract_flat_pq f g dc lores locap ht
  obtain ⟨_, hn0_ge8, _, hdef, _⟩ := large_support_counts f g dc lores locap (by omega)
  rw [ht] at hdef
  have hpair_bounds (p q : W 8) (hp : p ≠ zero 8) (hq : q ≠ zero 8) (hpq : p ≠ q)
      (hZ : ∀ a : W 8, lo f g a % 16 = 0 ↔ dot 8 a p = false ∧ dot 8 a q = false) :
      let c1 := secCount f g p q 1
      let c2 := secCount f g p q 2
      let c3 := secCount f g p q 3
      0 ≤ c1 ∧ 0 ≤ c2 ∧ 0 ≤ c3 ∧ c1 + c2 + c3 ≤ 8 ∧
      (c1 + c2 = 4 ∨ 6 ≤ c1 + c2) ∧
      (c1 + c3 = 4 ∨ 6 ≤ c1 + c3) ∧
      (c2 + c3 = 4 ∨ 6 ≤ c2 + c3) := by
    have hnn (s : Nat) : 0 ≤ secCount f g p q s :=
      total_nonneg_int _ (fun a => by split <;> omega)
    have hsum_le : secCount f g p q 1 + secCount f g p q 2 + secCount f g p q 3 ≤ 8 := by
      have htot : secCount f g p q 1 + secCount f g p q 2 + secCount f g p q 3 =
          multiplicity (lo f g) 8 := by
        unfold secCount multiplicity
        rw [← total_add, ← total_add]
        apply congrArg (total 8); funext a
        unfold secOf
        cases h1 : dot 8 a p <;> cases h2 : dot 8 a q
        · have hz := (hZ a).2 ⟨h1, h2⟩
          have hne : (lo f g a).natAbs ≠ 8 := by omega
          simp [hne]
        · by_cases h8 : (lo f g a).natAbs = 8 <;> simp [h8]
        · by_cases h8 : (lo f g a).natAbs = 8 <;> simp [h8]
        · by_cases h8 : (lo f g a).natAbs = 8 <;> simp [h8]
      omega
    have hhalf (d : W 8) (hd : d ≠ zero 8)
        (hoff : ∀ a, dot 8 a d = true → lo f g a % 16 ≠ 0) :
        total 8 (smallIn f g d) = 4 ∨ 6 ≤ total 8 (smallIn f g d) := by
      have hlev (a : W 8) (ha : dot 8 a d = true) :
          (lo f g a).natAbs = 8 ∨ (lo f g a).natAbs = 24 := by
        have r := lores a; have c := locap a; have o := hoff a ha; omega
      have ⟨h4, hodd, _⟩ := halfspace_small_counts f g d hd hlev
      by_cases h5 : total 8 (smallIn f g d) = 5
      · have := hodd (by rw [h5]; decide); omega
      · omega
    have hr_ne : add 8 p q ≠ zero 8 := fun h => hpq (by
      have h2 := congrArg (add 8 p) h; rw [add_cancel_l, add_zero_right] at h2; exact h2.symm)
    have h_p := hhalf p hp (fun a ha hz => by rw [(hZ a).1 hz |>.1] at ha; exact absurd ha (by decide))
    have h_q := hhalf q hq (fun a ha hz => by rw [(hZ a).1 hz |>.2] at ha; exact absurd ha (by decide))
    have h_r := hhalf (add 8 p q) hr_ne (fun a ha hz => by
      have ⟨h1, h2⟩ := (hZ a).1 hz; rw [dot_right, h1, h2] at ha; exact absurd ha (by decide))
    have eq_p : total 8 (smallIn f g p) = secCount f g p q 1 + secCount f g p q 3 := by
      unfold smallIn secCount; rw [← total_add]
      apply congrArg (total 8); funext a; unfold secOf
      cases dot 8 a p <;> cases dot 8 a q <;> cases decide ((lo f g a).natAbs = 8) <;> decide
    have eq_q : total 8 (smallIn f g q) = secCount f g p q 2 + secCount f g p q 3 := by
      unfold smallIn secCount; rw [← total_add]
      apply congrArg (total 8); funext a; unfold secOf
      cases dot 8 a p <;> cases dot 8 a q <;> cases decide ((lo f g a).natAbs = 8) <;> decide
    have eq_r : total 8 (smallIn f g (add 8 p q)) = secCount f g p q 1 + secCount f g p q 2 := by
      unfold smallIn secCount; rw [← total_add]
      apply congrArg (total 8); funext a; unfold secOf
      rw [dot_right]
      cases dot 8 a p <;> cases dot 8 a q <;> cases decide ((lo f g a).natAbs = 8) <;> decide
    rw [eq_p] at h_p; rw [eq_q] at h_q; rw [eq_r] at h_r
    exact ⟨hnn 1, hnn 2, hnn 3, hsum_le, h_r, h_p, h_q⟩
  -- Helper: given any `(p, q)` with `c1 ≤ c2 ≤ c3`, conclude the 4 triples
  have finish (p q : W 8) (hp : p ≠ zero 8) (hq : q ≠ zero 8) (hpq : p ≠ q)
      (hZ : ∀ a : W 8, lo f g a % 16 = 0 ↔ dot 8 a p = false ∧ dot 8 a q = false)
      (h12 : secCount f g p q 1 ≤ secCount f g p q 2)
      (h23 : secCount f g p q 2 ≤ secCount f g p q 3) :
      ∃ p' q' : W 8, p' ≠ zero 8 ∧ q' ≠ zero 8 ∧ p' ≠ q' ∧
        (∀ a : W 8, lo f g a % 16 = 0 ↔ dot 8 a p' = false ∧ dot 8 a q' = false) ∧
        ((secCount f g p' q' 1 = 2 ∧ secCount f g p' q' 2 = 2 ∧ secCount f g p' q' 3 = 2) ∨
         (secCount f g p' q' 1 = 1 ∧ secCount f g p' q' 2 = 3 ∧ secCount f g p' q' 3 = 3) ∨
         (secCount f g p' q' 1 = 0 ∧ secCount f g p' q' 2 = 4 ∧ secCount f g p' q' 3 = 4) ∨
         (secCount f g p' q' 1 = 2 ∧ secCount f g p' q' 2 = 2 ∧ secCount f g p' q' 3 = 4)) := by
    have ⟨h01, h02, h03, hsum, h12b, h13b, h23b⟩ := hpair_bounds p q hp hq hpq hZ
    refine ⟨p, q, hp, hq, hpq, hZ, ?_⟩
    omega
  -- Helper: swapping `p` and `q` swaps sectors 1 and 2; replacing `q` by `p⊕q` swaps sectors 1 and 3
  have swap12 (p q : W 8) (hp : p ≠ zero 8) (hq : q ≠ zero 8) (hpq : p ≠ q)
      (hZ : ∀ a : W 8, lo f g a % 16 = 0 ↔ dot 8 a p = false ∧ dot 8 a q = false) :
      q ≠ zero 8 ∧ p ≠ zero 8 ∧ q ≠ p ∧
      (∀ a : W 8, lo f g a % 16 = 0 ↔ dot 8 a q = false ∧ dot 8 a p = false) ∧
      secCount f g q p 1 = secCount f g p q 2 ∧
      secCount f g q p 2 = secCount f g p q 1 ∧
      secCount f g q p 3 = secCount f g p q 3 := by
    refine ⟨hq, hp, hpq.symm, fun a => (hZ a).trans and_comm, ?_, ?_, ?_⟩
    all_goals
      unfold secCount; apply congrArg (total 8); funext a; unfold secOf
      cases dot 8 a p <;> cases dot 8 a q <;> cases decide ((lo f g a).natAbs = 8) <;> decide
  have swap13 (p q : W 8) (hp : p ≠ zero 8) (hq : q ≠ zero 8) (hpq : p ≠ q)
      (hZ : ∀ a : W 8, lo f g a % 16 = 0 ↔ dot 8 a p = false ∧ dot 8 a q = false) :
      let r := add 8 p q
      p ≠ zero 8 ∧ r ≠ zero 8 ∧ p ≠ r ∧
      (∀ a : W 8, lo f g a % 16 = 0 ↔ dot 8 a p = false ∧ dot 8 a r = false) ∧
      secCount f g p r 1 = secCount f g p q 3 ∧
      secCount f g p r 2 = secCount f g p q 2 ∧
      secCount f g p r 3 = secCount f g p q 1 := by
    have hr0 : add 8 p q ≠ zero 8 := fun h => hpq (by
      have h2 := congrArg (add 8 p) h; rw [add_cancel_l, add_zero_right] at h2; exact h2.symm)
    have hpr : p ≠ add 8 p q := fun h => hq (by
      have h2 := congrArg (add 8 p) h; rw [add_self, add_cancel_l] at h2; exact h2.symm)
    refine ⟨hp, hr0, hpr, ?_, ?_, ?_, ?_⟩
    · intro a; rw [hZ a, dot_right]
      cases dot 8 a p <;> cases dot 8 a q <;> decide
    all_goals
      unfold secCount; apply congrArg (total 8); funext a; unfold secOf; rw [dot_right]
      cases dot 8 a p <;> cases dot 8 a q <;> cases decide ((lo f g a).natAbs = 8) <;> decide
  -- Sort `(c1, c2, c3)` using 3-step bubble sort (swap12, swap13/swap23, swap12)
  -- Step A: ensure `c1 ≤ c2`
  have stepA : ∃ p1 q1 : W 8, p1 ≠ zero 8 ∧ q1 ≠ zero 8 ∧ p1 ≠ q1 ∧
      (∀ a : W 8, lo f g a % 16 = 0 ↔ dot 8 a p1 = false ∧ dot 8 a q1 = false) ∧
      secCount f g p1 q1 1 ≤ secCount f g p1 q1 2 := by
    by_cases h : secCount f g p0 q0 1 ≤ secCount f g p0 q0 2
    · exact ⟨p0, q0, hp0, hq0, hpq0, hZ0, h⟩
    · have ⟨h1, h2, h3, h4, e1, e2, _⟩ := swap12 p0 q0 hp0 hq0 hpq0 hZ0
      exact ⟨q0, p0, h1, h2, h3, h4, by omega⟩
  obtain ⟨p1, q1, hp1, hq1, hpq1, hZ1, h12_1⟩ := stepA
  -- Step B: ensure `c3` is the maximum (`c1 ≤ c3 ∧ c2 ≤ c3`)
  have stepB : ∃ p2 q2 : W 8, p2 ≠ zero 8 ∧ q2 ≠ zero 8 ∧ p2 ≠ q2 ∧
      (∀ a : W 8, lo f g a % 16 = 0 ↔ dot 8 a p2 = false ∧ dot 8 a q2 = false) ∧
      secCount f g p2 q2 1 ≤ secCount f g p2 q2 3 ∧
      secCount f g p2 q2 2 ≤ secCount f g p2 q2 3 := by
    by_cases h : secCount f g p1 q1 2 ≤ secCount f g p1 q1 3
    · exact ⟨p1, q1, hp1, hq1, hpq1, hZ1, by omega, h⟩
    · -- `c2 > c3` and `c2 ≥ c1`, so swap sectors 2 and 3 (swap12, then swap13)
      have ⟨a1, a2, a3, a4, ea1, ea2, ea3⟩ := swap12 p1 q1 hp1 hq1 hpq1 hZ1
      have ⟨b1, b2, b3, b4, eb1, eb2, eb3⟩ := swap13 q1 p1 a1 a2 a3 a4
      exact ⟨q1, add 8 q1 p1, b1, b2, b3, b4, by omega, by omega⟩
  obtain ⟨p2, q2, hp2, hq2, hpq2, hZ2, h13_2, h23_2⟩ := stepB
  -- Step C: ensure `c1 ≤ c2` again while keeping `c3` fixed!
  by_cases h : secCount f g p2 q2 1 ≤ secCount f g p2 q2 2
  · exact finish p2 q2 hp2 hq2 hpq2 hZ2 h h23_2
  · have ⟨h1, h2, h3, h4, e1, e2, e3⟩ := swap12 p2 q2 hp2 hq2 hpq2 hZ2
    exact finish q2 p2 h1 h2 h3 h4 (by omega) (by omega)

/-! ## Section 5: Four-Cell Walsh Identities, Mod-3 Congruence, and Moment Totals -/

private theorem duality_w8 (D B : W 8 → Int) :
    total 8 (fun x => D x * transform B x) = total 8 (fun a => B a * transform D a) := by
  simp only [transform, ← total_scale]
  rw [swap]
  apply congrArg (total 8); funext a
  apply congrArg (total 8); funext x
  rw [Balanced242Section0320.chr_comm]
  ac_rfl

private theorem sum_mod3 (F G : W 8 → Int) (h : ∀ a, (F a - G a) % 3 = 0) :
    (total 8 F - total 8 G) % 3 = 0 := by
  rw [← total_sub]
  have aux : ∀ (n : Nat) (H : W n → Int), (∀ x, H x % 3 = 0) → total n H % 3 = 0 := by
    intro n; induction n with
    | zero => intro H hH; exact hH ()
    | succ n ih =>
      intro H hH
      change (total n (fun x => H (false, x)) + total n (fun x => H (true, x))) % 3 = 0
      have h1 := ih (fun x => H (false, x)) (fun x => hH (false, x))
      have h2 := ih (fun x => H (true, x)) (fun x => hH (true, x))
      omega
  exact aux 8 (fun a => F a - G a) h

/-- Core four-cell moment package for a fixed `(p, q)` orthogonal basis of `Z^⊥`. -/
private theorem cell_moments_package (f g : Half) (p q : W 8)
    (dc : lo f g (zero 8) = 0) (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24) (ht : agreements f g = 118)
    (hZ : ∀ a : W 8, lo f g a % 16 = 0 ↔ dot 8 a p = false ∧ dot 8 a q = false)
    (hp : p ≠ zero 8) (hq : q ≠ zero 8) (hpq : p ≠ q) :
    let V := Vtbl f g
    let v0 (x : W 8) := V x
    let v1 (x : W 8) := V (add 8 p x)
    let v2 (x : W 8) := V (add 8 q x)
    let v3 (x : W 8) := V (add 8 (add 8 p q) x)
    let z0 (x : W 8) := v0 x + v1 x + v2 x + v3 x
    let z1 (x : W 8) := v0 x - v1 x + v2 x - v3 x
    let z2 (x : W 8) := v0 x + v1 x - v2 x - v3 x
    let z3 (x : W 8) := v0 x - v1 x - v2 x + v3 x
    let B (s : Nat) (a : W 8) : Int :=
      if secOf p q a == s && decide ((lo f g a).natAbs = 8) then lo f g a / 8 else 0
    let j1 (x : W 8) := transform (B 1) x
    let j2 (x : W 8) := transform (B 2) x
    let j3 (x : W 8) := transform (B 3) x
    let M (x : W 8) : CellRow :=
      (v0 x * v0 x + v1 x * v1 x + v2 x * v2 x + v3 x * v3 x,
       z1 x * z1 x, z2 x * z2 x, z3 x * z3 x,
       z1 x * j1 x, z2 x * j2 x, z3 x * j3 x, z0 x)
    let emp (x : W 8) : Int :=
      if v0 x = 0 && v1 x = 0 && v2 x = 0 && v3 x = 0 then 1 else 0
    let target : CellRow :=
      (118, 144 - 2 * secCount f g p q 1, 144 - 2 * secCount f g p q 2,
       144 - 2 * secCount f g p q 3,
       4 * secCount f g p q 1, 4 * secCount f g p q 2, 4 * secCount f g p q 3, 0)
    -- (1) Invariance on every 4-point coset `x + K`
    (∀ x, M (add 8 p x) = M x ∧ M (add 8 q x) = M x ∧
          emp (add 8 p x) = emp x ∧ emp (add 8 q x) = emp x) ∧
    -- (2) Pointwise ternary cell reconstruction from `(j1, j2, j3)` and `z0 % 3`
    (∀ x, ∃ off : Int, (off = 0 ∨ off = 1 ∨ off = 2) ∧
          M x = cellRowOfJ (j1 x) (j2 x) (j3 x) off ∧
          emp x = isEmptyOfJ (j1 x) (j2 x) (j3 x) off) ∧
    -- (3) Exact global totals of all 8 moments (`= 4 * dot8 w target`)
    (∀ w : CellRow, total 8 (fun x => dot8 w (M x)) = 4 * dot8 w target) ∧
    -- (4) Divisibility of empty-cell count over `W 8` by 4
    (∃ N : Int, total 8 emp = 4 * N) := by
  intro V v0 v1 v2 v3 z0 z1 z2 z3 B j1 j2 j3 M emp target
  have hV_vals (x : W 8) : V x = -1 ∨ V x = 0 ∨ V x = 1 := by
    unfold V Vtbl; cases f x <;> cases g x <;> simp [sign]
  -- (A) Exact transforms of `z1, z2, z3`
  have htr_shift (d : W 8) (a : W 8) :
      transform (fun x => V (add 8 d x)) a = sign (dot 8 a d) * transform V a := by
    unfold transform
    have hsh := sum_shift 8 d (fun x => V (add 8 d x) * chr a x)
    rw [← hsh]
    have hpt (x : W 8) : V (add 8 d (add 8 d x)) * chr a (add 8 d x) =
        sign (dot 8 a d) * (V x * chr a x) := by
      rw [add_cancel_l, chr, dot_right, signMul]; unfold chr; ac_rfl
    rw [funext hpt, total_scale]
  have htr_z (s : Nat) (hs : s = 1 ∨ s = 2 ∨ s = 3) (a : W 8) :
      transform (if s = 1 then z1 else if s = 2 then z2 else z3) a =
        if secOf p q a == s then 2 * lo f g a else 0 := by
    have h1 := htr_shift p a
    have h2 := htr_shift q a
    have h3 := htr_shift (add 8 p q) a
    have hlo : lo f g a = 2 * transform V a := lo_eq_2_transform_V f g a
    rcases hs with rfl | rfl | rfl
    · simp only [if_true]
      have hexp : transform z1 a = transform V a - transform (fun x => V (add 8 p x)) a +
          transform (fun x => V (add 8 q x)) a - transform (fun x => V (add 8 (add 8 p q) x)) a := by
        unfold transform z1 v0 v1 v2 v3
        simp only [Int.add_mul, Int.sub_mul, total_add, total_sub]
      rw [hexp, h1, h2, h3, dot_right]
      unfold secOf; cases dot 8 a p <;> cases dot 8 a q <;> simp [sign] <;> omega
    · simp only [show (2 : Nat) ≠ 1 by decide, if_false, if_true]
      have hexp : transform z2 a = transform V a + transform (fun x => V (add 8 p x)) a -
          transform (fun x => V (add 8 q x)) a - transform (fun x => V (add 8 (add 8 p q) x)) a := by
        unfold transform z2 v0 v1 v2 v3
        simp only [Int.add_mul, Int.sub_mul, total_add, total_sub]
      rw [hexp, h1, h2, h3, dot_right]
      unfold secOf; cases dot 8 a p <;> cases dot 8 a q <;> simp [sign] <;> omega
    · simp only [show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, if_false]
      have hexp : transform z3 a = transform V a - transform (fun x => V (add 8 p x)) a -
          transform (fun x => V (add 8 q x)) a + transform (fun x => V (add 8 (add 8 p q) x)) a := by
        unfold transform z3 v0 v1 v2 v3
        simp only [Int.add_mul, Int.sub_mul, total_add, total_sub]
      rw [hexp, h1, h2, h3, dot_right]
      unfold secOf; cases dot 8 a p <;> cases dot 8 a q <;> simp [sign] <;> omega
  have htr_z1 (a : W 8) : transform z1 a = if secOf p q a == 1 then 2 * lo f g a else 0 :=
    htr_z 1 (Or.inl rfl) a
  have htr_z2 (a : W 8) : transform z2 a = if secOf p q a == 2 then 2 * lo f g a else 0 :=
    htr_z 2 (Or.inr (Or.inl rfl)) a
  have htr_z3 (a : W 8) : transform z3 a = if secOf p q a == 3 then 2 * lo f g a else 0 :=
    htr_z 3 (Or.inr (Or.inr rfl)) a
  -- (B) Coset invariance under `p` and `q`
  have hj_p (s : Nat) (x : W 8) :
      transform (B s) (add 8 p x) = (if s = 1 ∨ s = 3 then -1 else 1) * transform (B s) x := by
    unfold transform; rw [← total_scale]
    apply congrArg (total 8); funext a
    dsimp only [B]
    cases hs : (secOf p q a == s && decide ((lo f g a).natAbs = 8)) with
    | false => simp
    | true =>
      simp only [if_true]
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      rw [chr, dot_add_l, dot_comm 8 p a, dot_comm 8 x a, signMul]
      unfold chr; rw [dot_comm 8 x a]
      have hsec := hs.1
      unfold secOf at hsec
      cases h1 : dot 8 a p <;> cases h2 : dot 8 a q <;> rw [h1, h2] at hsec <;>
        simp at hsec <;> subst hsec <;> simp [sign] <;> omega
  have hj_q (s : Nat) (x : W 8) :
      transform (B s) (add 8 q x) = (if s = 2 ∨ s = 3 then -1 else 1) * transform (B s) x := by
    unfold transform; rw [← total_scale]
    apply congrArg (total 8); funext a
    dsimp only [B]
    cases hs : (secOf p q a == s && decide ((lo f g a).natAbs = 8)) with
    | false => simp
    | true =>
      simp only [if_true]
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      rw [chr, dot_add_l, dot_comm 8 q a, dot_comm 8 x a, signMul]
      unfold chr; rw [dot_comm 8 x a]
      have hsec := hs.1
      unfold secOf at hsec
      cases h1 : dot 8 a p <;> cases h2 : dot 8 a q <;> rw [h1, h2] at hsec <;>
        simp at hsec <;> subst hsec <;> simp [sign] <;> omega
  have hinv_pq (x : W 8) :
      M (add 8 p x) = M x ∧ M (add 8 q x) = M x ∧
      emp (add 8 p x) = emp x ∧ emp (add 8 q x) = emp x := by
    have hv_p : v0 (add 8 p x) = v1 x ∧ v1 (add 8 p x) = v0 x ∧
                v2 (add 8 p x) = v3 x ∧ v3 (add 8 p x) = v2 x := by
      refine ⟨rfl, ?_, ?_, ?_⟩
      · dsimp only [v1, v0]; rw [add_cancel_l]
      · dsimp only [v2, v3]; rw [← add_assoc_w, add_comm 8 q p]
      · dsimp only [v3, v2]; rw [add_assoc_w, add_comm 8 q (add 8 p x), ← add_assoc_w, add_cancel_l, add_comm 8 x q]
    have hv_q : v0 (add 8 q x) = v2 x ∧ v1 (add 8 q x) = v3 x ∧
                v2 (add 8 q x) = v0 x ∧ v3 (add 8 q x) = v1 x := by
      refine ⟨rfl, ?_, ?_, ?_⟩
      · dsimp only [v1, v3]; rw [← add_assoc_w]
      · dsimp only [v2, v0]; rw [add_cancel_l]
      · dsimp only [v3, v1]; rw [add_assoc_w, add_cancel_l]
    have hj1p : j1 (add 8 p x) = -j1 x := by have := hj_p 1 x; simp at this; exact this
    have hj2p : j2 (add 8 p x) = j2 x := by have := hj_p 2 x; simp at this; exact this
    have hj3p : j3 (add 8 p x) = -j3 x := by have := hj_p 3 x; simp at this; exact this
    have hj1q : j1 (add 8 q x) = j1 x := by have := hj_q 1 x; simp at this; exact this
    have hj2q : j2 (add 8 q x) = -j2 x := by have := hj_q 2 x; simp at this; exact this
    have hj3q : j3 (add 8 q x) = -j3 x := by have := hj_q 3 x; simp at this; exact this
    have hz0p : z0 (add 8 p x) = z0 x := by dsimp only [z0]; rw [hv_p.1, hv_p.2.1, hv_p.2.2.1, hv_p.2.2.2]; omega
    have hz1p : z1 (add 8 p x) = -z1 x := by dsimp only [z1]; rw [hv_p.1, hv_p.2.1, hv_p.2.2.1, hv_p.2.2.2]; omega
    have hz2p : z2 (add 8 p x) = z2 x := by dsimp only [z2]; rw [hv_p.1, hv_p.2.1, hv_p.2.2.1, hv_p.2.2.2]; omega
    have hz3p : z3 (add 8 p x) = -z3 x := by dsimp only [z3]; rw [hv_p.1, hv_p.2.1, hv_p.2.2.1, hv_p.2.2.2]; omega
    have hz0q : z0 (add 8 q x) = z0 x := by dsimp only [z0]; rw [hv_q.1, hv_q.2.1, hv_q.2.2.1, hv_q.2.2.2]; omega
    have hz1q : z1 (add 8 q x) = z1 x := by dsimp only [z1]; rw [hv_q.1, hv_q.2.1, hv_q.2.2.1, hv_q.2.2.2]; omega
    have hz2q : z2 (add 8 q x) = -z2 x := by dsimp only [z2]; rw [hv_q.1, hv_q.2.1, hv_q.2.2.1, hv_q.2.2.2]; omega
    have hz3q : z3 (add 8 q x) = -z3 x := by dsimp only [z3]; rw [hv_q.1, hv_q.2.1, hv_q.2.2.1, hv_q.2.2.2]; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [M]
      rw [hv_p.1, hv_p.2.1, hv_p.2.2.1, hv_p.2.2.2,
          hz0p, hz1p, hz2p, hz3p, hj1p, hj2p, hj3p,
          Int.neg_mul_neg, Int.neg_mul_neg, Int.neg_mul_neg, Int.neg_mul_neg]
      have hm0 : v1 x * v1 x + v0 x * v0 x + v3 x * v3 x + v2 x * v2 x =
          v0 x * v0 x + v1 x * v1 x + v2 x * v2 x + v3 x * v3 x := by omega
      rw [hm0]
    · dsimp only [M]
      rw [hv_q.1, hv_q.2.1, hv_q.2.2.1, hv_q.2.2.2,
          hz0q, hz1q, hz2q, hz3q, hj1q, hj2q, hj3q,
          Int.neg_mul_neg, Int.neg_mul_neg, Int.neg_mul_neg, Int.neg_mul_neg]
      have hm0 : v2 x * v2 x + v3 x * v3 x + v0 x * v0 x + v1 x * v1 x =
          v0 x * v0 x + v1 x * v1 x + v2 x * v2 x + v3 x * v3 x := by omega
      rw [hm0]
    · dsimp only [emp]; rw [hv_p.1, hv_p.2.1, hv_p.2.2.1, hv_p.2.2.2]
      by_cases h0 : v0 x = 0 <;> by_cases h1 : v1 x = 0 <;>
      by_cases h2 : v2 x = 0 <;> by_cases h3 : v3 x = 0 <;> simp [h0, h1, h2, h3]
    · dsimp only [emp]; rw [hv_q.1, hv_q.2.1, hv_q.2.2.1, hv_q.2.2.2]
      by_cases h0 : v0 x = 0 <;> by_cases h1 : v1 x = 0 <;>
      by_cases h2 : v2 x = 0 <;> by_cases h3 : v3 x = 0 <;> simp [h0, h1, h2, h3]
  -- (C) Mod-3 congruence `z_s(x) ≡ j_s(x) (mod 3)` for `s ∈ {1, 2, 3}`
  have hmod3_sec (s : Nat) (zs : W 8 → Int)
      (htrz : ∀ a, transform zs a = if secOf p q a == s then 2 * lo f g a else 0)
      (hs0 : s ≠ 0) (x : W 8) : (zs x - transform (B s) x) % 3 = 0 := by
    have hinv := inversion zs x
    have hpt (a : W 8) : (transform zs a * chr a x - B s a * chr x a) % 3 = 0 := by
      rw [htrz a, Balanced242Section0320.chr_comm x a]
      dsimp only [B]
      cases hsec : secOf p q a == s with
      | false => simp
      | true =>
        have hnz : lo f g a % 16 ≠ 0 := by
          intro h16
          have ⟨h1, h2⟩ := (hZ a).1 h16
          have : secOf p q a = 0 := by simp [secOf, h1, h2]
          rw [this] at hsec; simp only [beq_iff_eq] at hsec; exact hs0 hsec.symm
        have hr := lores a; have hc := locap a
        have hvals : lo f g a = -24 ∨ lo f g a = -8 ∨ lo f g a = 8 ∨ lo f g a = 24 := by omega
        have hch : chr a x = 1 ∨ chr a x = -1 := sign_vals _
        rcases hvals with hv | hv | hv | hv <;> rcases hch with hch | hch <;>
          simp [hv, hch]
    have hsum := sum_mod3 _ _ hpt
    change (total 8 (fun a => transform zs a * chr a x) - transform (B s) x) % 3 = 0 at hsum
    rw [hinv] at hsum
    change (256 * zs x - transform (B s) x) % 3 = 0 at hsum
    omega
  have hmod_1 (x : W 8) : (z1 x - j1 x) % 3 = 0 := hmod3_sec 1 z1 htr_z1 (by decide) x
  have hmod_2 (x : W 8) : (z2 x - j2 x) % 3 = 0 := hmod3_sec 2 z2 htr_z2 (by decide) x
  have hmod_3 (x : W 8) : (z3 x - j3 x) % 3 = 0 := hmod3_sec 3 z3 htr_z3 (by decide) x
  have hpt_rec (x : W 8) : ∃ off : Int, (off = 0 ∨ off = 1 ∨ off = 2) ∧
      M x = cellRowOfJ (j1 x) (j2 x) (j3 x) off ∧
      emp x = isEmptyOfJ (j1 x) (j2 x) (j3 x) off := by
    let off := z0 x % 3
    have hoff : off = 0 ∨ off = 1 ∨ off = 2 := by dsimp only [off]; omega
    have hm1 := hmod_1 x; have hm2 := hmod_2 x; have hm3 := hmod_3 x
    have hv0_eq : v0 x = mods3 (j1 x + j2 x + j3 x + off) :=
      mods3_eq_of_ternary (v0 x) _ (hV_vals x) (by dsimp only [z0, z1, z2, z3, off] at hm1 hm2 hm3 ⊢; omega)
    have hv1_eq : v1 x = mods3 (-j1 x + j2 x - j3 x + off) :=
      mods3_eq_of_ternary (v1 x) _ (hV_vals _) (by dsimp only [z0, z1, z2, z3, off] at hm1 hm2 hm3 ⊢; omega)
    have hv2_eq : v2 x = mods3 (j1 x - j2 x - j3 x + off) :=
      mods3_eq_of_ternary (v2 x) _ (hV_vals _) (by dsimp only [z0, z1, z2, z3, off] at hm1 hm2 hm3 ⊢; omega)
    have hv3_eq : v3 x = mods3 (-j1 x - j2 x + j3 x + off) :=
      mods3_eq_of_ternary (v3 x) _ (hV_vals _) (by dsimp only [z0, z1, z2, z3, off] at hm1 hm2 hm3 ⊢; omega)
    refine ⟨off, hoff, ?_, ?_⟩
    · dsimp only [M, cellRowOfJ, cellValsOfJ, z0, z1, z2, z3]
      rw [hv0_eq, hv1_eq, hv2_eq, hv3_eq]
    · dsimp only [emp, isEmptyOfJ, cellValsOfJ]
      rw [hv0_eq, hv1_eq, hv2_eq, hv3_eq]
  -- (D) Exact totals of all 8 moments over `W 8`
  have hsec_size (s : Nat) (hs : s = 1 ∨ s = 2 ∨ s = 3) :
      total 8 (fun a => if secOf p q a == s then (1 : Int) else 0) = 64 := by
    have hsp : total 8 (fun a => sign (dot 8 a p)) = 0 := by
      have h := identity_spectrum 8 p
      have he : (fun a => sign (dot 8 a p)) = chr p := by funext a; simp [chr, dot_comm 8 a p]
      rw [he]; change total 8 (chr p) = _ at h; rw [h]; simp [hp]
    have hsq : total 8 (fun a => sign (dot 8 a q)) = 0 := by
      have h := identity_spectrum 8 q
      have he : (fun a => sign (dot 8 a q)) = chr q := by funext a; simp [chr, dot_comm 8 a q]
      rw [he]; change total 8 (chr q) = _ at h; rw [h]; simp [hq]
    have hsr : total 8 (fun a => sign (dot 8 a (add 8 p q))) = 0 := by
      have hr : add 8 p q ≠ zero 8 := fun h => hpq (by
        have h2 := congrArg (add 8 p) h; rw [add_cancel_l, add_zero_right] at h2; exact h2.symm)
      have h := identity_spectrum 8 (add 8 p q)
      have he : (fun a => sign (dot 8 a (add 8 p q))) = chr (add 8 p q) := by
        funext a; simp [chr, dot_comm 8 a (add 8 p q)]
      rw [he]; change total 8 (chr (add 8 p q)) = _ at h; rw [h]; simp [hr]
    rcases hs with rfl | rfl | rfl
    · have hpt (a : W 8) : 4 * (if secOf p q a == 1 then (1 : Int) else 0) =
          1 - sign (dot 8 a p) + sign (dot 8 a q) - sign (dot 8 a (add 8 p q)) := by
        unfold secOf; rw [dot_right]; cases dot 8 a p <;> cases dot 8 a q <;> decide
      have ht4 := congrArg (total 8) (funext hpt)
      simp only [total_scale, total_add, total_sub, total_const, hsp, hsq, hsr] at ht4
      change 4 * _ = 256 * 1 - 0 + 0 - 0 at ht4; omega
    · have hpt (a : W 8) : 4 * (if secOf p q a == 2 then (1 : Int) else 0) =
          1 + sign (dot 8 a p) - sign (dot 8 a q) - sign (dot 8 a (add 8 p q)) := by
        unfold secOf; rw [dot_right]; cases dot 8 a p <;> cases dot 8 a q <;> decide
      have ht4 := congrArg (total 8) (funext hpt)
      simp only [total_scale, total_add, total_sub, total_const, hsp, hsq, hsr] at ht4
      change 4 * _ = 256 * 1 + 0 - 0 - 0 at ht4; omega
    · have hpt (a : W 8) : 4 * (if secOf p q a == 3 then (1 : Int) else 0) =
          1 - sign (dot 8 a p) - sign (dot 8 a q) + sign (dot 8 a (add 8 p q)) := by
        unfold secOf; rw [dot_right]; cases dot 8 a p <;> cases dot 8 a q <;> decide
      have ht4 := congrArg (total 8) (funext hpt)
      simp only [total_scale, total_add, total_sub, total_const, hsp, hsq, hsr] at ht4
      change 4 * _ = 256 * 1 - 0 - 0 + 0 at ht4; omega
  have htot_m0 : total 8 (fun x => v0 x * v0 x + v1 x * v1 x + v2 x * v2 x + v3 x * v3 x) = 4 * 118 := by
    simp only [total_add, v0, v1, v2, v3]
    rw [sum_shift 8 p (fun x => V x * V x), sum_shift 8 q (fun x => V x * V x),
        sum_shift 8 (add 8 p q) (fun x => V x * V x)]
    have hVsq : total 8 (fun x => V x * V x) = agreements f g := by
      unfold agreements countPair V Vtbl
      rw [← total_add]; apply congrArg (total 8); funext x
      cases f x <;> cases g x <;> simp [sign, sameBit]
    omega
  have htot_zsq (s : Nat) (zs : W 8 → Int) (hs : s = 1 ∨ s = 2 ∨ s = 3)
      (htrz : ∀ a, transform zs a = if secOf p q a == s then 2 * lo f g a else 0) :
      total 8 (fun x => zs x * zs x) = 4 * (144 - 2 * secCount f g p q s) := by
    have hpar := parsevalInt 8 zs
    change total 8 (fun a => transform zs a * transform zs a) = 256 * total 8 (fun x => zs x * zs x) at hpar
    have hpt (a : W 8) : transform zs a * transform zs a =
        2304 * (if secOf p q a == s then (1 : Int) else 0) -
        2048 * (if secOf p q a == s && decide ((lo f g a).natAbs = 8) then (1 : Int) else 0) := by
      rw [htrz a]
      cases hsec : secOf p q a == s with
      | false => simp
      | true =>
        have hnz : lo f g a % 16 ≠ 0 := by
          intro h16; have ⟨h1, h2⟩ := (hZ a).1 h16
          have : secOf p q a = 0 := by simp [secOf, h1, h2]
          rw [this] at hsec; simp only [beq_iff_eq] at hsec; rcases hs with rfl | rfl | rfl <;> omega
        have hr := lores a; have hc := locap a
        have hvals : lo f g a = -24 ∨ lo f g a = -8 ∨ lo f g a = 8 ∨ lo f g a = 24 := by omega
        rcases hvals with hv | hv | hv | hv <;> simp [hv]
    rw [funext hpt, total_sub, total_scale, total_scale, hsec_size s hs] at hpar
    change 2304 * 64 - 2048 * secCount f g p q s = 256 * total 8 (fun x => zs x * zs x) at hpar
    omega
  have htot_zj (s : Nat) (zs : W 8 → Int)
      (htrz : ∀ a, transform zs a = if secOf p q a == s then 2 * lo f g a else 0) :
      total 8 (fun x => zs x * transform (B s) x) = 4 * (4 * secCount f g p q s) := by
    rw [duality_w8 zs (B s)]
    have hpt (a : W 8) : B s a * transform zs a =
        16 * (if secOf p q a == s && decide ((lo f g a).natAbs = 8) then (1 : Int) else 0) := by
      rw [htrz a]; dsimp only [B]
      cases hsec : secOf p q a == s with
      | false => simp
      | true =>
        by_cases h8 : (lo f g a).natAbs = 8
        · have hv : lo f g a = 8 ∨ lo f g a = -8 := by omega
          rcases hv with hv | hv <;> simp [hv]
        · simp [h8]
    rw [funext hpt, total_scale]
    change 16 * secCount f g p q s = 4 * (4 * secCount f g p q s); omega
  have htot_z0 : total 8 z0 = 0 := by
    unfold z0 v0 v1 v2 v3
    simp only [total_add, sum_shift]
    have hVsum : total 8 V = 0 := by
      have h0 := lo_eq_2_transform_V f g (zero 8)
      rw [dc] at h0
      have ht0 : transform V (zero 8) = total 8 V := by
        unfold transform; apply congrArg (total 8); funext x; simp [chr, dot_zero, sign]
      rw [ht0] at h0; omega
    omega
  have hM_tot (w : CellRow) : total 8 (fun x => dot8 w (M x)) = 4 * dot8 w target := by
    dsimp only [dot8, M, target]
    simp only [total_add, total_scale, htot_m0,
      htot_zsq 1 z1 (Or.inl rfl) htr_z1,
      htot_zsq 2 z2 (Or.inr (Or.inl rfl)) htr_z2,
      htot_zsq 3 z3 (Or.inr (Or.inr rfl)) htr_z3,
      htot_zj 1 z1 htr_z1, htot_zj 2 z2 htr_z2, htot_zj 3 z3 htr_z3, htot_z0]
    have h4 (a b : Int) : a * (4 * b) = 4 * (a * b) := by ac_rfl
    simp only [h4]
    omega
  -- (E) `4 ∣ total 8 emp` using any `r1` in sector 1 and `r2` in sector 2
  have hemp_div4 : ∃ N : Int, total 8 emp = 4 * N := by
    have hr1_pos : 0 < total 8 (fun a => if secOf p q a == 1 then (1 : Int) else 0) := by
      rw [hsec_size 1 (Or.inl rfl)]; decide
    have hr2_pos : 0 < total 8 (fun a => if secOf p q a == 2 then (1 : Int) else 0) := by
      rw [hsec_size 2 (Or.inr (Or.inl rfl))]; decide
    obtain ⟨r1, hr1⟩ := total_pos_exists _ hr1_pos
    obtain ⟨r2, hr2⟩ := total_pos_exists _ hr2_pos
    simp only [beq_iff_eq, secOf] at hr1 hr2
    have h1p : dot 8 r1 p = true := by
      cases h : dot 8 r1 p <;> cases h' : dot 8 r1 q <;> rw [h, h'] at hr1 <;> first | rfl | exact absurd hr1 (by decide)
    have h1q : dot 8 r1 q = false := by
      cases h : dot 8 r1 p <;> cases h' : dot 8 r1 q <;> rw [h, h'] at hr1 <;> first | rfl | exact absurd hr1 (by decide)
    have h2p : dot 8 r2 p = false := by
      cases h : dot 8 r2 p <;> cases h' : dot 8 r2 q <;> rw [h, h'] at hr2 <;> first | rfl | exact absurd hr2 (by decide)
    have h2q : dot 8 r2 q = true := by
      cases h : dot 8 r2 p <;> cases h' : dot 8 r2 q <;> rw [h, h'] at hr2 <;> first | rfl | exact absurd hr2 (by decide)
    let N := total 8 (fun x => if !dot 8 x r1 && !dot 8 x r2 then emp x else 0)
    refine ⟨N, ?_⟩
    have hshift_ind (d : W 8) (b1 b2 : Bool)
        (hd1 : dot 8 d r1 = b1) (hd2 : dot 8 d r2 = b2) (hemp_d : ∀ x, emp (add 8 d x) = emp x) :
        total 8 (fun x => if dot 8 x r1 == b1 && dot 8 x r2 == b2 then emp x else 0) = N := by
      rw [← sum_shift 8 d (fun x => if dot 8 x r1 == b1 && dot 8 x r2 == b2 then emp x else 0)]
      dsimp only [N]; apply congrArg (total 8); funext x
      rw [hemp_d x, dot_add_l, dot_add_l, hd1, hd2]
      cases b1 <;> cases b2 <;> cases dot 8 x r1 <;> cases dot 8 x r2 <;> simp
    have h00 : total 8 (fun x => if dot 8 x r1 == false && dot 8 x r2 == false then emp x else 0) = N := by
      dsimp only [N]; apply congrArg (total 8); funext x; cases dot 8 x r1 <;> cases dot 8 x r2 <;> simp
    have h10 := hshift_ind p true false (by rw [dot_comm]; exact h1p) (by rw [dot_comm]; exact h2p)
      (fun x => (hinv_pq x).2.2.1)
    have h01 := hshift_ind q false true (by rw [dot_comm]; exact h1q) (by rw [dot_comm]; exact h2q)
      (fun x => (hinv_pq x).2.2.2)
    have h11 := hshift_ind (add 8 p q) true true
      (by rw [dot_add_l, dot_comm 8 p r1, dot_comm 8 q r1, h1p, h1q]; rfl)
      (by rw [dot_add_l, dot_comm 8 p r2, dot_comm 8 q r2, h2p, h2q]; rfl)
      (fun x => by rw [add_assoc_w, (hinv_pq _).2.2.1, (hinv_pq x).2.2.2])
    have hpart : total 8 emp =
        total 8 (fun x => if dot 8 x r1 == false && dot 8 x r2 == false then emp x else 0) +
        total 8 (fun x => if dot 8 x r1 == true && dot 8 x r2 == false then emp x else 0) +
        total 8 (fun x => if dot 8 x r1 == false && dot 8 x r2 == true then emp x else 0) +
        total 8 (fun x => if dot 8 x r1 == true && dot 8 x r2 == true then emp x else 0) := by
      rw [← total_add, ← total_add, ← total_add]
      apply congrArg (total 8); funext x
      cases dot 8 x r1 <;> cases dot 8 x r2 <;> simp
    rw [hpart, h00, h10, h01, h11]; omega
  exact ⟨hinv_pq, hpt_rec, hM_tot, hemp_div4⟩

/-! ## Section 6: Pivot Elimination for All 4 Triples & Main Unconditional Theorem `no_t118` -/

/-- Extract the exact `Nodup` list of magnitude-8 low masks in sector `s`. -/
private def secList (f g : Half) (p q : W 8) (s : Nat) : List (W 8) :=
  (worlds 8).filter (fun a => secOf p q a == s && decide ((lo f g a).natAbs = 8))

private theorem secList_spec (f g : Half) (p q : W 8) (s : Nat) :
    (secList f g p q s).Nodup ∧
    ((secList f g p q s).length : Int) = secCount f g p q s ∧
    (∀ a ∈ secList f g p q s, secOf p q a = s ∧ (lo f g a = 8 ∨ lo f g a = -8)) ∧
    (∀ x : W 8,
      transform (fun a => if secOf p q a == s && decide ((lo f g a).natAbs = 8) then lo f g a / 8 else 0) x =
      (secList f g p q s).foldl (fun acc a => acc + sign (xor (decide (lo f g a = -8)) (dot 8 a x))) 0) := by
  refine ⟨(worlds_nodup 8).filter _, ?_, ?_, ?_⟩
  · exact filter_worlds_length _
  · intro a ha
    rw [secList, List.mem_filter] at ha
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ha
    exact ⟨ha.2.1, by omega⟩
  · intro x
    unfold secList
    rw [filter_worlds_sum]
    unfold transform; apply congrArg (total 8); funext a; dsimp only
    cases h : (secOf p q a == s && decide ((lo f g a).natAbs = 8)) with
    | false => simp only [Bool.false_eq_true, if_false, Int.zero_mul]
    | true =>
      simp only [if_true]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      have hv : lo f g a = 8 ∨ lo f g a = -8 := by omega
      rw [chr, dot_comm 8 x a, signMul]
      rcases hv with hv | hv <;> cases dot 8 a x <;> simp [hv, sign]

private theorem mask_bit_shift (p q a : W 8) (eps b2 b3 : Bool) (x : W 8)
    (h1 : dot 8 a p = (secOf p q a == 1 || secOf p q a == 3))
    (h2 : dot 8 a q = (secOf p q a == 2 || secOf p q a == 3)) :
    let y := add 8 (if xor b3 b2 then p else zero 8) (add 8 (if b2 then q else zero 8) x)
    xor eps (dot 8 a y) =
      xor eps (xor (dot 8 a x)
        (if secOf p q a = 1 then xor b3 b2
         else if secOf p q a = 2 then b2
         else if secOf p q a = 3 then b3 else false)) := by
  dsimp only
  rw [dot_right, dot_right]
  have hd_if (b : Bool) (v : W 8) : dot 8 a (if b then v else zero 8) = (b && dot 8 a v) := by
    cases b <;> simp [dot_zero_right]
  rw [hd_if, hd_if, h1, h2]
  have hs : secOf p q a = 0 ∨ secOf p q a = 1 ∨ secOf p q a = 2 ∨ secOf p q a = 3 := by
    unfold secOf; cases dot 8 a p <;> cases dot 8 a q <;> decide
  rcases hs with h | h | h | h <;> rw [h] <;>
    cases eps <;> cases b2 <;> cases b3 <;> cases dot 8 a x <;> decide

private theorem secOf_dots (p q a : W 8) :
    dot 8 a p = (secOf p q a == 1 || secOf p q a == 3) ∧
    dot 8 a q = (secOf p q a == 2 || secOf p q a == 3) := by
  unfold secOf; cases dot 8 a p <;> cases dot 8 a q <;> decide

private theorem add4_mk (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) :
    add 4 (a0, (a1, (a2, (a3, ())))) (b0, (b1, (b2, (b3, ())))) =
      (xor a0 b0, (xor a1 b1, (xor a2 b2, (xor a3 b3, ())))) := rfl

private theorem add5_mk (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool) :
    add 5 (a0, (a1, (a2, (a3, (a4, ()))))) (b0, (b1, (b2, (b3, (b4, ()))))) =
      (xor a0 b0, (xor a1 b1, (xor a2 b2, (xor a3 b3, (xor a4 b4, ()))))) := rfl

private theorem add6_mk (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    add 6 (a0, (a1, (a2, (a3, (a4, (a5, ())))))) (b0, (b1, (b2, (b3, (b4, (b5, ())))))) =
      (xor a0 b0, (xor a1 b1, (xor a2 b2, (xor a3 b3, (xor a4 b4, (xor a5 b5, ())))))) := rfl

private theorem dot4_mk (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) :
    dot 4 (a0, (a1, (a2, (a3, ())))) (b0, (b1, (b2, (b3, ())))) =
      xor (a0 && b0) (xor (a1 && b1) (xor (a2 && b2) (xor (a3 && b3) false))) := rfl

private theorem dot5_mk (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool) :
    dot 5 (a0, (a1, (a2, (a3, (a4, ()))))) (b0, (b1, (b2, (b3, (b4, ()))))) =
      xor (a0 && b0) (xor (a1 && b1) (xor (a2 && b2) (xor (a3 && b3) (xor (a4 && b4) false)))) := rfl

private theorem dot6_mk (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    dot 6 (a0, (a1, (a2, (a3, (a4, (a5, ())))))) (b0, (b1, (b2, (b3, (b4, (b5, ())))))) =
      xor (a0 && b0) (xor (a1 && b1) (xor (a2 && b2) (xor (a3 && b3) (xor (a4 && b4) (xor (a5 && b5) false))))) := rfl

/-- **UNCONDITIONAL** low-block-only exclusion of `agreements f g = 118` for balanced 9-variable
    nonlinearity-242 halves `(f, g)`. Zero `CoveringRadius244`, zero `SectionEnum`, zero `hi`! -/
theorem no_t118 (f g : Half)
    (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0)
    (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (ht : agreements f g = 118) : False := by
  obtain ⟨p, q, hp, hq, hpq, hZ, hcases⟩ := extract_sorted_pq f g dc lores locap ht
  obtain ⟨hinv_pq, hpt_rec, hM_tot, hemp_div4⟩ :=
    cell_moments_package f g p q dc lores locap ht hZ hp hq hpq
  -- Abbreviate `M`, `emp`, `j1, j2, j3` from `cell_moments_package`
  let V := Vtbl f g
  let B (s : Nat) (a : W 8) : Int :=
    if secOf p q a == s && decide ((lo f g a).natAbs = 8) then lo f g a / 8 else 0
  let j1 (x : W 8) := transform (B 1) x
  let j2 (x : W 8) := transform (B 2) x
  let j3 (x : W 8) := transform (B 3) x
  let v0 (x : W 8) := V x
  let v1 (x : W 8) := V (add 8 p x)
  let v2 (x : W 8) := V (add 8 q x)
  let v3 (x : W 8) := V (add 8 (add 8 p q) x)
  let z0 (x : W 8) := v0 x + v1 x + v2 x + v3 x
  let z1 (x : W 8) := v0 x - v1 x + v2 x - v3 x
  let z2 (x : W 8) := v0 x + v1 x - v2 x - v3 x
  let z3 (x : W 8) := v0 x - v1 x - v2 x + v3 x
  let M (x : W 8) : CellRow :=
    (v0 x * v0 x + v1 x * v1 x + v2 x * v2 x + v3 x * v3 x,
     z1 x * z1 x, z2 x * z2 x, z3 x * z3 x,
     z1 x * j1 x, z2 x * j2 x, z3 x * j3 x, z0 x)
  let emp (x : W 8) : Int :=
    if v0 x = 0 && v1 x = 0 && v2 x = 0 && v3 x = 0 then 1 else 0
  -- Helper: coset shift `yOf piv2 piv3 x` preserves `M` and `emp`
  let eps (a : W 8) : Bool := decide (lo f g a = -8)
  let yOf (piv2 piv3 x : W 8) : W 8 :=
    let b2 := xor (eps piv2) (dot 8 piv2 x)
    let b3 := xor (eps piv3) (dot 8 piv3 x)
    add 8 (if xor b3 b2 then p else zero 8) (add 8 (if b2 then q else zero 8) x)
  have hy_inv (piv2 piv3 x : W 8) :
      M (yOf piv2 piv3 x) = M x ∧ emp (yOf piv2 piv3 x) = emp x := by
    dsimp only [yOf]
    cases xor (xor (eps piv3) (dot 8 piv3 x)) (xor (eps piv2) (dot 8 piv2 x)) <;>
    cases xor (eps piv2) (dot 8 piv2 x)
    · simp only [Bool.false_eq_true, if_false, add_zero_left]; exact ⟨trivial, trivial⟩
    · simp only [Bool.false_eq_true, if_false, if_true, add_zero_left]
      exact ⟨(hinv_pq x).2.1, (hinv_pq x).2.2.2⟩
    · simp only [Bool.false_eq_true, if_false, if_true, add_zero_left]
      exact ⟨(hinv_pq x).1, (hinv_pq x).2.2.1⟩
    · simp only [if_true]
      exact ⟨((hinv_pq _).1).trans (hinv_pq x).2.1, ((hinv_pq _).2.2.1).trans (hinv_pq x).2.2.2⟩
  -- Bit formulas at `yOf piv2 piv3 x` for masks in sectors 1, 2, 3
  have hbit_s1 (piv2 piv3 a x : W 8) (ha : secOf p q a = 1) :
      xor (eps a) (dot 8 a (yOf piv2 piv3 x)) =
        xor (xor (eps a) (xor (eps piv3) (eps piv2)))
            (dot 8 (add 8 a (add 8 piv3 piv2)) x) := by
    dsimp only [yOf]
    rw [mask_bit_shift p q a (eps a) _ _ x (secOf_dots p q a).1 (secOf_dots p q a).2, ha]
    simp only [if_true, dot_add_l]
    cases eps a <;> cases eps piv2 <;> cases eps piv3 <;>
      cases dot 8 a x <;> cases dot 8 piv2 x <;> cases dot 8 piv3 x <;> decide
  have hbit_s2 (piv2 piv3 a x : W 8) (ha : secOf p q a = 2) :
      xor (eps a) (dot 8 a (yOf piv2 piv3 x)) =
        xor (xor (eps a) (eps piv2)) (dot 8 (add 8 a piv2) x) := by
    dsimp only [yOf]
    rw [mask_bit_shift p q a (eps a) _ _ x (secOf_dots p q a).1 (secOf_dots p q a).2, ha]
    simp only [show (2 : Nat) ≠ 1 by decide, if_false, if_true, dot_add_l]
    cases eps a <;> cases eps piv2 <;> cases dot 8 a x <;> cases dot 8 piv2 x <;> decide
  have hbit_s3 (piv2 piv3 a x : W 8) (ha : secOf p q a = 3) :
      xor (eps a) (dot 8 a (yOf piv2 piv3 x)) =
        xor (xor (eps a) (eps piv3)) (dot 8 (add 8 a piv3) x) := by
    dsimp only [yOf]
    rw [mask_bit_shift p q a (eps a) _ _ x (secOf_dots p q a).1 (secOf_dots p q a).2, ha]
    simp only [show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, if_false, if_true, dot_add_l]
    cases eps a <;> cases eps piv3 <;> cases dot 8 a x <;> cases dot 8 piv3 x <;> decide
  have hbit_piv2 (piv2 piv3 x : W 8) (h2 : secOf p q piv2 = 2) :
      xor (eps piv2) (dot 8 piv2 (yOf piv2 piv3 x)) = false := by
    rw [hbit_s2 piv2 piv3 piv2 x h2, add_self, Bool.xor_self, dot_zero]; rfl
  have hbit_piv3 (piv2 piv3 x : W 8) (h3 : secOf p q piv3 = 3) :
      xor (eps piv3) (dot 8 piv3 (yOf piv2 piv3 x)) = false := by
    rw [hbit_s3 piv2 piv3 piv3 x h3, add_self, Bool.xor_self, dot_zero]; rfl
  have hne_add (a b : W 8) (hab : a ≠ b) : add 8 a b ≠ zero 8 := fun h => hab (by
    have h2 := congrArg (add 8 a) h; rw [add_cancel_l, add_zero_right] at h2; exact h2.symm)
  obtain ⟨hnd1, hlen1, hmem1, hj1_eq⟩ := secList_spec f g p q 1
  obtain ⟨hnd2, hlen2, hmem2, hj2_eq⟩ := secList_spec f g p q 2
  obtain ⟨hnd3, hlen3, hmem3, hj3_eq⟩ := secList_spec f g p q 3
  -- Split into the 4 admissible sorted triples `(c1, c2, c3)`
  rcases hcases with ⟨hc1, hc2, hc3⟩ | ⟨hc1, hc2, hc3⟩ | ⟨hc1, hc2, hc3⟩ | ⟨hc1, hc2, hc3⟩
  · -- Case 1: (2, 2, 2)
    have hl1 : (secList f g p q 1).length = 2 := by omega
    have hl2 : (secList f g p q 2).length = 2 := by omega
    have hl3 : (secList f g p q 3).length = 2 := by omega
    rcases hL1 : secList f g p q 1 with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩ <;> simp [hL1] at hl1
    rcases hL2 : secList f g p q 2 with _ | ⟨b0, _ | ⟨piv2, _ | _⟩⟩ <;> simp [hL2] at hl2
    rcases hL3 : secList f g p q 3 with _ | ⟨c0, _ | ⟨piv3, _ | _⟩⟩ <;> simp [hL3] at hl3
    rw [hL1] at hnd1 hmem1 hj1_eq; rw [hL2] at hnd2 hmem2 hj2_eq; rw [hL3] at hnd3 hmem3 hj3_eq
    have ha01 : a0 ≠ a1 := by simp at hnd1; exact hnd1
    have hb0p : b0 ≠ piv2 := by simp at hnd2; exact hnd2
    have hc0p : c0 ≠ piv3 := by simp at hnd3; exact hnd3
    have hs_a0 := (hmem1 a0 (by simp)).1; have hs_a1 := (hmem1 a1 (by simp)).1
    have hs_b0 := (hmem2 b0 (by simp)).1; have hs_p2 := (hmem2 piv2 (by simp)).1
    have hs_c0 := (hmem3 c0 (by simp)).1; have hs_p3 := (hmem3 piv3 (by simp)).1
    let d0 := add 8 a0 (add 8 piv3 piv2)
    let d1 := add 8 a1 (add 8 piv3 piv2)
    let d2 := add 8 b0 piv2
    let d3 := add 8 c0 piv3
    let L : W 8 → W 4 := fun x => (dot 8 d0 x, (dot 8 d1 x, (dot 8 d2 x, (dot 8 d3 x, ()))))
    let shift : W 4 :=
      (xor (eps a0) (xor (eps piv3) (eps piv2)),
      (xor (eps a1) (xor (eps piv3) (eps piv2)),
      (xor (eps b0) (eps piv2),
      (xor (eps c0) (eps piv3), ()))))
    have hL_add : ∀ x y, L (add 8 x y) = add 4 (L x) (L y) := by
      intro x y; dsimp only [L]; rw [add4_mk, dot_right, dot_right, dot_right, dot_right]
    have hdiffs : ∀ d ∈ diffs222, ∃ x : W 8, dot 4 d (L x) = true := by
      intro d hd; simp only [diffs222, List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · have hne : add 8 d0 d1 ≠ zero 8 := by
          have : add 8 d0 d1 = add 8 a0 a1 := by
            dsimp only [d0, d1]; rw [add_assoc_w, add_comm 8 (add 8 piv3 piv2) (add 8 a1 _),
              add_assoc_w, add_self, add_zero_right]
          rw [this]; exact hne_add a0 a1 ha01
        obtain ⟨x, hx⟩ := exists_dot_true _ hne
        exact ⟨x, by dsimp only [L]; rw [dot4_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d2 (hne_add b0 piv2 hb0p)
        exact ⟨x, by dsimp only [L]; rw [dot4_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d3 (hne_add c0 piv3 hc0p)
        exact ⟨x, by dsimp only [L]; rw [dot4_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
    have htarget_eq : target222 = (118, 144 - 2 * secCount f g p q 1, 144 - 2 * secCount f g p q 2,
        144 - 2 * secCount f g p q 3, 4 * secCount f g p q 1, 4 * secCount f g p q 2,
        4 * secCount f g p q 3, 0) := by
      rw [hc1, hc2, hc3]; rfl
    apply refute_from_check (by decide) j222 diffs222 cutCerts_222 none target222
      trees_222_ok check_222_ok L hL_add shift hdiffs M emp
    · intro w; rw [htarget_eq]; exact hM_tot w
    · exact hemp_div4
    · intro x
      let y := yOf piv2 piv3 x
      obtain ⟨off, hoff, hMy, hey⟩ := hpt_rec y
      refine ⟨off, hoff, ?_⟩
      have hj_match : (j1 y, j2 y, j3 y) = j222 (add 4 shift (L x)) := by
        have h1 : j1 y = sign (xor (eps a0) (dot 8 a0 y)) + sign (xor (eps a1) (dot 8 a1 y)) := by
          change transform (B 1) y = _; rw [hj1_eq y]; simp [List.foldl, eps]
        have h2 : j2 y = sign (xor (eps b0) (dot 8 b0 y)) + sign (xor (eps piv2) (dot 8 piv2 y)) := by
          change transform (B 2) y = _; rw [hj2_eq y]; simp [List.foldl, eps]
        have h3 : j3 y = sign (xor (eps c0) (dot 8 c0 y)) + sign (xor (eps piv3) (dot 8 piv3 y)) := by
          change transform (B 3) y = _; rw [hj3_eq y]; simp [List.foldl, eps]
        rw [h1, h2, h3,
            hbit_s1 piv2 piv3 a0 x hs_a0, hbit_s1 piv2 piv3 a1 x hs_a1,
            hbit_s2 piv2 piv3 b0 x hs_b0, hbit_piv2 piv2 piv3 x hs_p2,
            hbit_s3 piv2 piv3 c0 x hs_c0, hbit_piv3 piv2 piv3 x hs_p3]
        rfl
      rw [← (hy_inv piv2 piv3 x).1, ← (hy_inv piv2 piv3 x).2]
      have he1 : (j222 (add 4 shift (L x))).1 = j1 y := (congrArg Prod.fst hj_match).symm
      have he2 : (j222 (add 4 shift (L x))).2.1 = j2 y := (congrArg (fun t => t.2.1) hj_match).symm
      have he3 : (j222 (add 4 shift (L x))).2.2 = j3 y := (congrArg (fun t => t.2.2) hj_match).symm
      dsimp only; rw [he1, he2, he3]; exact ⟨hMy, hey⟩

  · -- Case 2: (1, 3, 3)
    have hl1 : (secList f g p q 1).length = 1 := by omega
    have hl2 : (secList f g p q 2).length = 3 := by omega
    have hl3 : (secList f g p q 3).length = 3 := by omega
    rcases hL1 : secList f g p q 1 with _ | ⟨a0, _ | _⟩ <;> simp [hL1] at hl1
    rcases hL2 : secList f g p q 2 with _ | ⟨b0, _ | ⟨b1, _ | ⟨piv2, _ | _⟩⟩⟩ <;> simp [hL2] at hl2
    rcases hL3 : secList f g p q 3 with _ | ⟨c0, _ | ⟨c1, _ | ⟨piv3, _ | _⟩⟩⟩ <;> simp [hL3] at hl3
    rw [hL1] at hnd1 hmem1 hj1_eq; rw [hL2] at hnd2 hmem2 hj2_eq; rw [hL3] at hnd3 hmem3 hj3_eq
    simp at hnd2 hnd3
    obtain ⟨⟨hb01, hb0p⟩, hb1p⟩ := hnd2
    obtain ⟨⟨hc01, hc0p⟩, hc1p⟩ := hnd3
    have hs_a0 := (hmem1 a0 (by simp)).1
    have hs_b0 := (hmem2 b0 (by simp)).1; have hs_b1 := (hmem2 b1 (by simp)).1; have hs_p2 := (hmem2 piv2 (by simp)).1
    have hs_c0 := (hmem3 c0 (by simp)).1; have hs_c1 := (hmem3 c1 (by simp)).1; have hs_p3 := (hmem3 piv3 (by simp)).1
    let d0 := add 8 a0 (add 8 piv3 piv2)
    let d1 := add 8 b0 piv2; let d2 := add 8 b1 piv2
    let d3 := add 8 c0 piv3; let d4 := add 8 c1 piv3
    let L : W 8 → W 5 := fun x => (dot 8 d0 x, (dot 8 d1 x, (dot 8 d2 x, (dot 8 d3 x, (dot 8 d4 x, ())))))
    let shift : W 5 :=
      (xor (eps a0) (xor (eps piv3) (eps piv2)),
      (xor (eps b0) (eps piv2),
      (xor (eps b1) (eps piv2),
      (xor (eps c0) (eps piv3),
      (xor (eps c1) (eps piv3), ())))))
    have hL_add : ∀ x y, L (add 8 x y) = add 5 (L x) (L y) := by
      intro x y; dsimp only [L]; rw [add5_mk, dot_right, dot_right, dot_right, dot_right, dot_right]
    have hdiffs : ∀ d ∈ diffs133, ∃ x : W 8, dot 5 d (L x) = true := by
      intro d hd; simp only [diffs133, List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨x, hx⟩ := exists_dot_true d1 (hne_add b0 piv2 hb0p)
        exact ⟨x, by dsimp only [L]; rw [dot5_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d2 (hne_add b1 piv2 hb1p)
        exact ⟨x, by dsimp only [L]; rw [dot5_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · have hne : add 8 d1 d2 ≠ zero 8 := by
          have : add 8 d1 d2 = add 8 b0 b1 := by
            dsimp only [d1, d2]; rw [add_assoc_w, add_comm 8 piv2 (add 8 b1 piv2), add_assoc_w, add_self, add_zero_right]
          rw [this]; exact hne_add b0 b1 hb01
        obtain ⟨x, hx⟩ := exists_dot_true _ hne
        exact ⟨x, by dsimp only [L]; rw [dot5_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d3 (hne_add c0 piv3 hc0p)
        exact ⟨x, by dsimp only [L]; rw [dot5_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d4 (hne_add c1 piv3 hc1p)
        exact ⟨x, by dsimp only [L]; rw [dot5_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · have hne : add 8 d3 d4 ≠ zero 8 := by
          have : add 8 d3 d4 = add 8 c0 c1 := by
            dsimp only [d3, d4]; rw [add_assoc_w, add_comm 8 piv3 (add 8 c1 piv3), add_assoc_w, add_self, add_zero_right]
          rw [this]; exact hne_add c0 c1 hc01
        obtain ⟨x, hx⟩ := exists_dot_true _ hne
        exact ⟨x, by dsimp only [L]; rw [dot5_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
    have htarget_eq : target133 = (118, 144 - 2 * secCount f g p q 1, 144 - 2 * secCount f g p q 2,
        144 - 2 * secCount f g p q 3, 4 * secCount f g p q 1, 4 * secCount f g p q 2,
        4 * secCount f g p q 3, 0) := by
      rw [hc1, hc2, hc3]; rfl
    apply refute_from_check (by decide) j133 diffs133 cutCerts_133 none target133
      trees_133_ok check_133_ok L hL_add shift hdiffs M emp
    · intro w; rw [htarget_eq]; exact hM_tot w
    · exact hemp_div4
    · intro x
      let y := yOf piv2 piv3 x
      obtain ⟨off, hoff, hMy, hey⟩ := hpt_rec y
      refine ⟨off, hoff, ?_⟩
      have hj_match : (j1 y, j2 y, j3 y) = j133 (add 5 shift (L x)) := by
        have h1 : j1 y = sign (xor (eps a0) (dot 8 a0 y)) := by
          change transform (B 1) y = _; rw [hj1_eq y]; simp [List.foldl, eps]
        have h2 : j2 y = sign (xor (eps b0) (dot 8 b0 y)) + sign (xor (eps b1) (dot 8 b1 y)) +
            sign (xor (eps piv2) (dot 8 piv2 y)) := by
          change transform (B 2) y = _; rw [hj2_eq y]; simp [List.foldl, eps]
        have h3 : j3 y = sign (xor (eps c0) (dot 8 c0 y)) + sign (xor (eps c1) (dot 8 c1 y)) +
            sign (xor (eps piv3) (dot 8 piv3 y)) := by
          change transform (B 3) y = _; rw [hj3_eq y]; simp [List.foldl, eps]
        rw [h1, h2, h3,
            hbit_s1 piv2 piv3 a0 x hs_a0,
            hbit_s2 piv2 piv3 b0 x hs_b0, hbit_s2 piv2 piv3 b1 x hs_b1, hbit_piv2 piv2 piv3 x hs_p2,
            hbit_s3 piv2 piv3 c0 x hs_c0, hbit_s3 piv2 piv3 c1 x hs_c1, hbit_piv3 piv2 piv3 x hs_p3]
        rfl
      rw [← (hy_inv piv2 piv3 x).1, ← (hy_inv piv2 piv3 x).2]
      have he1 : (j133 (add 5 shift (L x))).1 = j1 y := (congrArg Prod.fst hj_match).symm
      have he2 : (j133 (add 5 shift (L x))).2.1 = j2 y := (congrArg (fun t => t.2.1) hj_match).symm
      have he3 : (j133 (add 5 shift (L x))).2.2 = j3 y := (congrArg (fun t => t.2.2) hj_match).symm
      dsimp only; rw [he1, he2, he3]; exact ⟨hMy, hey⟩

  · -- Case 3: (0, 4, 4)
    have hl1 : (secList f g p q 1).length = 0 := by omega
    have hl2 : (secList f g p q 2).length = 4 := by omega
    have hl3 : (secList f g p q 3).length = 4 := by omega
    rcases hL1 : secList f g p q 1 with _ | _ <;> simp [hL1] at hl1
    rcases hL2 : secList f g p q 2 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨piv2, _ | _⟩⟩⟩⟩ <;> simp [hL2] at hl2
    rcases hL3 : secList f g p q 3 with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨piv3, _ | _⟩⟩⟩⟩ <;> simp [hL3] at hl3
    rw [hL1] at hnd1 hmem1 hj1_eq; rw [hL2] at hnd2 hmem2 hj2_eq; rw [hL3] at hnd3 hmem3 hj3_eq
    simp at hnd2 hnd3
    obtain ⟨⟨hb01, hb02, hb0p⟩, ⟨hb12, hb1p⟩, hb2p⟩ := hnd2
    obtain ⟨⟨hc01, hc02, hc0p⟩, ⟨hc12, hc1p⟩, hc2p⟩ := hnd3
    have hs_b0 := (hmem2 b0 (by simp)).1; have hs_b1 := (hmem2 b1 (by simp)).1
    have hs_b2 := (hmem2 b2 (by simp)).1; have hs_p2 := (hmem2 piv2 (by simp)).1
    have hs_c0 := (hmem3 c0 (by simp)).1; have hs_c1 := (hmem3 c1 (by simp)).1
    have hs_c2 := (hmem3 c2 (by simp)).1; have hs_p3 := (hmem3 piv3 (by simp)).1
    let d0 := add 8 b0 piv2; let d1 := add 8 b1 piv2; let d2 := add 8 b2 piv2
    let d3 := add 8 c0 piv3; let d4 := add 8 c1 piv3; let d5 := add 8 c2 piv3
    let L : W 8 → W 6 := fun x =>
      (dot 8 d0 x, (dot 8 d1 x, (dot 8 d2 x, (dot 8 d3 x, (dot 8 d4 x, (dot 8 d5 x, ()))))))
    let shift : W 6 :=
      (xor (eps b0) (eps piv2), (xor (eps b1) (eps piv2), (xor (eps b2) (eps piv2),
      (xor (eps c0) (eps piv3), (xor (eps c1) (eps piv3), (xor (eps c2) (eps piv3), ()))))))
    have hL_add : ∀ x y, L (add 8 x y) = add 6 (L x) (L y) := by
      intro x y; dsimp only [L]; rw [add6_mk, dot_right, dot_right, dot_right, dot_right, dot_right, dot_right]
    have cancel_piv (u v w : W 8) : add 8 (add 8 u w) (add 8 v w) = add 8 u v := by
      rw [add_assoc_w, add_comm 8 w (add 8 v w), add_assoc_w, add_self, add_zero_right]
    have hdiffs : ∀ d ∈ diffs044, ∃ x : W 8, dot 6 d (L x) = true := by
      intro d hd; simp only [diffs044, List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨x, hx⟩ := exists_dot_true d0 (hne_add b0 piv2 hb0p)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d1 (hne_add b1 piv2 hb1p)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d2 (hne_add b2 piv2 hb2p)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true (add 8 d0 d1) (by rw [cancel_piv]; exact hne_add b0 b1 hb01)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
      · obtain ⟨x, hx⟩ := exists_dot_true (add 8 d0 d2) (by rw [cancel_piv]; exact hne_add b0 b2 hb02)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
      · obtain ⟨x, hx⟩ := exists_dot_true (add 8 d1 d2) (by rw [cancel_piv]; exact hne_add b1 b2 hb12)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d3 (hne_add c0 piv3 hc0p)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d4 (hne_add c1 piv3 hc1p)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d5 (hne_add c2 piv3 hc2p)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true (add 8 d3 d4) (by rw [cancel_piv]; exact hne_add c0 c1 hc01)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
      · obtain ⟨x, hx⟩ := exists_dot_true (add 8 d3 d5) (by rw [cancel_piv]; exact hne_add c0 c2 hc02)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
      · obtain ⟨x, hx⟩ := exists_dot_true (add 8 d4 d5) (by rw [cancel_piv]; exact hne_add c1 c2 hc12)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
    have htarget_eq : target044 = (118, 144 - 2 * secCount f g p q 1, 144 - 2 * secCount f g p q 2,
        144 - 2 * secCount f g p q 3, 4 * secCount f g p q 1, 4 * secCount f g p q 2,
        4 * secCount f g p q 3, 0) := by
      rw [hc1, hc2, hc3]; rfl
    apply refute_from_check (by decide) j044 diffs044 cutCerts_044 (some intCert_044) target044
      trees_044_ok check_044_ok L hL_add shift hdiffs M emp
    · intro w; rw [htarget_eq]; exact hM_tot w
    · exact hemp_div4
    · intro x
      let y := yOf piv2 piv3 x
      obtain ⟨off, hoff, hMy, hey⟩ := hpt_rec y
      refine ⟨off, hoff, ?_⟩
      have hj_match : (j1 y, j2 y, j3 y) = j044 (add 6 shift (L x)) := by
        have h1 : j1 y = 0 := by change transform (B 1) y = _; rw [hj1_eq y]; rfl
        have h2 : j2 y = sign (xor (eps b0) (dot 8 b0 y)) + sign (xor (eps b1) (dot 8 b1 y)) +
            sign (xor (eps b2) (dot 8 b2 y)) + sign (xor (eps piv2) (dot 8 piv2 y)) := by
          change transform (B 2) y = _; rw [hj2_eq y]; simp [List.foldl, eps]
        have h3 : j3 y = sign (xor (eps c0) (dot 8 c0 y)) + sign (xor (eps c1) (dot 8 c1 y)) +
            sign (xor (eps c2) (dot 8 c2 y)) + sign (xor (eps piv3) (dot 8 piv3 y)) := by
          change transform (B 3) y = _; rw [hj3_eq y]; simp [List.foldl, eps]
        rw [h1, h2, h3,
            hbit_s2 piv2 piv3 b0 x hs_b0, hbit_s2 piv2 piv3 b1 x hs_b1,
            hbit_s2 piv2 piv3 b2 x hs_b2, hbit_piv2 piv2 piv3 x hs_p2,
            hbit_s3 piv2 piv3 c0 x hs_c0, hbit_s3 piv2 piv3 c1 x hs_c1,
            hbit_s3 piv2 piv3 c2 x hs_c2, hbit_piv3 piv2 piv3 x hs_p3]
        rfl
      rw [← (hy_inv piv2 piv3 x).1, ← (hy_inv piv2 piv3 x).2]
      have he1 : (j044 (add 6 shift (L x))).1 = j1 y := (congrArg Prod.fst hj_match).symm
      have he2 : (j044 (add 6 shift (L x))).2.1 = j2 y := (congrArg (fun t => t.2.1) hj_match).symm
      have he3 : (j044 (add 6 shift (L x))).2.2 = j3 y := (congrArg (fun t => t.2.2) hj_match).symm
      dsimp only; rw [he1, he2, he3]; exact ⟨hMy, hey⟩

  · -- Case 4: (2, 2, 4)
    have hl1 : (secList f g p q 1).length = 2 := by omega
    have hl2 : (secList f g p q 2).length = 2 := by omega
    have hl3 : (secList f g p q 3).length = 4 := by omega
    rcases hL1 : secList f g p q 1 with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩ <;> simp [hL1] at hl1
    rcases hL2 : secList f g p q 2 with _ | ⟨b0, _ | ⟨piv2, _ | _⟩⟩ <;> simp [hL2] at hl2
    rcases hL3 : secList f g p q 3 with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨piv3, _ | _⟩⟩⟩⟩ <;> simp [hL3] at hl3
    rw [hL1] at hnd1 hmem1 hj1_eq; rw [hL2] at hnd2 hmem2 hj2_eq; rw [hL3] at hnd3 hmem3 hj3_eq
    simp at hnd1 hnd2 hnd3
    have ha01 : a0 ≠ a1 := hnd1
    have hb0p : b0 ≠ piv2 := hnd2
    obtain ⟨⟨hc01, hc02, hc0p⟩, ⟨hc12, hc1p⟩, hc2p⟩ := hnd3
    have hs_a0 := (hmem1 a0 (by simp)).1; have hs_a1 := (hmem1 a1 (by simp)).1
    have hs_b0 := (hmem2 b0 (by simp)).1; have hs_p2 := (hmem2 piv2 (by simp)).1
    have hs_c0 := (hmem3 c0 (by simp)).1; have hs_c1 := (hmem3 c1 (by simp)).1
    have hs_c2 := (hmem3 c2 (by simp)).1; have hs_p3 := (hmem3 piv3 (by simp)).1
    let d0 := add 8 a0 (add 8 piv3 piv2); let d1 := add 8 a1 (add 8 piv3 piv2)
    let d2 := add 8 b0 piv2
    let d3 := add 8 c0 piv3; let d4 := add 8 c1 piv3; let d5 := add 8 c2 piv3
    let L : W 8 → W 6 := fun x =>
      (dot 8 d0 x, (dot 8 d1 x, (dot 8 d2 x, (dot 8 d3 x, (dot 8 d4 x, (dot 8 d5 x, ()))))))
    let shift : W 6 :=
      (xor (eps a0) (xor (eps piv3) (eps piv2)), (xor (eps a1) (xor (eps piv3) (eps piv2)),
      (xor (eps b0) (eps piv2),
      (xor (eps c0) (eps piv3), (xor (eps c1) (eps piv3), (xor (eps c2) (eps piv3), ()))))))
    have hL_add : ∀ x y, L (add 8 x y) = add 6 (L x) (L y) := by
      intro x y; dsimp only [L]; rw [add6_mk, dot_right, dot_right, dot_right, dot_right, dot_right, dot_right]
    have cancel_piv (u v w : W 8) : add 8 (add 8 u w) (add 8 v w) = add 8 u v := by
      rw [add_assoc_w, add_comm 8 w (add 8 v w), add_assoc_w, add_self, add_zero_right]
    have hdiffs : ∀ d ∈ diffs224, ∃ x : W 8, dot 6 d (L x) = true := by
      intro d hd; simp only [diffs224, List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨x, hx⟩ := exists_dot_true (add 8 d0 d1) (by rw [cancel_piv]; exact hne_add a0 a1 ha01)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d2 (hne_add b0 piv2 hb0p)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d3 (hne_add c0 piv3 hc0p)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d4 (hne_add c1 piv3 hc1p)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true d5 (hne_add c2 piv3 hc2p)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; exact hx⟩
      · obtain ⟨x, hx⟩ := exists_dot_true (add 8 d3 d4) (by rw [cancel_piv]; exact hne_add c0 c1 hc01)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
      · obtain ⟨x, hx⟩ := exists_dot_true (add 8 d3 d5) (by rw [cancel_piv]; exact hne_add c0 c2 hc02)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
      · obtain ⟨x, hx⟩ := exists_dot_true (add 8 d4 d5) (by rw [cancel_piv]; exact hne_add c1 c2 hc12)
        exact ⟨x, by dsimp only [L]; rw [dot6_mk]; simp only [Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false]; rwa [← dot_add_l]⟩
    have htarget_eq : target224 = (118, 144 - 2 * secCount f g p q 1, 144 - 2 * secCount f g p q 2,
        144 - 2 * secCount f g p q 3, 4 * secCount f g p q 1, 4 * secCount f g p q 2,
        4 * secCount f g p q 3, 0) := by
      rw [hc1, hc2, hc3]; rfl
    apply refute_from_check (by decide) j224 diffs224 cutCerts_224 none target224
      trees_224_ok check_224_ok L hL_add shift hdiffs M emp
    · intro w; rw [htarget_eq]; exact hM_tot w
    · exact hemp_div4
    · intro x
      let y := yOf piv2 piv3 x
      obtain ⟨off, hoff, hMy, hey⟩ := hpt_rec y
      refine ⟨off, hoff, ?_⟩
      have hj_match : (j1 y, j2 y, j3 y) = j224 (add 6 shift (L x)) := by
        have h1 : j1 y = sign (xor (eps a0) (dot 8 a0 y)) + sign (xor (eps a1) (dot 8 a1 y)) := by
          change transform (B 1) y = _; rw [hj1_eq y]; simp [List.foldl, eps]
        have h2 : j2 y = sign (xor (eps b0) (dot 8 b0 y)) + sign (xor (eps piv2) (dot 8 piv2 y)) := by
          change transform (B 2) y = _; rw [hj2_eq y]; simp [List.foldl, eps]
        have h3 : j3 y = sign (xor (eps c0) (dot 8 c0 y)) + sign (xor (eps c1) (dot 8 c1 y)) +
            sign (xor (eps c2) (dot 8 c2 y)) + sign (xor (eps piv3) (dot 8 piv3 y)) := by
          change transform (B 3) y = _; rw [hj3_eq y]; simp [List.foldl, eps]
        rw [h1, h2, h3,
            hbit_s1 piv2 piv3 a0 x hs_a0, hbit_s1 piv2 piv3 a1 x hs_a1,
            hbit_s2 piv2 piv3 b0 x hs_b0, hbit_piv2 piv2 piv3 x hs_p2,
            hbit_s3 piv2 piv3 c0 x hs_c0, hbit_s3 piv2 piv3 c1 x hs_c1,
            hbit_s3 piv2 piv3 c2 x hs_c2, hbit_piv3 piv2 piv3 x hs_p3]
        rfl
      rw [← (hy_inv piv2 piv3 x).1, ← (hy_inv piv2 piv3 x).2]
      have he1 : (j224 (add 6 shift (L x))).1 = j1 y := (congrArg Prod.fst hj_match).symm
      have he2 : (j224 (add 6 shift (L x))).2.1 = j2 y := (congrArg (fun t => t.2.1) hj_match).symm
      have he3 : (j224 (add 6 shift (L x))).2.2 = j3 y := (congrArg (fun t => t.2.2) hj_match).symm
      dsimp only; rw [he1, he2, he3]; exact ⟨hMy, hey⟩

#print axioms no_t118

end Balanced242T118
