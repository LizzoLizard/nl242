/-
  All-degree multivariate Krawtchouk identities, inequalities, and mod-2^n congruences
  for `W n`, matching `replay.py`'s exact `kraw(n, w, j)` (`comb` sum) definition:

    1. `sum_triple_esym`: for any three lists `L1 L2 L3 : List (W n)` and degrees `i j l : Nat`,
       `∑_{v ∈ W n} esym v L1 i * esym v L2 j * esym v L3 l` equals `2^n` times the count
       of triples `(S1, S2, S3)` of sublists of lengths `(i, j, l)` whose combined XOR is `0`.
    2. `kraw_triple_nonneg_and_mod`: for ALL `i j l : Nat` (degrees 0, 2, 4, 6, ...),
         `-choose a i * choose b j * choose c l ≤ ∑_{v ≠ 0} K_i K_j K_l`
       and
         `(∑_{v ≠ 0} K_i K_j K_l + choose a i * choose b j * choose c l) % (many n) = 0`.
       This simultaneously formalizes every MacWilliams/Delsarte LP row (`deg = 4, 6`) and
       every `mac` mod-`2^n` congruence in `replay.py` (`affine_system` and `conditional`).
    3. `kraw_triple_deg2_eq`: when `P, Q, R` are pairwise disjoint and `i + j + l = 2`,
         `∑_{v ≠ 0} K_i K_j K_l = -choose a i * choose b j * choose c l`.
    4. `kraw_even_flip`: for even `i + j + l`, `K_i(a, a - x) K_j(b, b - y) K_l(c, c - z) =
       K_i(a, x) K_j(b, y) K_l(c, z)`, justifying the unordered-half canonicalization `lo ≤ hi`
       in `replay.py`'s `splits` and `conditional`.
-/
import Balanced242Quartic

namespace Balanced242Krawtchouk
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Hyperplane Balanced242Plateau

/-- Nonzero indicator on `W n`: `0` at `zero n`, `1` elsewhere. -/
def nz {n : Nat} (v : W n) : Int := if v = zero n then 0 else 1

theorem nz_total {n : Nat} (F : W n → Int) :
    total n (fun v => nz v * F v) = total n F - F (zero n) := by
  have hs := select n (zero n) F
  have hpt (v : W n) : nz v * F v + hits (zero n) v * F v = F v := by
    unfold nz hits
    if h : v = zero n then
      subst h; simp
    else
      have h' : ¬ zero n = v := fun e => h e.symm
      simp [h, h']
  have hsum := congrArg (total n) (funext hpt)
  rw [total_add, hs] at hsum
  have hsub := congrArg (· - F (zero n)) hsum
  simpa [Int.add_sub_cancel] using hsub

/-! ## Binomial coefficients and exact Krawtchouk polynomials -/

/-- Exact integer binomial coefficient `C(n, k)`. -/
def choose : Nat → Nat → Int
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => choose n (k + 1) + choose n k

theorem choose_zero (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n (k + 1) + choose n k := rfl

theorem choose_gt : ∀ (n k : Nat), n < k → choose n k = 0
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | n + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [choose_succ_succ, choose_gt n (k + 1) (by omega), choose_gt n k (by omega)]; rfl

/-- Helper sum over `List Int`. -/
def sumInt : List Int → Int
  | [] => 0
  | a :: t => a + sumInt t

theorem sumInt_append : ∀ (A B : List Int), sumInt (A ++ B) = sumInt A + sumInt B
  | [], B => by simp [sumInt]
  | a :: t, B => by
    show a + sumInt (t ++ B) = a + sumInt t + sumInt B
    rw [sumInt_append t B]; omega

theorem sumInt_map_scale (c : Int) : ∀ (L : List Int),
    sumInt (L.map (fun x => c * x)) = c * sumInt L
  | [] => by simp [sumInt]
  | a :: t => by
    simp only [List.map_cons, sumInt, sumInt_map_scale c t, Int.mul_add]

theorem sumInt_map_add {α : Type} (f g : α → Int) : ∀ (L : List α),
    sumInt (L.map (fun x => f x + g x)) = sumInt (L.map f) + sumInt (L.map g)
  | [] => rfl
  | a :: t => by
    simp only [List.map_cons, sumInt, sumInt_map_add f g t]; omega

theorem sumInt_mul_sumInt {α β : Type} (L1 : List α) (L2 : List β) (f : α → Int) (g : β → Int) :
    sumInt (L1.map f) * sumInt (L2.map g) =
      sumInt (L1.map (fun x => sumInt (L2.map (fun y => f x * g y)))) := by
  induction L1 with
  | nil => simp [sumInt]
  | cons a t ih =>
    simp only [List.map_cons, sumInt, Int.add_mul, ih]
    congr 1
    rw [← sumInt_map_scale (f a), List.map_map]; rfl

theorem sumInt_nonneg : ∀ (L : List Int), (∀ x, x ∈ L → 0 ≤ x) → 0 ≤ sumInt L
  | [], _ => Int.le_refl 0
  | a :: t, h => by
    have ha : 0 ≤ a := h a (List.Mem.head _)
    have ht : 0 ≤ sumInt t := sumInt_nonneg t (fun x hx => h x (List.Mem.tail _ hx))
    unfold sumInt; omega

theorem sumInt_zero : ∀ (L : List Int), (∀ x, x ∈ L → x = 0) → sumInt L = 0
  | [], _ => rfl
  | a :: t, h => by
    have ha : a = 0 := h a (List.Mem.head _)
    have ht : sumInt t = 0 := sumInt_zero t (fun x hx => h x (List.Mem.tail _ hx))
    unfold sumInt; rw [ha, ht]; rfl

/-- Alternating sign `(-1)^r`. -/
def altSign (r : Nat) : Int := if r % 2 = 0 then 1 else -1

private theorem altSign_succ (k : Nat) : altSign (k + 1) = -altSign k := by
  unfold altSign
  if h : k % 2 = 0 then
    have h1 : (k + 1) % 2 = 1 := by omega
    simp [h, h1]
  else
    have h1 : (k + 1) % 2 = 0 := by omega
    simp [h, h1]

/-- Exact Krawtchouk polynomial `kraw(s, x, k) = ∑_{r=0}^k (-1)^r C(x, r) C(s - x, k - r)`
    (matching `replay.py`'s `kraw(n, w, j)` for `0 ≤ x ≤ s`). -/
def kraw (s x k : Nat) : Int :=
  sumInt ((List.range (k + 1)).map (fun r => altSign r * choose x r * choose (s - x) (k - r)))

/-- Pure negative-weight Krawtchouk `krawNeg m k = (-1)^k C(m, k)` (structurally recursive on `m`). -/
def krawNeg : Nat → Nat → Int
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | m + 1, k + 1 => krawNeg m (k + 1) - krawNeg m k

/-- Recursive form `krawRec p m k` for `p` `+1`-weights and `m` `-1`-weights (`s = p + m`, `x = m`),
    structurally recursive on `p`. -/
def krawRec : Nat → Nat → Nat → Int
  | 0, m, k => krawNeg m k
  | _ + 1, _, 0 => 1
  | p + 1, m, k + 1 => krawRec p m (k + 1) + krawRec p m k

theorem krawRec_zero (p m : Nat) : krawRec p m 0 = 1 := by
  cases p <;> cases m <;> rfl

theorem krawRec_pos_succ (p m k : Nat) :
    krawRec (p + 1) m (k + 1) = krawRec p m (k + 1) + krawRec p m k := rfl

private theorem krawRec_neg_succ : ∀ (p m k : Nat),
    krawRec p (m + 1) (k + 1) = krawRec p m (k + 1) - krawRec p m k
  | 0, _, _ => rfl
  | p + 1, m, 0 => by
    simp only [krawRec_pos_succ, krawRec_neg_succ p m 0, krawRec_zero]; omega
  | p + 1, m, k + 1 => by
    rw [krawRec_pos_succ, krawRec_pos_succ, krawRec_pos_succ,
        krawRec_neg_succ p m (k + 1), krawRec_neg_succ p m k]
    omega

private theorem kraw_zero_k (s x : Nat) : kraw s x 0 = 1 := by
  unfold kraw; simp [List.range_succ, sumInt, altSign, choose_zero]

private theorem kraw_zero_pos (m k : Nat) : kraw m m k = altSign k * choose m k := by
  unfold kraw
  rw [Nat.sub_self]
  have hsum : ∀ (L : List Nat), (∀ r, r ∈ L → r < k) →
      sumInt (L.map (fun r => altSign r * choose m r * choose 0 (k - r))) = 0 := by
    intro L hL
    apply sumInt_zero
    intro v hv
    rw [List.mem_map] at hv
    rcases hv with ⟨r, hr, rfl⟩
    have hlt := hL r hr
    rw [choose_gt 0 (k - r) (by omega), Int.mul_zero]
  rw [List.range_succ, List.map_append, sumInt_append,
      hsum (List.range k) (fun r hr => List.mem_range.mp hr)]
  simp [sumInt, choose_zero]

private theorem kraw_pos_succ (p m k : Nat) :
    kraw (p + 1 + m) m (k + 1) = kraw (p + m) m (k + 1) + kraw (p + m) m k := by
  unfold kraw
  have hs1 : p + 1 + m - m = p + 1 := by omega
  have hs0 : p + m - m = p := by omega
  rw [hs1, hs0]
  have hsplit (r : Nat) (hr : r ∈ List.range (k + 1)) :
      altSign r * choose m r * choose (p + 1) (k + 1 - r) =
        altSign r * choose m r * choose p (k + 1 - r) +
        altSign r * choose m r * choose p (k - r) := by
    rw [List.mem_range] at hr
    have hsub : k + 1 - r = (k - r) + 1 := by omega
    rw [hsub, choose_succ_succ, Int.mul_add]
  rw [List.range_succ (k + 1)]
  simp only [List.map_append, sumInt_append]
  have hlast : sumInt ([k + 1].map (fun r => altSign r * choose m r * choose (p + 1) (k + 1 - r))) =
      sumInt ([k + 1].map (fun r => altSign r * choose m r * choose p (k + 1 - r))) := by
    simp [sumInt, choose_zero]
  have hpref :
      sumInt ((List.range (k + 1)).map (fun r => altSign r * choose m r * choose (p + 1) (k + 1 - r))) =
      sumInt ((List.range (k + 1)).map (fun r => altSign r * choose m r * choose p (k + 1 - r))) +
      sumInt ((List.range (k + 1)).map (fun r => altSign r * choose m r * choose p (k - r))) := by
    rw [← sumInt_map_add]
    congr 1
    apply List.map_congr_left
    intro r hr
    exact hsplit r hr
  rw [hpref, hlast]; omega

/-- Equivalence between `kraw (p + m) m k` (binomial sum) and `krawRec p m k`. -/
theorem kraw_eq_krawRec : ∀ (p m k : Nat), kraw (p + m) m k = krawRec p m k
  | 0, m, k => by
    rw [Nat.zero_add, kraw_zero_pos]
    induction m generalizing k with
    | zero =>
      cases k with
      | zero => decide
      | succ k' => simp [choose, krawRec, krawNeg]
    | succ m' ih =>
      cases k with
      | zero => simp [altSign, choose_zero, krawRec_zero]
      | succ k' =>
        show altSign (k' + 1) * choose (m' + 1) (k' + 1) =
          krawRec 0 m' (k' + 1) - krawRec 0 m' k'
        rw [← ih (k' + 1), ← ih k', choose_succ_succ, Int.mul_add, altSign_succ]
        simp only [Int.neg_mul]; omega
  | p + 1, m, 0 => by
    rw [kraw_zero_k, krawRec_zero]
  | p + 1, m, k + 1 => by
    rw [kraw_pos_succ p m k, kraw_eq_krawRec p m (k + 1), kraw_eq_krawRec p m k]; rfl

theorem kraw_at_zero (s k : Nat) : kraw s 0 k = choose s k := by
  have h : kraw (s + 0) 0 k = krawRec s 0 k := kraw_eq_krawRec s 0 k
  rw [Nat.add_zero] at h
  rw [h]; clear h
  induction s generalizing k with
  | zero =>
    cases k <;> rfl
  | succ s' ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      rw [krawRec_pos_succ, choose_succ_succ, ih (k' + 1), ih k']

theorem kraw_flip (s x k : Nat) (hxs : x ≤ s) :
    kraw s (s - x) k = altSign k * kraw s x k := by
  have hsym : ∀ (p m k : Nat), krawRec m p k = altSign k * krawRec p m k := by
    intro p
    induction p with
    | zero =>
      intro m k
      rw [← kraw_eq_krawRec 0 m k, ← kraw_eq_krawRec m 0 k, Nat.add_zero, Nat.zero_add,
          kraw_at_zero, kraw_zero_pos]
      have hsq : altSign k * altSign k = 1 := by unfold altSign; split <;> decide
      rw [← Int.mul_assoc, hsq, Int.one_mul]
    | succ p' ih =>
      intro m k
      cases k with
      | zero => rw [krawRec_zero, krawRec_zero]; decide
      | succ k' =>
        rw [krawRec_neg_succ m p' k', krawRec_pos_succ, ih m (k' + 1), ih m k',
            altSign_succ, Int.mul_add]
        simp only [Int.neg_mul]; omega
  have h1 : kraw s (s - x) k = krawRec x (s - x) k := by
    have hk := kraw_eq_krawRec x (s - x) k
    have heq : x + (s - x) = s := by omega
    rw [heq] at hk; exact hk
  have h2 : kraw s x k = krawRec (s - x) x k := by
    have hk := kraw_eq_krawRec (s - x) x k
    have heq : (s - x) + x = s := by omega
    rw [heq] at hk; exact hk
  rw [h1, h2, hsym (s - x) x k]

/-! ## Elementary symmetric character polynomials & exact sublist expansion -/

/-- Elementary symmetric polynomial of degree `k` in `{chr v a : a ∈ L}`. -/
def esym {n : Nat} (v : W n) : List (W n) → Nat → Int
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | a :: L, k + 1 => esym v L (k + 1) + chr v a * esym v L k

theorem esym_zero {n : Nat} (v : W n) (L : List (W n)) : esym v L 0 = 1 := by
  cases L <;> rfl

/-- XOR of a list of vectors in `W n`. -/
def xorList {n : Nat} : List (W n) → W n
  | [] => zero n
  | a :: L => add n a (xorList L)

/-- All length-`k` sublists of `L`. -/
def sublists {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, a :: L => sublists (k + 1) L ++ (sublists k L).map (a :: ·)

theorem esym_eq_krawRec {n : Nat} (v : W n) : ∀ (L : List (W n)) (k : Nat),
    let pos := (L.filter (fun a => !(dot n v a))).length
    let neg := (L.filter (fun a => dot n v a)).length
    esym v L k = krawRec pos neg k
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => by dsimp only; rw [esym_zero, krawRec_zero]
  | a :: L, k + 1 => by
    dsimp only
    show esym v L (k + 1) + chr v a * esym v L k = _
    rw [esym_eq_krawRec v L (k + 1), esym_eq_krawRec v L k]
    cases hd : dot n v a
    · simp only [List.filter_cons, hd, Bool.not_false, if_true, Bool.false_eq_true, if_false,
        List.length_cons, chr, sign, Int.one_mul]
      rw [krawRec_pos_succ]
    · simp only [List.filter_cons, hd, Bool.not_true, Bool.false_eq_true, if_false, if_true,
        List.length_cons, chr, sign]
      rw [krawRec_neg_succ]
      omega

theorem filter_pos_add_neg {n : Nat} (v : W n) : ∀ (L : List (W n)),
    (L.filter (fun a => !(dot n v a))).length + (L.filter (fun a => dot n v a)).length = L.length
  | [] => rfl
  | a :: L => by
    have ih := filter_pos_add_neg v L
    cases hd : dot n v a <;>
      simp only [List.filter_cons, hd, Bool.not_false, Bool.not_true, if_true,
        Bool.false_eq_true, if_false, List.length_cons] <;> omega

theorem esym_eq_kraw {n : Nat} (v : W n) (L : List (W n)) (k : Nat) :
    esym v L k = kraw L.length (L.filter (fun a => dot n v a)).length k := by
  rw [esym_eq_krawRec v L k, ← filter_pos_add_neg v L, kraw_eq_krawRec]

theorem esym_eq_sublists {n : Nat} (v : W n) : ∀ (L : List (W n)) (k : Nat),
    esym v L k = sumInt ((sublists k L).map (fun S => chr v (xorList S)))
  | [], 0 => by simp [esym, sublists, xorList, sumInt, chr, dot_zero_right, sign]
  | _ :: _, 0 => by simp [esym, sublists, xorList, sumInt, chr, dot_zero_right, sign]
  | [], _ + 1 => rfl
  | a :: L, k + 1 => by
    unfold esym sublists
    rw [List.map_append, sumInt_append, List.map_map]
    rw [esym_eq_sublists v L (k + 1), esym_eq_sublists v L k]
    congr 1
    rw [← sumInt_map_scale (chr v a), List.map_map]
    congr 1; apply List.map_congr_left
    intro S _
    show chr v a * chr v (xorList S) = chr v (add n a (xorList S))
    exact (Balanced242Plateau.chr_add v a (xorList S)).symm

/-! ## Summing products of three Krawtchouk polynomials over `W n` -/

private theorem total_sumInt {n : Nat} {α : Type} :
    ∀ (L : List α) (F : W n → α → Int),
      total n (fun v => sumInt (L.map (fun x => F v x))) =
        sumInt (L.map (fun x => total n (fun v => F v x)))
  | [], _ => by simp [sumInt, total_zero]
  | a :: t, F => by
    simp only [List.map_cons, sumInt, total_add, total_sumInt t F]

private theorem sum_chr_eq {n : Nat} (u : W n) :
    total n (fun v => chr v u) = many n * (if u = zero n then 1 else 0) := by
  have h := identity_spectrum n u
  have heq : total n (fun v => chr v u) = total n (chr u) := by
    apply congrArg (total n); funext v; simp only [chr, dot_comm n v u]
  rw [heq]
  change total n (chr u) = _ at h
  rw [h]
  if hz : u = zero n then simp [hz] else simp [hz]

/-- Exact character-orthogonality formula for the sum of any triple product of `esym` over `W n`. -/
theorem sum_triple_esym {n : Nat} (L1 L2 L3 : List (W n)) (i j l : Nat) :
    total n (fun v => esym v L1 i * esym v L2 j * esym v L3 l) =
      many n * sumInt ((sublists i L1).map (fun S1 =>
        sumInt ((sublists j L2).map (fun S2 =>
          sumInt ((sublists l L3).map (fun S3 =>
            if add n (xorList S1) (add n (xorList S2) (xorList S3)) = zero n then (1 : Int) else 0)))))) := by
  have hexp (v : W n) :
      esym v L1 i * esym v L2 j * esym v L3 l =
        sumInt ((sublists i L1).map (fun S1 =>
          sumInt ((sublists j L2).map (fun S2 =>
            sumInt ((sublists l L3).map (fun S3 =>
              chr v (add n (xorList S1) (add n (xorList S2) (xorList S3))))))))) := by
    rw [esym_eq_sublists v L1 i, esym_eq_sublists v L2 j, esym_eq_sublists v L3 l,
        Int.mul_assoc,
        sumInt_mul_sumInt (sublists j L2) (sublists l L3),
        sumInt_mul_sumInt (sublists i L1) (sublists j L2)]
    congr 1; apply List.map_congr_left; intro S1 _
    congr 1; apply List.map_congr_left; intro S2 _
    rw [← sumInt_map_scale (chr v (xorList S1)), List.map_map]
    congr 1; apply List.map_congr_left; intro S3 _
    show chr v (xorList S1) * (chr v (xorList S2) * chr v (xorList S3)) =
      chr v (add n (xorList S1) (add n (xorList S2) (xorList S3)))
    rw [Balanced242Plateau.chr_add, Balanced242Plateau.chr_add]
  rw [funext hexp, total_sumInt, ← sumInt_map_scale (many n), List.map_map]
  congr 1; apply List.map_congr_left; intro S1 _
  dsimp only [Function.comp_def]
  rw [total_sumInt, ← sumInt_map_scale (many n), List.map_map]
  congr 1; apply List.map_congr_left; intro S2 _
  dsimp only [Function.comp_def]
  rw [total_sumInt, ← sumInt_map_scale (many n), List.map_map]
  congr 1; apply List.map_congr_left; intro S3 _
  exact sum_chr_eq (add n (xorList S1) (add n (xorList S2) (xorList S3)))

/-! ## Connecting subset counts on `W n` to `kraw` -/

/-- Support list of a predicate `P : W n → Bool`. -/
def suppList {n : Nat} (P : W n → Bool) : List (W n) :=
  (worlds n).filter P

/-- Number of elements of `P` with `dot n v a = true` (the `c = true` half). -/
def halfCnt {n : Nat} (v : W n) (P : W n → Bool) : Nat :=
  ((suppList P).filter (fun a => dot n v a)).length

/-- Number of elements of `P` with `dot n v a = false` (the `c = false` half). -/
def halfCntFalse {n : Nat} (v : W n) (P : W n → Bool) : Nat :=
  ((suppList P).filter (fun a => !(dot n v a))).length

theorem halfCnt_le {n : Nat} (v : W n) (P : W n → Bool) :
    halfCnt v P ≤ (suppList P).length :=
  List.length_filter_le _ _

private theorem filter_false_nil {α : Type} : ∀ (L : List α), L.filter (fun _ => false) = []
  | [] => rfl
  | _ :: t => filter_false_nil t

theorem halfCnt_zero {n : Nat} (P : W n → Bool) : halfCnt (zero n) P = 0 := by
  unfold halfCnt
  have hfn : (fun a => dot n (zero n) a) = (fun _ => false) := funext (dot_zero n)
  rw [hfn, filter_false_nil]; rfl

theorem halfCnt_add_false {n : Nat} (v : W n) (P : W n → Bool) :
    halfCntFalse v P + halfCnt v P = (suppList P).length :=
  filter_pos_add_neg v (suppList P)

/-- Main theorem (all degrees `i, j, l`, all dimensions `n`):
    (1) Delsarte/MacWilliams nonnegativity:
          `-C(a, i) C(b, j) C(c, l) ≤ ∑_{v ≠ 0} K_i(a, x_v) K_j(b, y_v) K_l(c, z_v)`
    (2) Exact mod-`2^n` congruence (`replay.py`'s `mac` observation):
          `(∑_{v ≠ 0} K_i K_j K_l + C(a, i) C(b, j) C(c, l)) % (many n) = 0`. -/
theorem kraw_triple_nonneg_and_mod {n : Nat} (P Q R : W n → Bool) (i j l : Nat) :
    let a := (suppList P).length
    let b := (suppList Q).length
    let c := (suppList R).length
    let S := total n (fun v => nz v * (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l))
    let dc := choose a i * choose b j * choose c l;
    -dc ≤ S ∧ (S + dc) % many n = 0 := by
  intro a b c S dc
  have hfull : total n (fun v => kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l) =
      S + dc := by
    have hnz := nz_total (fun v => kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l)
    rw [halfCnt_zero, halfCnt_zero, halfCnt_zero, kraw_at_zero, kraw_at_zero, kraw_at_zero] at hnz
    change S = total n _ - dc at hnz
    exact (Int.sub_add_cancel _ _).symm.trans (congrArg (· + dc) hnz.symm)
  have heq : total n (fun v => kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l) =
      total n (fun v => esym v (suppList P) i * esym v (suppList Q) j * esym v (suppList R) l) := by
    apply congrArg (total n); funext v
    rw [esym_eq_kraw v (suppList P) i, esym_eq_kraw v (suppList Q) j, esym_eq_kraw v (suppList R) l]
    rfl
  rw [sum_triple_esym] at heq
  rw [hfull] at heq
  have hnn_inner : 0 ≤ sumInt ((sublists i (suppList P)).map (fun S1 =>
      sumInt ((sublists j (suppList Q)).map (fun S2 =>
        sumInt ((sublists l (suppList R)).map (fun S3 =>
          if add n (xorList S1) (add n (xorList S2) (xorList S3)) = zero n then (1 : Int) else 0)))))) := by
    apply sumInt_nonneg; intro x1 hx1
    rw [List.mem_map] at hx1; rcases hx1 with ⟨S1, _, rfl⟩
    apply sumInt_nonneg; intro x2 hx2
    rw [List.mem_map] at hx2; rcases hx2 with ⟨S2, _, rfl⟩
    apply sumInt_nonneg; intro x3 hx3
    rw [List.mem_map] at hx3; rcases hx3 with ⟨S3, _, rfl⟩
    split <;> decide
  have hmn : 0 ≤ many n := by have := many_pos n; omega
  have hprod : 0 ≤ S + dc := by rw [heq]; exact Int.mul_nonneg hmn hnn_inner
  have hmod : (S + dc) % many n = 0 := by rw [heq, Int.mul_emod_right]
  exact ⟨by omega, hmod⟩

/-- Half-count symmetry for even total degree `i + j + l`: replacing `(x, y, z)` by `(a-x, b-y, c-z)`
    leaves `K_i(a, x) K_j(b, y) K_l(c, z)` unchanged (justifying `lo ≤ hi` in `replay.py`). -/
theorem kraw_even_flip {n : Nat} (P Q R : W n → Bool) (v : W n) (i j l : Nat)
    (heven : (i + j + l) % 2 = 0) :
    let a := (suppList P).length
    let b := (suppList Q).length
    let c := (suppList R).length
    kraw a (halfCntFalse v P) i * kraw b (halfCntFalse v Q) j * kraw c (halfCntFalse v R) l =
      kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l := by
  intro a b c
  have hfP : halfCntFalse v P = a - halfCnt v P := by have := halfCnt_add_false v P; omega
  have hfQ : halfCntFalse v Q = b - halfCnt v Q := by have := halfCnt_add_false v Q; omega
  have hfR : halfCntFalse v R = c - halfCnt v R := by have := halfCnt_add_false v R; omega
  rw [hfP, hfQ, hfR,
      kraw_flip a (halfCnt v P) i (halfCnt_le v P),
      kraw_flip b (halfCnt v Q) j (halfCnt_le v Q),
      kraw_flip c (halfCnt v R) l (halfCnt_le v R)]
  have hprod : altSign i * altSign j * altSign l = 1 := by
    unfold altSign
    have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
    have hl : l % 2 = 0 ∨ l % 2 = 1 := by omega
    rcases hi with h1 | h1 <;> rcases hj with h2 | h2 <;> rcases hl with h3 | h3 <;>
      simp [h1, h2, h3] <;> omega
  calc
    altSign i * kraw a (halfCnt v P) i * (altSign j * kraw b (halfCnt v Q) j) *
        (altSign l * kraw c (halfCnt v R) l)
      = (altSign i * altSign j * altSign l) *
          (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l) := by ac_rfl
    _ = kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l := by
        rw [hprod, Int.one_mul]

/-! ## Degree-2 exact equalities for pairwise disjoint `P, Q, R` -/

private theorem sublists_zero {α : Type} (L : List α) : sublists 0 L = [[]] := by
  cases L <;> rfl

private theorem sublists_one_mem {α : Type} : ∀ {L : List α} {S : List α},
    S ∈ sublists 1 L → ∃ x, S = [x] ∧ x ∈ L
  | [], _, h => nomatch h
  | a :: t, S, h => by
    unfold sublists at h
    rw [List.mem_append] at h
    rcases h with h1 | h2
    · rcases sublists_one_mem h1 with ⟨x, rfl, hx⟩
      exact ⟨x, rfl, List.Mem.tail _ hx⟩
    · rw [sublists_zero] at h2
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at h2
      exact ⟨a, h2, List.Mem.head _⟩

private theorem sublists_two_mem {α : Type} : ∀ {L : List α} {S : List α},
    L.Nodup → S ∈ sublists 2 L → ∃ x y, S = [x, y] ∧ x ≠ y ∧ x ∈ L ∧ y ∈ L
  | [], _, _, h => nomatch h
  | a :: t, S, hnd, h => by
    rw [List.nodup_cons] at hnd
    unfold sublists at h
    rw [List.mem_append] at h
    rcases h with h1 | h2
    · rcases sublists_two_mem hnd.2 h1 with ⟨x, y, rfl, hne, hx, hy⟩
      exact ⟨x, y, rfl, hne, List.Mem.tail _ hx, List.Mem.tail _ hy⟩
    · rw [List.mem_map] at h2
      rcases h2 with ⟨S', hS', rfl⟩
      rcases sublists_one_mem hS' with ⟨y, rfl, hy⟩
      have hne : a ≠ y := fun heq => hnd.1 (heq ▸ hy)
      exact ⟨a, y, rfl, hne, List.Mem.head _, List.Mem.tail _ hy⟩

private theorem worlds_nodup_k : ∀ (n : Nat), (worlds n).Nodup
  | 0 => by decide
  | m + 1 => by
    show ((worlds m).map (fun x => (false, x)) ++ (worlds m).map (fun x => (true, x))).Nodup
    have ih := worlds_nodup_k m
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

private theorem suppList_nodup {n : Nat} (P : W n → Bool) : (suppList P).Nodup :=
  (worlds_nodup_k n).filter P

private theorem add_ne_zero_of_ne {n : Nat} {x y : W n} (hne : x ≠ y) : add n x y ≠ zero n := by
  intro h0
  have h1 : add n x (add n x y) = add n x (zero n) := congrArg (add n x) h0
  rw [← Balanced242Plateau.add_assoc', add_self, add_zero_left, add_zero_right] at h1
  exact hne h1.symm

/-- All six degree-2 Krawtchouk equalities (`i + j + l = 2`) for pairwise disjoint `P, Q, R`:
    `∑_{v ≠ 0} K_i(a, x_v) K_j(b, y_v) K_l(c, z_v) = -C(a, i) C(b, j) C(c, l)`. -/
theorem kraw_triple_deg2_eq {n : Nat} (P Q R : W n → Bool)
    (hPQ : ∀ x, (P x && Q x) = false) (hPR : ∀ x, (P x && R x) = false)
    (hQR : ∀ x, (Q x && R x) = false) (i j l : Nat) (hdeg : i + j + l = 2) :
    let a := (suppList P).length
    let b := (suppList Q).length
    let c := (suppList R).length
    total n (fun v =>
      nz v * (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l)) =
      -(choose a i * choose b j * choose c l) := by
  intro a b c
  have hfull : total n (fun v => kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l) =
      total n (fun v => nz v * (kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l)) +
      choose a i * choose b j * choose c l := by
    have hnz := nz_total (fun v => kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l)
    rw [halfCnt_zero, halfCnt_zero, halfCnt_zero, kraw_at_zero, kraw_at_zero, kraw_at_zero] at hnz
    exact ((Int.sub_add_cancel _ _).symm.trans (congrArg (· + _) hnz.symm))
  have heq : total n (fun v => kraw a (halfCnt v P) i * kraw b (halfCnt v Q) j * kraw c (halfCnt v R) l) =
      many n * sumInt ((sublists i (suppList P)).map (fun S1 =>
        sumInt ((sublists j (suppList Q)).map (fun S2 =>
          sumInt ((sublists l (suppList R)).map (fun S3 =>
            if add n (xorList S1) (add n (xorList S2) (xorList S3)) = zero n then (1 : Int) else 0)))))) := by
    rw [← sum_triple_esym]
    apply congrArg (total n); funext v
    rw [esym_eq_kraw v (suppList P) i, esym_eq_kraw v (suppList Q) j, esym_eq_kraw v (suppList R) l]
    rfl
  have hne_disj {A B : W n → Bool} (hAB : ∀ x, (A x && B x) = false)
      {x y : W n} (hx : x ∈ suppList A) (hy : y ∈ suppList B) : x ≠ y := by
    intro hxy; subst hxy
    have hA : A x = true := (List.mem_filter.mp hx).2
    have hB : B x = true := (List.mem_filter.mp hy).2
    have := hAB x; rw [hA, hB] at this; exact Bool.noConfusion this
  have hzero : sumInt ((sublists i (suppList P)).map (fun S1 =>
      sumInt ((sublists j (suppList Q)).map (fun S2 =>
        sumInt ((sublists l (suppList R)).map (fun S3 =>
          if add n (xorList S1) (add n (xorList S2) (xorList S3)) = zero n then (1 : Int) else 0)))))) = 0 := by
    apply sumInt_zero; intro x1 hx1
    rw [List.mem_map] at hx1; rcases hx1 with ⟨S1, hS1, rfl⟩
    apply sumInt_zero; intro x2 hx2
    rw [List.mem_map] at hx2; rcases hx2 with ⟨S2, hS2, rfl⟩
    apply sumInt_zero; intro x3 hx3
    rw [List.mem_map] at hx3; rcases hx3 with ⟨S3, hS3, rfl⟩
    have hnzx : add n (xorList S1) (add n (xorList S2) (xorList S3)) ≠ zero n := by
      cases i with
      | zero =>
        rw [sublists_zero] at hS1; simp only [List.mem_singleton] at hS1; subst hS1
        cases j with
        | zero =>
          have hl : l = 2 := by omega
          subst hl
          rw [sublists_zero] at hS2; simp only [List.mem_singleton] at hS2; subst hS2
          rcases sublists_two_mem (suppList_nodup R) hS3 with ⟨x, y, rfl, hne, _, _⟩
          simp only [xorList, add_zero_left, add_zero_right]; exact add_ne_zero_of_ne hne
        | succ j' =>
          cases j' with
          | zero =>
            have hl : l = 1 := by omega
            subst hl
            rcases sublists_one_mem hS2 with ⟨y, rfl, hy⟩
            rcases sublists_one_mem hS3 with ⟨z, rfl, hz⟩
            simp only [xorList, add_zero_left, add_zero_right]
            exact add_ne_zero_of_ne (hne_disj hQR hy hz)
          | succ j'' =>
            have hj : j'' = 0 := by omega
            have hl : l = 0 := by omega
            subst hj; subst hl
            rw [sublists_zero] at hS3; simp only [List.mem_singleton] at hS3; subst hS3
            rcases sublists_two_mem (suppList_nodup Q) hS2 with ⟨x, y, rfl, hne, _, _⟩
            simp only [xorList, add_zero_left, add_zero_right]; exact add_ne_zero_of_ne hne
      | succ i' =>
        cases i' with
        | zero =>
          cases j with
          | zero =>
            have hl : l = 1 := by omega
            subst hl
            rw [sublists_zero] at hS2; simp only [List.mem_singleton] at hS2; subst hS2
            rcases sublists_one_mem hS1 with ⟨x, rfl, hx⟩
            rcases sublists_one_mem hS3 with ⟨z, rfl, hz⟩
            simp only [xorList, add_zero_left, add_zero_right]
            exact add_ne_zero_of_ne (hne_disj hPR hx hz)
          | succ j' =>
            have hj : j' = 0 := by omega
            have hl : l = 0 := by omega
            subst hj; subst hl
            rw [sublists_zero] at hS3; simp only [List.mem_singleton] at hS3; subst hS3
            rcases sublists_one_mem hS1 with ⟨x, rfl, hx⟩
            rcases sublists_one_mem hS2 with ⟨y, rfl, hy⟩
            simp only [xorList, add_zero_right]
            exact add_ne_zero_of_ne (hne_disj hPQ hx hy)
        | succ i'' =>
          have hi : i'' = 0 := by omega
          have hj : j = 0 := by omega
          have hl : l = 0 := by omega
          subst hi; subst hj; subst hl
          rw [sublists_zero] at hS2 hS3
          simp only [List.mem_singleton] at hS2 hS3; subst hS2; subst hS3
          rcases sublists_two_mem (suppList_nodup P) hS1 with ⟨x, y, rfl, hne, _, _⟩
          simp only [xorList, add_zero_right]; exact add_ne_zero_of_ne hne
    simp [hnzx]
  rw [hzero, Int.mul_zero] at heq
  rw [hfull] at heq
  have hsub := congrArg (· - (choose a i * choose b j * choose c l)) heq
  simpa [Int.add_sub_cancel, Int.zero_sub] using hsub

end Balanced242Krawtchouk

#print axioms Balanced242Krawtchouk.kraw_eq_krawRec
#print axioms Balanced242Krawtchouk.kraw_at_zero
#print axioms Balanced242Krawtchouk.kraw_flip
#print axioms Balanced242Krawtchouk.sum_triple_esym
#print axioms Balanced242Krawtchouk.kraw_triple_nonneg_and_mod
#print axioms Balanced242Krawtchouk.kraw_even_flip
#print axioms Balanced242Krawtchouk.kraw_triple_deg2_eq
