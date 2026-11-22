/-
  Unconditional quartic weight lower bounds and divisibility laws used by `replay.py`
  (`six` and `half`), proved constructively without `SectionEnum` or `Classical.choice`:

    1. `half_mass_div8`: for any 7-variable section `transform D = 2 * H` with `H` odd
       and `|H| ≤ 7`, `8 ∣ (6x + 3y + 5z)` (`mass % 8 = 0`).
    2. `flat4_exc35_odd`: on any bent (`rr = 1`, rank 4) 4-flat with `transform G = 2 * H`,
       the `{3, 5}`-count `∑ 1_{|H| ∈ {3, 5}}` is ODD (hence `≥ 1`).
    3. `flat5_exc35_even`: on any quadratic 5-flat with `transform G = 2 * H`,
       the `{3, 5}`-count is EVEN; if rank 4 (`rr = 2`), it is `≥ 2`.
    4. `six_bc_ge_4`: on any 6-variable rank-4 section (`rr = 4`), `4 ≤ b + c ∧ (b + c) % 2 = 0`.
    5. `six_bc_ge_8`: on any 6-variable rank-6 section (`rr = 1`), `8 ≤ b + c ∧ (b + c) % 2 = 0`
       (proved via hyperplane transitivity + constructive finite pigeonhole on `W 6 → W 5`).
    6. `half_yz_ge_8` & `half_yz_ge_16`: on any 7-variable section of rank 4 (`rr = 8`) or
       rank 6 (`rr = 2`), `8 ≤ y + z` (resp. `16 ≤ y + z`) and `(y + z) % 2 = 0`.
-/
import Balanced242AnchorPair
import Balanced242SectionBounds

namespace Balanced242Quartic
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Hyperplane Balanced242Plateau Balanced242Rank
open Balanced242AnchorPair (sec_cube)

local notation "phase" => Balanced242Section0320.phase
local notation "bind" => Balanced242Plateau.ind

/-- Indicator `1` when `|h| ∈ {3, 5}`, else `0`. -/
def exc35 (h : Int) : Int :=
  if h.natAbs = 3 ∨ h.natAbs = 5 then 1 else 0

private theorem H_vals (h : Int) (ho : h % 2 = 1) (hc : h.natAbs ≤ 7) :
    h = -7 ∨ h = -5 ∨ h = -3 ∨ h = -1 ∨ h = 1 ∨ h = 3 ∨ h = 5 ∨ h = 7 := by
  omega

/-- Pointwise mod-8 relation linking `H`, `phase H`, and the `{3, 5}` indicator `exc35 H`. -/
theorem mod8_phase_exc (h : Int) (ho : h % 2 = 1) (hc : h.natAbs ≤ 7) :
    (h - phase h - 4 * exc35 h) % 8 = 0 := by
  rcases H_vals h ho hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem total_mod_eq_zero {n : Nat} {k : Int} (F : W n → Int)
    (hF : ∀ x, F x % k = 0) : total n F % k = 0 := by
  induction n with
  | zero => exact hF ()
  | succ m ih =>
    show (total m (fun z => F (false, z)) + total m (fun z => F (true, z))) % k = 0
    have h0 := ih (fun z => F (false, z)) (fun z => hF (false, z))
    have h1 := ih (fun z => F (true, z)) (fun z => hF (true, z))
    rw [Int.add_emod, h0, h1]; simp

/-- Unconditional proof of `8 ∣ (6x + 3y + 5z)` (`mass % 8 = 0`) for any 7-var section. -/
theorem half_mass_div8 (D H : W 7 → Int) (hspec : ∀ a, transform D a = 2 * H a)
    (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7) :
    let x := total 7 (fun a => if (H a).natAbs = 1 then (1 : Int) else 0)
    let y := total 7 (fun a => if (H a).natAbs = 5 then (1 : Int) else 0)
    let z := total 7 (fun a => if (H a).natAbs = 3 then (1 : Int) else 0)
    (6 * x + 3 * y + 5 * z) % 8 = 0 := by
  intro x y z
  have hene := Balanced242SectionBounds.section_energy D H hspec hH
  dsimp only at hene
  have hdiff : total 7 (fun u => D u * D u - D u) % 2 = 0 := by
    apply total_mod_eq_zero; intro u
    have hsub : D u * D u - D u = D u * (D u - 1) := by rw [Int.mul_sub, Int.mul_one]
    rw [hsub]
    if h0 : D u % 2 = 0 then
      rw [Int.mul_emod, h0, Int.zero_mul]; rfl
    else
      have h1 : (D u - 1) % 2 = 0 := by omega
      rw [Int.mul_emod, h1, Int.mul_zero]; rfl
  have hsumD : total 7 D = 2 * H (zero 7) := by
    have hs := hspec (zero 7)
    unfold transform at hs
    have hc (u : W 7) : D u * chr (zero 7) u = D u := by simp [chr, dot_zero, sign]
    rw [funext hc] at hs; exact hs
  rw [total_sub, hsumD] at hdiff
  omega

/-! ## Hyperplane partitioning & constructive search helpers -/

/-- Dot product on an affine hyperplane `secPt n w c` equals `c`. -/
theorem secPt_dot : ∀ (n : Nat) (w : W (n + 1)), w ≠ zero (n + 1) →
    ∀ (c : Bool) (x : W n), dot (n + 1) w (secPt n w c x) = c
  | 0, (true, _), _, c, () => by
    rw [secPt_true]; cases c <;> rfl
  | 0, (false, _), hw, _, _ => absurd rfl hw
  | m + 1, (true, w'), _, c, x => by
    rw [secPt_true]
    show xor (true && xor c (dot (m + 1) w' x)) (dot (m + 1) w' x) = c
    cases c <;> cases dot (m + 1) w' x <;> rfl
  | m + 1, (false, w'), hw, c, (bx, x') => by
    have hw' : w' ≠ zero (m + 1) := fun h => hw (by rw [h]; rfl)
    show xor (false && bx) (dot (m + 1) w' (secPt m w' c x')) = c
    rw [secPt_dot m w' hw' c x']; simp

/-- Partitioning `total (n+1) F` along the two complementary hyperplanes of `w ≠ 0`. -/
theorem sec_sum : ∀ (n : Nat) (w : W (n + 1)), w ≠ zero (n + 1) →
    ∀ (F : W (n + 1) → Int),
      total (n + 1) F = total n (fun x => F (secPt n w false x)) +
                        total n (fun x => F (secPt n w true x))
  | 0, (true, _), _, F => by
    show F (false, ()) + F (true, ()) = F (secPt 0 (true, ()) false ()) + F (secPt 0 (true, ()) true ())
    rw [secPt_true, secPt_true]; rfl
  | 0, (false, _), hw, _ => absurd rfl hw
  | m + 1, (true, w'), _, F => by
    show total (m + 1) (fun x => F (false, x)) + total (m + 1) (fun x => F (true, x)) = _
    have hpt (x : W (m + 1)) :
        F (false, x) + F (true, x) =
          F (secPt (m + 1) (true, w') false x) + F (secPt (m + 1) (true, w') true x) := by
      rw [secPt_true, secPt_true]
      cases dot (m + 1) w' x
      · simp
      · simp [Int.add_comm]
    rw [← total_add, ← total_add]; exact congrArg (total (m + 1)) (funext hpt)
  | m + 1, (false, w'), hw, F => by
    have hw' : w' ≠ zero (m + 1) := fun h => hw (by rw [h]; rfl)
    show total (m + 1) (fun x => F (false, x)) + total (m + 1) (fun x => F (true, x)) =
      (total m (fun x' => F (false, secPt m w' false x')) + total m (fun x' => F (true, secPt m w' false x'))) +
      (total m (fun x' => F (false, secPt m w' true x')) + total m (fun x' => F (true, secPt m w' true x')))
    rw [sec_sum m w' hw' (fun x => F (false, x)), sec_sum m w' hw' (fun x => F (true, x))]
    omega

/-- Constructive search for an element failing a Bool predicate on a list. -/
private def findFalse {α : Type} (p : α → Bool) : (L : List α) → L.all p = false → { a : α // a ∈ L ∧ p a = false }
  | [], h => False.elim (Bool.noConfusion h)
  | a :: t, h =>
    match hp : p a with
    | false => ⟨a, List.Mem.head _, hp⟩
    | true =>
      have ht : t.all p = false := by simp only [List.all_cons, hp, Bool.true_and] at h; exact h
      let r := findFalse p t ht
      ⟨r.1, List.Mem.tail _ r.2.1, r.2.2⟩

private theorem all_worlds_true_of_total {n : Nat} (p : W n → Bool)
    (h : total n (fun x => bind (p x)) = many n) : (worlds n).all p = true := by
  rw [List.all_eq_true]; intro x _
  cases hx : p x
  · exfalso
    have hle : total n (fun y => bind (p y)) ≤ many n - 1 := by
      have hpt (y : W n) : bind (p y) ≤ (1 : Int) - hits x y := by
        unfold Balanced242Plateau.ind hits
        if hy : x = y then
          subst hy; simp [hx]
        else
          simp only [hy, if_false, Int.sub_zero]; cases p y <;> decide
      have hm := total_mono n _ _ hpt
      rw [total_sub, total_const, Int.mul_one, diagonal] at hm
      exact hm
    omega
  · rfl

private def find_true_of_pos {n : Nat} (p : W n → Bool)
    (h : 0 < total n (fun x => bind (p x))) : { x : W n // p x = true } :=
  have hall : (worlds n).all (fun x => !p x) = false := by
    cases hb : (worlds n).all (fun x => !p x)
    · rfl
    · exfalso
      rw [List.all_eq_true] at hb
      have hz (x : W n) : bind (p x) = 0 := by
        have := hb x (all_worlds n x)
        cases hx : p x <;> simp [hx] at this ⊢ <;> rfl
      rw [funext hz, total_zero] at h; omega
  let r := findFalse (fun x => !p x) (worlds n) hall
  ⟨r.1, by have h := r.2.2; cases hp : p r.1 <;> simp [hp] at h ⊢⟩

private def find_false_of_lt {n : Nat} (p : W n → Bool)
    (h : total n (fun x => bind (p x)) < many n) : { x : W n // p x = false } :=
  have hall : (worlds n).all p = false := by
    cases hb : (worlds n).all p
    · rfl
    · exfalso
      rw [List.all_eq_true] at hb
      have h1 (x : W n) : bind (p x) = 1 := by
        have := hb x (all_worlds n x); simp [Balanced242Plateau.ind, this]
      rw [funext h1, total_const, Int.mul_one] at h; omega
  let r := findFalse p (worlds n) hall
  ⟨r.1, r.2.2⟩

/-- Recover `rr β` from a known plateau height `M > 0`. -/
private theorem rr_from_plateau {n : Nat} (β : W n → Bool) (hc : Cube β) (M : Int)
    (hplat : ∀ y, transform (fun a => sign (β a)) y = 0 ∨
      transform (fun a => sign (β a)) y = M ∨ transform (fun a => sign (β a)) y = -M) :
    many n * rr β = M * M := by
  have hrg := rr_good β hc
  have hrr := rr_pos β
  have hmn := many_pos n
  have hpos : 0 < total n (fun y => bind (good β y)) := by
    if h : 0 < total n (fun y => bind (good β y)) then exact h
    else
      exfalso
      have hle : rr β * total n (fun y => bind (good β y)) ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
  let ⟨y, hy⟩ := find_true_of_pos (good β) hpos
  have hsg := spec_good β hc y
  rw [hy] at hsg
  simp only [Balanced242Plateau.ind, if_true, Int.mul_one] at hsg
  rcases hplat y with h | h | h
  · rw [h] at hsg
    have hprod : 0 < many n * rr β := Int.mul_pos hmn (by omega)
    omega
  · rw [h] at hsg; exact hsg.symm
  · rw [h, Int.neg_mul_neg] at hsg; exact hsg.symm

/-- Constructive witness of a direction `u ≠ 0` with `perp β u = false` whenever `2 ≤ rr β`. -/
private def find_non_perp {n : Nat} (β : W n → Bool) (hrr : 2 ≤ rr β) :
    { u : W n // u ≠ zero n ∧ perp β u = false } :=
  have hrp := rr_perp β
  have hmn := many_pos n
  have hlt : total n (fun w => bind (perp β w)) < many n := by
    if h : total n (fun w => bind (perp β w)) < many n then exact h
    else
      exfalso
      have hge : 2 * many n ≤ rr β * total n (fun w => bind (perp β w)) := by
        have h1 : 2 * many n ≤ rr β * many n :=
          Int.mul_le_mul_of_nonneg_right hrr (by omega)
        have h2 : rr β * many n ≤ rr β * total n (fun w => bind (perp β w)) :=
          Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
        omega
      omega
  let ⟨u, hu⟩ := find_false_of_lt (perp β) hlt
  have hne : u ≠ zero n := by
    intro h0; subst h0
    have hp0 : perp β (zero n) = true := by rw [perp_spec]; intro e _; exact dot_zero n e
    rw [hp0] at hu; exact Bool.noConfusion hu
  ⟨u, hne, hu⟩

/-- Any `W n` with `transform G = 2 * H` satisfies `2 * total n H = many n * G (zero n)`. -/
private theorem sum_H_of_transform {n : Nat} (G H : W n → Int) (hspec : ∀ a, transform G a = 2 * H a) :
    2 * total n H = many n * G (zero n) := by
  have hinv := inversion G (zero n)
  have h0 (a : W n) : transform G a * chr a (zero n) = 2 * H a := by
    rw [hspec a]; simp [chr, dot_zero_right, sign]
  rw [funext h0, total_scale] at hinv
  exact hinv

/-! ## Step 1 & Step 2: 4-flat oddness and 5-flat evenness -/

/-- On a bent (`rr = 1`, rank 4) 4-flat with `transform G = 2 * H`, `∑ exc35(H)` is odd (≥ 1). -/
theorem flat4_exc35_odd (G H : W 4 → Int) (hspec : ∀ a, transform G a = 2 * H a)
    (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7)
    (β : W 4 → Bool) (hc : Cube β) (hph : ∀ a, phase (H a) = sign (β a))
    (hrr : rr β = 1) :
    total 4 (fun a => exc35 (H a)) % 2 = 1 ∧ 1 ≤ total 4 (fun a => exc35 (H a)) := by
  have hsumH : total 4 H % 8 = 0 := by
    have hs := sum_H_of_transform G H hspec
    have hm : many 4 = 16 := by decide
    rw [hm] at hs
    have : total 4 H = 8 * G (zero 4) := by omega
    rw [this]; omega
  have hall_good : good β (zero 4) = true := by
    have hrg := rr_good β hc
    rw [hrr, Int.one_mul] at hrg
    have ha := all_worlds_true_of_total (good β) hrg
    rw [List.all_eq_true] at ha
    exact ha (zero 4) (all_worlds 4 (zero 4))
  have hsq : transform (fun a => sign (β a)) (zero 4) * transform (fun a => sign (β a)) (zero 4) = 16 := by
    have hsg := spec_good β hc (zero 4)
    rw [hall_good, hrr] at hsg
    have hm : many 4 = 16 := by decide
    rw [hm] at hsg; simpa [Balanced242Plateau.ind] using hsg
  have hsumPh : total 4 (fun a => phase (H a)) = 4 ∨ total 4 (fun a => phase (H a)) = -4 := by
    have heq : total 4 (fun a => phase (H a)) = transform (fun a => sign (β a)) (zero 4) := by
      unfold transform; apply congrArg (total 4); funext a
      rw [hph a]; simp [chr, dot_zero, sign]
    rw [heq]
    exact sq_cases _ 4 hsq
  have hmod : total 4 (fun a => H a - phase (H a) - 4 * exc35 (H a)) % 8 = 0 :=
    total_mod_eq_zero _ (fun a => mod8_phase_exc (H a) (hH a).1 (hH a).2)
  rw [total_sub, total_sub, total_scale] at hmod
  have hodd : total 4 (fun a => exc35 (H a)) % 2 = 1 := by
    rcases hsumPh with h4 | h4 <;> rw [h4] at hmod <;> omega
  have hnn : 0 ≤ total 4 (fun a => exc35 (H a)) := by
    rw [← total_zero 4]
    exact total_mono 4 _ _ (fun a => by unfold exc35; split <;> decide)
  exact ⟨hodd, by omega⟩

private theorem dvd8_of_sq_dvd32 (s k : Int) (h : s * s = 32 * k) : s % 8 = 0 := by
  let q := s / 8
  let r := s % 8
  have hr : 0 ≤ r ∧ r < 8 := ⟨Int.emod_nonneg s (by decide), Int.emod_lt_of_pos s (by decide)⟩
  have hdiv : 8 * q + r = s := Int.ediv_add_emod s 8
  have hsq : s * s = 64 * (q * q) + 16 * (q * r) + r * r := by
    rw [← hdiv]
    simp only [Int.add_mul, Int.mul_add]
    have a1 : 8 * q * (8 * q) = 64 * (q * q) := by
      have : 8 * q * (8 * q) = (8 * 8) * (q * q) := by ac_rfl
      rw [this]; rfl
    have a2 : 8 * q * r = 8 * (q * r) := Int.mul_assoc 8 q r
    have a3 : r * (8 * q) = 8 * (q * r) := by ac_rfl
    rw [a1, a2, a3]; omega
  rw [hsq] at h
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  rcases hr_cases with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0
  · exact h0
  · rw [h0] at h; omega
  · rw [h0] at h; omega
  · rw [h0] at h; omega
  · rw [h0] at h
    have : 16 * (q * 4) = 64 * q := by
      have : 16 * (q * 4) = (16 * 4) * q := by ac_rfl
      rw [this]; rfl
    rw [this] at h; omega
  · rw [h0] at h; omega
  · rw [h0] at h; omega
  · rw [h0] at h; omega

/-- On any quadratic 5-flat with `transform G = 2 * H`, `∑ exc35(H)` is always EVEN. -/
theorem flat5_exc35_even (G H : W 5 → Int) (hspec : ∀ a, transform G a = 2 * H a)
    (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7)
    (β : W 5 → Bool) (hc : Cube β) (hph : ∀ a, phase (H a) = sign (β a)) :
    total 5 (fun a => exc35 (H a)) % 2 = 0 := by
  have hsumH : total 5 H % 8 = 0 := by
    have hs := sum_H_of_transform G H hspec
    have hm : many 5 = 32 := by decide
    rw [hm] at hs
    have : total 5 H = 16 * G (zero 5) := by omega
    rw [this]; omega
  have hsumPh : total 5 (fun a => phase (H a)) % 8 = 0 := by
    have heq : total 5 (fun a => phase (H a)) = transform (fun a => sign (β a)) (zero 5) := by
      unfold transform; apply congrArg (total 5); funext a
      rw [hph a]; simp [chr, dot_zero, sign]
    rw [heq]
    have hsg := spec_good β hc (zero 5)
    have hm : many 5 = 32 := by decide
    rw [hm] at hsg
    exact dvd8_of_sq_dvd32 _ _ hsg
  have hmod : total 5 (fun a => H a - phase (H a) - 4 * exc35 (H a)) % 8 = 0 :=
    total_mod_eq_zero _ (fun a => mod8_phase_exc (H a) (hH a).1 (hH a).2)
  rw [total_sub, total_sub, total_scale] at hmod
  omega

/-- On a rank-4 (`rr = 2`) 5-flat with `transform G = 2 * H`, `∑ exc35(H) ≥ 2` and EVEN. -/
theorem flat5_rank4_exc35 (G H : W 5 → Int) (hspec : ∀ a, transform G a = 2 * H a)
    (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7)
    (β : W 5 → Bool) (hc : Cube β) (hph : ∀ a, phase (H a) = sign (β a))
    (hrr : rr β = 2) :
    2 ≤ total 5 (fun a => exc35 (H a)) ∧ total 5 (fun a => exc35 (H a)) % 2 = 0 := by
  obtain ⟨u, hu, hnp⟩ := find_non_perp β (by omega)
  have hMM : (8 : Int) * 8 = many 5 * rr β := by rw [hrr]; decide
  have hside (c : Bool) : 1 ≤ total 4 (fun a => exc35 (H (secPt 4 u c a))) := by
    let βc : W 4 → Bool := fun a => β (secPt 4 u c a)
    have hcc : Cube βc := sec_cube β hc u c
    have hplat (y : W 4) :
        transform (fun a => sign (βc a)) y = 0 ∨
        transform (fun a => sign (βc a)) y = 4 ∨
        transform (fun a => sign (βc a)) y = -4 := by
      have hlv := (section_levels β hc u hu c 8 hMM y).2 hnp
      change 2 * transform (fun a => sign (βc a)) y = 0 ∨
        2 * transform (fun a => sign (βc a)) y = 8 ∨
        2 * transform (fun a => sign (βc a)) y = -8 at hlv
      rcases hlv with h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    have hrr4 : rr βc = 1 := by
      have h := rr_from_plateau βc hcc 4 hplat
      have hm : many 4 = 16 := by decide
      rw [hm] at h; omega
    have hspec4 (a : W 4) : transform (secFun 4 u c G) a = 2 * H (secPt 4 u c a) := by
      rw [← sec_transform 4 u hu c G a, hspec]
    exact (flat4_exc35_odd (secFun 4 u c G) (fun a => H (secPt 4 u c a)) hspec4
      (fun a => hH (secPt 4 u c a)) βc hcc (fun a => hph (secPt 4 u c a)) hrr4).2
  have hsp := sec_sum 4 u hu (fun a => exc35 (H a))
  have h0 := hside false
  have h1 := hside true
  exact ⟨by rw [hsp]; omega, flat5_exc35_even G H hspec hH β hc hph⟩

/-! ## Step 3: 6-variable rank-4 (`b + c ≥ 4`) and rank-6 (`b + c ≥ 8`) bounds -/

private theorem total_exc35_eq_bc {n : Nat} (H : W n → Int) :
    total n (fun a => exc35 (H a)) =
      total n (fun a => if (H a).natAbs = 5 then (1 : Int) else 0) +
      total n (fun a => if (H a).natAbs = 3 then (1 : Int) else 0) := by
  rw [← total_add]
  apply congrArg (total n); funext a; unfold exc35
  if h5 : (H a).natAbs = 5 then
    simp [h5]
  else if h3 : (H a).natAbs = 3 then
    simp [h5, h3]
  else
    simp [h5, h3]

/-- `replay.py`'s `six` rank-4 quartic bound: `4 ≤ b + c` and `2 ∣ (b + c)`. -/
theorem six_bc_ge_4 (G H : W 6 → Int) (hspec : ∀ a, transform G a = 2 * H a)
    (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7)
    (β : W 6 → Bool) (hc : Cube β) (hph : ∀ a, phase (H a) = sign (β a))
    (hrr : rr β = 4) :
    let b := total 6 (fun a => if (H a).natAbs = 5 then (1 : Int) else 0)
    let c := total 6 (fun a => if (H a).natAbs = 3 then (1 : Int) else 0)
    4 ≤ b + c ∧ (b + c) % 2 = 0 := by
  intro b c
  obtain ⟨u, hu, hnp⟩ := find_non_perp β (by omega)
  have hMM : (16 : Int) * 16 = many 6 * rr β := by rw [hrr]; decide
  have hside (d : Bool) :
      2 ≤ total 5 (fun a => exc35 (H (secPt 5 u d a))) ∧
      total 5 (fun a => exc35 (H (secPt 5 u d a))) % 2 = 0 := by
    let βd : W 5 → Bool := fun a => β (secPt 5 u d a)
    have hcd : Cube βd := sec_cube β hc u d
    have hplat (y : W 5) :
        transform (fun a => sign (βd a)) y = 0 ∨
        transform (fun a => sign (βd a)) y = 8 ∨
        transform (fun a => sign (βd a)) y = -8 := by
      have hlv := (section_levels β hc u hu d 16 hMM y).2 hnp
      change 2 * transform (fun a => sign (βd a)) y = 0 ∨
        2 * transform (fun a => sign (βd a)) y = 16 ∨
        2 * transform (fun a => sign (βd a)) y = -16 at hlv
      rcases hlv with h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    have hrr5 : rr βd = 2 := by
      have h := rr_from_plateau βd hcd 8 hplat
      have hm : many 5 = 32 := by decide
      rw [hm] at h; omega
    have hspec5 (a : W 5) : transform (secFun 5 u d G) a = 2 * H (secPt 5 u d a) := by
      rw [← sec_transform 5 u hu d G a, hspec]
    exact flat5_rank4_exc35 (secFun 5 u d G) (fun a => H (secPt 5 u d a)) hspec5
      (fun a => hH (secPt 5 u d a)) βd hcd (fun a => hph (secPt 5 u d a)) hrr5
  have hsp := sec_sum 5 u hu (fun a => exc35 (H a))
  have h0 := hside false
  have h1 := hside true
  have hbc : b + c = total 6 (fun a => exc35 (H a)) := (total_exc35_eq_bc H).symm
  rw [hbc, hsp]
  exact ⟨by omega, by omega⟩

/-! ### Constructive finite pigeonhole on `W 6 → W 5` (zero `Classical.choice`) -/

private def findCollisionAux {α β : Type} [DecidableEq β] (f : α → β) :
    List α → Option (α × α)
  | [] => none
  | a :: t =>
    match t.find? (fun b => decide (f a = f b)) with
    | some b => some (a, b)
    | none => findCollisionAux f t

private theorem nodup_remove_length {β : Type} [DecidableEq β] (x : β) :
    ∀ (ys : List β), x ∈ ys → (ys.erase x).length + 1 = ys.length
  | [], h => nomatch h
  | y :: t, h => by
    simp only [List.erase_cons]
    if hxy : y = x then
      subst hxy; simp
    else
      have hbeq : (y == x) = false := beq_false_of_ne hxy
      simp only [hbeq, Bool.false_eq_true, if_false, List.length_cons]
      have hxt : x ∈ t := by
        cases h with
        | head => exact absurd rfl hxy
        | tail _ ht => exact ht
      have ih := nodup_remove_length x t hxt
      omega

private theorem mem_erase_of_ne {β : Type} [DecidableEq β] {x y : β} (hne : y ≠ x) :
    ∀ {ys : List β}, y ∈ ys → y ∈ ys.erase x
  | [], h => nomatch h
  | z :: t, h => by
    simp only [List.erase_cons]
    if hzx : z = x then
      subst hzx; simp only [beq_self_eq_true, if_true]
      cases h with
      | head => exact absurd rfl hne
      | tail _ ht => exact ht
    else
      have hbeq : (z == x) = false := beq_false_of_ne hzx
      simp only [hbeq, Bool.false_eq_true, if_false]
      cases h with
      | head => exact List.Mem.head _
      | tail _ ht => exact List.Mem.tail _ (mem_erase_of_ne hne ht)

private theorem findCollision_some {α β : Type} [DecidableEq β] (f : α → β) :
    ∀ (xs : List α) (ys : List β),
      (∀ x, x ∈ xs → f x ∈ ys) →
      ys.length < xs.length →
      ∃ p, findCollisionAux f xs = some p ∧ p.1 ∈ xs ∧ p.2 ∈ xs ∧ f p.1 = f p.2 ∧
        (xs.Nodup → p.1 ≠ p.2)
  | [], _, _, hlt => by simp at hlt
  | a :: t, ys, hsub, hlt => by
    unfold findCollisionAux
    cases hfind : t.find? (fun b => decide (f a = f b)) with
    | some b =>
      have hmem : b ∈ t := List.mem_of_find?_eq_some hfind
      have hdec : decide (f a = f b) = true := List.find?_some (p := fun b => decide (f a = f b)) hfind
      have heq : f a = f b := of_decide_eq_true hdec
      refine ⟨(a, b), rfl, List.Mem.head _, List.Mem.tail _ hmem, heq, ?_⟩
      intro hnd hab
      rw [List.nodup_cons] at hnd
      dsimp only at hab; subst hab; exact hnd.1 hmem
    | none =>
      have hne (x : α) (hx : x ∈ t) : f x ≠ f a := by
        intro hfx
        have h1 := List.find?_eq_none.mp hfind x hx
        simp [hfx] at h1
      have hsub' (x : α) (hx : x ∈ t) : f x ∈ ys.erase (f a) :=
        mem_erase_of_ne (hne x hx) (hsub x (List.Mem.tail _ hx))
      have hlen := nodup_remove_length (f a) ys (hsub a (List.Mem.head _))
      have hlt' : (ys.erase (f a)).length < t.length := by
        simp only [List.length_cons] at hlt; omega
      obtain ⟨p, hp, hm1, hm2, hfeq, hndp⟩ := findCollision_some f t (ys.erase (f a)) hsub' hlt'
      refine ⟨p, hp, List.Mem.tail _ hm1, List.Mem.tail _ hm2, hfeq, ?_⟩
      intro hnd
      rw [List.nodup_cons] at hnd
      exact hndp hnd.2

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

private theorem worlds_length : ∀ (n : Nat), (worlds n).length = 2 ^ n
  | 0 => rfl
  | m + 1 => by
    show ((worlds m).map (fun x => (false, x)) ++ (worlds m).map (fun x => (true, x))).length = 2 ^ (m + 1)
    rw [List.length_append, List.length_map, List.length_map, worlds_length m]
    have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by
      rw [Nat.pow_succ, Nat.mul_two]
    exact this.symm

/-- Constructive collision finder for any map `W 6 → W 5` (64 inputs, 32 outputs). -/
private def collide65 (f : W 6 → W 5) : { p : W 6 × W 6 // p.1 ≠ p.2 ∧ f p.1 = f p.2 } :=
  match h : findCollisionAux f (worlds 6) with
  | some p =>
    have hspec : p.1 ≠ p.2 ∧ f p.1 = f p.2 := by
      have hex := findCollision_some f (worlds 6) (worlds 5)
        (fun x _ => all_worlds 5 (f x))
        (by rw [worlds_length 5, worlds_length 6]; decide)
      rcases hex with ⟨q, hq, _, _, hfeq, hnd⟩
      rw [h] at hq
      have hpq : p = q := Option.some.inj hq
      rw [hpq]
      exact ⟨hnd (worlds_nodup 6), hfeq⟩
    ⟨p, hspec⟩
  | none =>
    False.elim (by
      have hex := findCollision_some f (worlds 6) (worlds 5)
        (fun x _ => all_worlds 5 (f x))
        (by rw [worlds_length 5, worlds_length 6]; decide)
      rcases hex with ⟨q, hq, _⟩
      rw [h] at hq
      exact Option.noConfusion hq)

private theorem total_filter_length : ∀ (n : Nat) (P : W n → Bool),
    ((worlds n).filter P).length = (total n (fun a => bind (P a))).toNat := by
  have helper : ∀ (n : Nat) (P : W n → Bool),
      (((worlds n).filter P).length : Int) = total n (fun a => bind (P a)) := by
    intro n
    induction n with
    | zero =>
      intro P
      show (([()] : List (W 0)).filter P).length = bind (P ())
      cases hp : P () <;> simp [List.filter, hp, Balanced242Plateau.ind]
    | succ m ih =>
      intro P
      show ((((worlds m).map (fun x => (false, x)) ++ (worlds m).map (fun x => (true, x))).filter P).length : Int) =
        total m (fun x => bind (P (false, x))) + total m (fun x => bind (P (true, x)))
      rw [List.filter_append, List.length_append, Int.natCast_add,
          List.filter_map, List.filter_map, List.length_map, List.length_map,
          ih (P ∘ fun x => (false, x)), ih (P ∘ fun x => (true, x))]
      rfl
  intro n P
  have h := helper n P
  omega

/-- Any set of `≤ 6` points in `W 6` is disjoint from at least one affine hyperplane `secPt 5 u c`. -/
private def exists_missing_hyperplane (P : W 6 → Bool)
    (hle : total 6 (fun a => bind (P a)) ≤ 6) :
    { uc : W 6 × Bool // uc.1 ≠ zero 6 ∧ ∀ x : W 5, P (secPt 5 uc.1 uc.2 x) = false } :=
  have hlen_int : (((worlds 6).filter P).length : Int) = total 6 (fun a => bind (P a)) := by
    have h := total_filter_length 6 P
    have hnn : 0 ≤ total 6 (fun a => bind (P a)) := by
      rw [← total_zero 6]
      exact total_mono 6 _ _ (fun a => ind_nonneg _)
    omega
  match hL : (worlds 6).filter P with
  | [] =>
    ⟨((true, zero 5), false), by intro h; exact Bool.noConfusion (Prod.mk.inj h).1, fun x => by
      cases hp : P (secPt 5 (true, zero 5) false x)
      · rfl
      · exfalso
        have hmem : secPt 5 (true, zero 5) false x ∈ (worlds 6).filter P :=
          List.mem_filter.mpr ⟨all_worlds 6 _, hp⟩
        rw [hL] at hmem; exact nomatch hmem⟩
  | p0 :: rest =>
    have hrlen : rest.length ≤ 5 := by
      rw [hL] at hlen_int; simp only [List.length_cons] at hlen_int; omega
    let nthOr (i : Nat) : W 6 :=
      match rest[i]? with
      | some p => add 6 p0 p
      | none => zero 6
    let v0 := nthOr 0; let v1 := nthOr 1; let v2 := nthOr 2; let v3 := nthOr 3; let v4 := nthOr 4
    let Φ (u : W 6) : W 5 :=
      (dot 6 u v0, dot 6 u v1, dot 6 u v2, dot 6 u v3, dot 6 u v4, ())
    let col := collide65 Φ
    let u := add 6 col.1.1 col.1.2
    have hu : u ≠ zero 6 := by
      intro h0
      have heq : col.1.1 = col.1.2 := by
        have h1 : add 6 col.1.1 (add 6 col.1.1 col.1.2) = add 6 col.1.1 (zero 6) :=
          congrArg (add 6 col.1.1) h0
        rw [← Balanced242Plateau.add_assoc', add_self, add_zero_left, add_zero_right] at h1
        exact h1.symm
      exact col.2.1 heq
    have hdot_zero (v : W 6) (heq : dot 6 col.1.1 v = dot 6 col.1.2 v) : dot 6 u v = false := by
      dsimp only [u]; rw [dot_add, heq]; cases dot 6 col.1.2 v <;> rfl
    have hΦ := col.2.2
    have h0 : dot 6 u v0 = false := hdot_zero v0 (Prod.mk.inj hΦ).1
    have h1 : dot 6 u v1 = false := hdot_zero v1 (Prod.mk.inj (Prod.mk.inj hΦ).2).1
    have h2 : dot 6 u v2 = false := hdot_zero v2 (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hΦ).2).2).1
    have h3 : dot 6 u v3 = false := hdot_zero v3 (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hΦ).2).2).2).1
    have h4 : dot 6 u v4 = false := hdot_zero v4 (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hΦ).2).2).2).2).1
    have hget (i : Nat) (hi : i < rest.length) : nthOr i = add 6 p0 rest[i] := by
      simp [nthOr, List.getElem?_eq_getElem hi]
    have hrest (p : W 6) (hp : p ∈ rest) : dot 6 u (add 6 p0 p) = false := by
      rcases List.mem_iff_getElem.mp hp with ⟨i, hi, rfl⟩
      have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hi5 with rfl | rfl | rfl | rfl | rfl
      · rw [← hget 0 hi]; exact h0
      · rw [← hget 1 hi]; exact h1
      · rw [← hget 2 hi]; exact h2
      · rw [← hget 3 hi]; exact h3
      · rw [← hget 4 hi]; exact h4
    let c := !(dot 6 u p0)
    ⟨(u, c), hu, fun x => by
      cases hp : P (secPt 5 u c x)
      · rfl
      · exfalso
        have hmem : secPt 5 u c x ∈ p0 :: rest := by
          rw [← hL]; exact List.mem_filter.mpr ⟨all_worlds 6 _, hp⟩
        have hd : dot 6 u (secPt 5 u c x) = c := secPt_dot 5 u hu c x
        rcases List.mem_cons.mp hmem with heq | htail
        · rw [heq] at hd
          dsimp only [c] at hd; cases dot 6 u p0 <;> simp at hd
        · have hdz := hrest (secPt 5 u c x) htail
          rw [dot_right, hd] at hdz
          dsimp only [c] at hdz; cases dot 6 u p0 <;> simp at hdz⟩

/-- `replay.py`'s `six` rank-6 quartic bound: `8 ≤ b + c` and `2 ∣ (b + c)`. -/
theorem six_bc_ge_8 (G H : W 6 → Int) (hspec : ∀ a, transform G a = 2 * H a)
    (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7)
    (β : W 6 → Bool) (hc : Cube β) (hph : ∀ a, phase (H a) = sign (β a))
    (hrr : rr β = 1) :
    let b := total 6 (fun a => if (H a).natAbs = 5 then (1 : Int) else 0)
    let c := total 6 (fun a => if (H a).natAbs = 3 then (1 : Int) else 0)
    8 ≤ b + c ∧ (b + c) % 2 = 0 := by
  intro b c
  have hMM : (8 : Int) * 8 = many 6 * rr β := by rw [hrr]; decide
  have hall_perp (u : W 6) : perp β u = true := by
    rw [perp_spec]; intro e he
    if he0 : e = zero 6 then
      subst he0; exact dot_zero_right 6 u
    else
      exfalso
      have h2 : bind (rad β (zero 6)) + bind (rad β e) ≤ total 6 (fun d => bind (rad β d)) := by
        have hpt (d : W 6) :
            hits (zero 6) d * bind (rad β d) + hits e d * bind (rad β d) ≤ bind (rad β d) := by
          unfold hits
          if h0 : zero 6 = d then
            have hne : ¬ e = d := fun h => he0 (h.trans h0.symm)
            simp [h0, hne]
          else if h1 : e = d then
            simp [h0, h1]
          else
            simp [h0, h1]; exact ind_nonneg _
        have hm := total_mono 6 _ _ hpt
        rw [total_add, select 6 (zero 6), select 6 e] at hm; exact hm
      change bind (rad β (zero 6)) + bind (rad β e) ≤ rr β at h2
      rw [rad_zero β, he, hrr] at h2; simp [Balanced242Plateau.ind] at h2
  -- Every hyperplane `secPt 5 u d` has rank 4 (`rr = 2`), hence `∑ exc35 ≥ 2` and even.
  have hhyp (u : W 6) (hu : u ≠ zero 6) (d : Bool) :
      2 ≤ total 5 (fun a => exc35 (H (secPt 5 u d a))) ∧
      total 5 (fun a => exc35 (H (secPt 5 u d a))) % 2 = 0 := by
    let βd : W 5 → Bool := fun a => β (secPt 5 u d a)
    have hcd : Cube βd := sec_cube β hc u d
    have hplat (y : W 5) :
        transform (fun a => sign (βd a)) y = 0 ∨
        transform (fun a => sign (βd a)) y = 8 ∨
        transform (fun a => sign (βd a)) y = -8 :=
      (section_levels β hc u hu d 8 hMM y).1 (hall_perp u)
    have hrr5 : rr βd = 2 := by
      have h := rr_from_plateau βd hcd 8 hplat
      have hm : many 5 = 32 := by decide
      rw [hm] at h; omega
    have hspec5 (a : W 5) : transform (secFun 5 u d G) a = 2 * H (secPt 5 u d a) := by
      rw [← sec_transform 5 u hu d G a, hspec]
    exact flat5_rank4_exc35 (secFun 5 u d G) (fun a => H (secPt 5 u d a)) hspec5
      (fun a => hH (secPt 5 u d a)) βd hcd (fun a => hph (secPt 5 u d a)) hrr5
  have hbc : b + c = total 6 (fun a => exc35 (H a)) := (total_exc35_eq_bc H).symm
  have heven : (b + c) % 2 = 0 := by
    have hu0 : (true, zero 5) ≠ zero 6 := fun h => Bool.noConfusion (Prod.mk.inj h).1
    have hsp := sec_sum 5 (true, zero 5) hu0 (fun a => exc35 (H a))
    have h0 := (hhyp _ hu0 false).2
    have h1 := (hhyp _ hu0 true).2
    rw [hbc, hsp]; omega
  have hge8 : 8 ≤ b + c := by
    if h8 : 8 ≤ b + c then exact h8
    else
      exfalso
      let P (a : W 6) : Bool := decide ((H a).natAbs = 3 ∨ (H a).natAbs = 5)
      have hP (a : W 6) : bind (P a) = exc35 (H a) := by
        unfold Balanced242Plateau.ind P exc35
        if h : (H a).natAbs = 3 ∨ (H a).natAbs = 5 then simp [h] else simp [h]
      have hle6 : total 6 (fun a => bind (P a)) ≤ 6 := by
        rw [funext hP, ← hbc]; omega
      let ⟨⟨u, d⟩, hu, hmiss⟩ := exists_missing_hyperplane P hle6
      have hzero : total 5 (fun a => exc35 (H (secPt 5 u d a))) = 0 := by
        have hz (a : W 5) : exc35 (H (secPt 5 u d a)) = 0 := by
          rw [← hP, hmiss a]; rfl
        rw [funext hz, total_zero]
      have hge2 := (hhyp u hu d).1
      omega
  exact ⟨hge8, heven⟩

/-! ## Step 4: 7-variable rank-4 (`y + z ≥ 8`) and rank-6 (`y + z ≥ 16`) bounds -/

/-- `replay.py`'s `half` rank-4 quartic bound: `8 ≤ y + z` and `2 ∣ (y + z)`. -/
theorem half_yz_ge_8 (D H : W 7 → Int) (hspec : ∀ a, transform D a = 2 * H a)
    (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7)
    (β : W 7 → Bool) (hc : Cube β) (hph : ∀ a, phase (H a) = sign (β a))
    (hrr : rr β = 8) :
    let y := total 7 (fun a => if (H a).natAbs = 5 then (1 : Int) else 0)
    let z := total 7 (fun a => if (H a).natAbs = 3 then (1 : Int) else 0)
    8 ≤ y + z ∧ (y + z) % 2 = 0 := by
  intro y z
  obtain ⟨u, hu, hnp⟩ := find_non_perp β (by omega)
  have hMM : (32 : Int) * 32 = many 7 * rr β := by rw [hrr]; decide
  have hside (d : Bool) :
      4 ≤ total 6 (fun a => exc35 (H (secPt 6 u d a))) ∧
      total 6 (fun a => exc35 (H (secPt 6 u d a))) % 2 = 0 := by
    let βd : W 6 → Bool := fun a => β (secPt 6 u d a)
    have hcd : Cube βd := sec_cube β hc u d
    have hplat (y : W 6) :
        transform (fun a => sign (βd a)) y = 0 ∨
        transform (fun a => sign (βd a)) y = 16 ∨
        transform (fun a => sign (βd a)) y = -16 := by
      have hlv := (section_levels β hc u hu d 32 hMM y).2 hnp
      change 2 * transform (fun a => sign (βd a)) y = 0 ∨
        2 * transform (fun a => sign (βd a)) y = 32 ∨
        2 * transform (fun a => sign (βd a)) y = -32 at hlv
      rcases hlv with h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    have hrr6 : rr βd = 4 := by
      have h := rr_from_plateau βd hcd 16 hplat
      have hm : many 6 = 64 := by decide
      rw [hm] at h; omega
    have hspec6 (a : W 6) : transform (secFun 6 u d D) a = 2 * H (secPt 6 u d a) := by
      rw [← sec_transform 6 u hu d D a, hspec]
    have h6 := six_bc_ge_4 (secFun 6 u d D) (fun a => H (secPt 6 u d a)) hspec6
      (fun a => hH (secPt 6 u d a)) βd hcd (fun a => hph (secPt 6 u d a)) hrr6
    dsimp only at h6
    rw [total_exc35_eq_bc (fun a => H (secPt 6 u d a))]
    exact h6
  have hsp := sec_sum 6 u hu (fun a => exc35 (H a))
  have h0 := hside false
  have h1 := hside true
  have hyz : y + z = total 7 (fun a => exc35 (H a)) := (total_exc35_eq_bc H).symm
  rw [hyz, hsp]
  exact ⟨by omega, by omega⟩

/-- `replay.py`'s `half` rank-6 quartic bound: `16 ≤ y + z` and `2 ∣ (y + z)`. -/
theorem half_yz_ge_16 (D H : W 7 → Int) (hspec : ∀ a, transform D a = 2 * H a)
    (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7)
    (β : W 7 → Bool) (hc : Cube β) (hph : ∀ a, phase (H a) = sign (β a))
    (hrr : rr β = 2) :
    let y := total 7 (fun a => if (H a).natAbs = 5 then (1 : Int) else 0)
    let z := total 7 (fun a => if (H a).natAbs = 3 then (1 : Int) else 0)
    16 ≤ y + z ∧ (y + z) % 2 = 0 := by
  intro y z
  obtain ⟨u, hu, hnp⟩ := find_non_perp β (by omega)
  have hMM : (16 : Int) * 16 = many 7 * rr β := by rw [hrr]; decide
  have hside (d : Bool) :
      8 ≤ total 6 (fun a => exc35 (H (secPt 6 u d a))) ∧
      total 6 (fun a => exc35 (H (secPt 6 u d a))) % 2 = 0 := by
    let βd : W 6 → Bool := fun a => β (secPt 6 u d a)
    have hcd : Cube βd := sec_cube β hc u d
    have hplat (y : W 6) :
        transform (fun a => sign (βd a)) y = 0 ∨
        transform (fun a => sign (βd a)) y = 8 ∨
        transform (fun a => sign (βd a)) y = -8 := by
      have hlv := (section_levels β hc u hu d 16 hMM y).2 hnp
      change 2 * transform (fun a => sign (βd a)) y = 0 ∨
        2 * transform (fun a => sign (βd a)) y = 16 ∨
        2 * transform (fun a => sign (βd a)) y = -16 at hlv
      rcases hlv with h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    have hrr6 : rr βd = 1 := by
      have h := rr_from_plateau βd hcd 8 hplat
      have hm : many 6 = 64 := by decide
      rw [hm] at h; omega
    have hspec6 (a : W 6) : transform (secFun 6 u d D) a = 2 * H (secPt 6 u d a) := by
      rw [← sec_transform 6 u hu d D a, hspec]
    have h6 := six_bc_ge_8 (secFun 6 u d D) (fun a => H (secPt 6 u d a)) hspec6
      (fun a => hH (secPt 6 u d a)) βd hcd (fun a => hph (secPt 6 u d a)) hrr6
    dsimp only at h6
    rw [total_exc35_eq_bc (fun a => H (secPt 6 u d a))]
    exact h6
  have hsp := sec_sum 6 u hu (fun a => exc35 (H a))
  have h0 := hside false
  have h1 := hside true
  have hyz : y + z = total 7 (fun a => exc35 (H a)) := (total_exc35_eq_bc H).symm
  rw [hyz, hsp]
  exact ⟨by omega, by omega⟩

end Balanced242Quartic

#print axioms Balanced242Quartic.half_mass_div8
#print axioms Balanced242Quartic.flat4_exc35_odd
#print axioms Balanced242Quartic.flat5_exc35_even
#print axioms Balanced242Quartic.flat5_rank4_exc35
#print axioms Balanced242Quartic.six_bc_ge_4
#print axioms Balanced242Quartic.six_bc_ge_8
#print axioms Balanced242Quartic.half_yz_ge_8
#print axioms Balanced242Quartic.half_yz_ge_16
