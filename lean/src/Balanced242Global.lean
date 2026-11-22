/-
  The pair-system hypotheses hdrop and hsec, derived from the halves.

  Global phase bits beta8 = bt(hi/4) are cubic-free, so the phase has radical size
  rr in {1, 4, 16, 64, 256}, i.e. polar rank r in {8, 6, 4, 2, 0}.  Rank-drop directions are
  w in R^perp, exactly 2^r - 1 of them (`hdrop_of`), and each hyperplane is a 7-variable
  section with phase rank secRank r d (`levels_side`).  Given the enumeration claims for
  single sections (`SectionEnum`), every hyperplane profile is admissible (`hsec_of`).
-/
import Balanced242Rank
import Balanced242Pair

namespace Balanced242Global
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support
open Balanced242Reduction (cnt low nz clsA clsB clsC hi_values pa pb pc sx sy sz low_le_cnt
  low_nonneg cnt_nonneg nz_total)
open Balanced242Pair (admissible half secRank inRange testBit factIndex exclAll excl6)
open Balanced242SectionFacts (U hi_U secD secH secCnt secD_bound secH_spec secH_odd
  low_eq_secCnt cnt_split hyperplane_0b0 hyperplane_mass t7_sum secD_sq_even point_le_total)
open Balanced242Hyperplane (secPt)
open Balanced242Plateau (Cube cube_of_spec bt phase_bt sq_cases)
open Balanced242Rank (good perp rr rr_good rr_perp rr_pos spec_good section_levels perp_spec)

local notation "phase" => Balanced242Section0320.phase
local notation "bind" => Balanced242Plateau.ind

/-- The enumeration claims (`sel`, `check_high_sections`, deferred MILP) for one 7-variable
    section: a table D with |D| <= 2 and even energy whose transform is 2H, H odd with
    |H| <= 7.  Profiles count |H| = 1, 5, 3. -/
def SectionEnum : Prop := ∀ (D H : W 7 → Int),
  (∀ y, -2 ≤ D y ∧ D y ≤ 2) → (∀ a, transform D a = 2 * H a) →
  (∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7) → total 7 (fun y => D y * D y) % 2 = 0 →
  ∀ x y z : Nat,
    (x : Int) = total 7 (fun a => if (H a).natAbs = 1 then 1 else 0) →
    (y : Int) = total 7 (fun a => if (H a).natAbs = 5 then 1 else 0) →
    (z : Int) = total 7 (fun a => if (H a).natAbs = 3 then 1 else 0) →
    88 ≤ 6 * x + 3 * y + 5 * z ∧ 19 ≤ x + y + z ∧
    (inRange x z (6 * x + 3 * y + 5 * z) &&
      testBit exclAll (factIndex x z (6 * x + 3 * y + 5 * z))) = false ∧
    ((∀ v, transform (fun a => phase (H a)) v = 0 ∨
        transform (fun a => phase (H a)) v = 16 ∨
        transform (fun a => phase (H a)) v = -16) →
      (inRange x z (6 * x + 3 * y + 5 * z) &&
        testBit excl6 (factIndex x z (6 * x + 3 * y + 5 * z))) = false)

/-- The T7 bound for a section whose phase has a given plateau height. -/
theorem t7_of_plateau (D H : W 7 → Int) (hD : ∀ y, -2 ≤ D y ∧ D y ≤ 2)
    (hspec : ∀ a, transform D a = 2 * H a) (m : Int) (hm : m = 16 ∨ m = 32 ∨ m = 64 ∨ m = 128)
    (hplat : ∀ y, transform (fun a => phase (H a)) y = 0 ∨
      transform (fun a => phase (H a)) y = m ∨ transform (fun a => phase (H a)) y = -m) :
    -16384 ≤ m * total 7 (fun a => phase (H a) * H a) ∧
      m * total 7 (fun a => phase (H a) * H a) ≤ 16384 := by
  let q : W 7 → Int := fun a => phase (H a)
  have hm128 : many 7 = 128 := by decide
  have F1 (a : W 7) : q a * q a = 1 := by
    show phase (H a) * phase (H a) = 1
    unfold Balanced242Section0320.phase
    by_cases h : H a % 4 = 1
    · rw [if_pos h]; decide
    · rw [if_neg h]; decide
  have S3 : total 7 (fun y => transform q y * transform q y) = 16384 := by
    rw [Balanced242Section0320.parseval]; simp only [F1, total_const, hm128]; decide
  have dual : total 7 (fun y => D y * transform q y) = 2 * total 7 (fun a => q a * H a) := by
    rw [← Balanced242Section0320.duality, ← total_scale]
    apply congrArg (total 7); funext a; rw [hspec, Int.mul_left_comm]
  have up (y : W 7) : m * (D y * transform q y) ≤ 2 * (transform q y * transform q y) ∧
      -m * (D y * transform q y) ≤ 2 * (transform q y * transform q y) := by
    have hd : D y = -2 ∨ D y = -1 ∨ D y = 0 ∨ D y = 1 ∨ D y = 2 := by have := hD y; omega
    rcases hm with hm | hm | hm | hm <;> subst hm <;>
      rcases hplat y with h | h | h <;> change transform q y = _ at h <;> rw [h] <;>
      rcases hd with d | d | d | d | d <;> rw [d] <;> decide
  have s1 := total_mono 7 _ _ (fun y => (up y).1)
  have s2 := total_mono 7 _ _ (fun y => (up y).2)
  simp only [total_scale] at s1 s2
  rw [S3, dual] at s1 s2
  generalize total 7 (fun a => q a * H a) = T at s1 s2
  have h1 : m * (2 * T) = 2 * (m * T) := Int.mul_left_comm m 2 T
  have h2 : -m * (2 * T) = -(2 * (m * T)) := by rw [Int.neg_mul, h1]
  rw [h1] at s1; rw [h2] at s2
  change -16384 ≤ m * T ∧ m * T ≤ 16384
  exact ⟨by omega, by omega⟩

/-- Assemble `half` from its component facts. -/
theorem half_true (x y z s : Nat) (h88 : 88 ≤ 6 * x + 3 * y + 5 * z)
    (h8 : (6 * x + 3 * y + 5 * z) % 8 = 0) (h19 : 19 ≤ x + y + z) (hs : s ≤ 6)
    (ht7 : (-896 + 8 * (x : Int) + 12 * (y : Int) + 4 * (z : Int)).natAbs ≤ 128 * 2 ^ (s / 2))
    (h0 : x = 0 → z = 0 → y = 80)
    (hA : (inRange x z (6 * x + 3 * y + 5 * z) &&
      testBit exclAll (factIndex x z (6 * x + 3 * y + 5 * z))) = false)
    (h6 : s = 6 → (inRange x z (6 * x + 3 * y + 5 * z) &&
      testBit excl6 (factIndex x z (6 * x + 3 * y + 5 * z))) = false) :
    half x y z s = true := by
  have e6 : (6 * x + 3 * y + 5 * z == 96 && x + z == 0) = false := by
    by_cases hxz : x + z = 0
    · have : y = 80 := h0 (by omega) (by omega)
      have : 6 * x + 3 * y + 5 * z ≠ 96 := by omega
      simp [this]
    · simp [hxz]
  have e8 : (s == 6 && inRange x z (6 * x + 3 * y + 5 * z) &&
      testBit excl6 (factIndex x z (6 * x + 3 * y + 5 * z))) = false := by
    by_cases h : s = 6
    · have := h6 h; rw [Bool.and_assoc, this]; simp
    · simp [h]
  show (decide (88 ≤ 6 * x + 3 * y + 5 * z) && (6 * x + 3 * y + 5 * z) % 8 == 0 &&
    decide (19 ≤ x + y + z) && decide (s ≤ 6) &&
    decide ((-896 + 8 * (x : Int) + 12 * (y : Int) + 4 * (z : Int)).natAbs ≤ 128 * 2 ^ (s / 2)) &&
    !(6 * x + 3 * y + 5 * z == 96 && x + z == 0) &&
    !(inRange x z (6 * x + 3 * y + 5 * z) && testBit exclAll (factIndex x z (6 * x + 3 * y + 5 * z))) &&
    !(s == 6 && inRange x z (6 * x + 3 * y + 5 * z) &&
      testBit excl6 (factIndex x z (6 * x + 3 * y + 5 * z)))) = true
  rw [decide_eq_true h88, decide_eq_true h19, decide_eq_true hs, decide_eq_true ht7, e6, hA, e8]
  simp [h8]

/-! ## Global objects of the halves -/

def H8 (f g : Half) (a : W 8) : Int := hi f g a / 4
def β8 (f g : Half) (a : W 8) : Bool := bt (H8 f g a)

section
variable (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)

include res in
theorem spec8 (a : W 8) : transform (U f g) a = 2 * H8 f g a := by
  have h1 := hi_U f g a; have h2 := res a; unfold H8; omega

include res in
theorem odd8 (a : W 8) : H8 f g a % 2 = 1 := by unfold H8; have := res a; omega

include res in
theorem cube8 : Cube (β8 f g) := cube_of_spec (U f g) (H8 f g) (spec8 f g res) (odd8 f g res)

include res in
theorem sec_phase (w : W 8) (c : Bool) :
    (fun a => phase (secH f g w c a)) = fun a => sign (β8 f g (secPt 7 w c a)) := by
  funext a; exact phase_bt _ (secH_odd f g res w c a)

set_option maxRecDepth 100000 in
theorem divisors256_mem : ∀ r : Nat, r < 257 → 256 % r = 0 →
    r ∈ [0, 1, 2, 4, 8, 16, 32, 64, 128, 256] := by decide

set_option maxRecDepth 100000 in
theorem levels256 (R C : Int) (h : R * C = 256) (r1 : 1 ≤ R) (c0 : 0 ≤ C) (z : Int)
    (hz : z * z = 256 * R) :
    (R = 1 ∧ C = 256) ∨ (R = 4 ∧ C = 64) ∨ (R = 16 ∧ C = 16) ∨ (R = 64 ∧ C = 4) ∨
      (R = 256 ∧ C = 1) := by
  obtain ⟨R', rfl⟩ : ∃ R' : Nat, R = R' := ⟨R.toNat, by omega⟩
  obtain ⟨C', rfl⟩ : ∃ C' : Nat, C = C' := ⟨C.toNat, by omega⟩
  have hRC : R' * C' = 256 := by exact_mod_cast h
  have C0 : C' ≠ 0 := by intro h; rw [h] at hRC; simp at hRC
  have Rle : R' ≤ 256 := by
    have := Nat.le_mul_of_pos_right R' (Nat.pos_of_ne_zero C0); omega
  have Rdvd : 256 % R' = 0 := by rw [← hRC]; exact Nat.mul_mod_right R' C'
  have hM : z.natAbs * z.natAbs = 256 * R' := by
    have := congrArg Int.natAbs hz
    rw [Int.natAbs_mul] at this; rw [this]; simp [Int.natAbs_mul]
  have Mle : z.natAbs < 257 := by
    false_or_by_contra
    have := Nat.mul_le_mul (Nat.le_of_not_lt ‹_›) (Nat.le_of_not_lt ‹_›)
    omega
  generalize z.natAbs = M at hM Mle
  have hmem := divisors256_mem R' (by omega) Rdvd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h <;> subst h
  · omega
  · left; constructor <;> omega
  · exact absurd hM (by revert M; decide)
  · right; left; constructor <;> omega
  · exact absurd hM (by revert M; decide)
  · right; right; left; constructor <;> omega
  · exact absurd hM (by revert M; decide)
  · right; right; right; left; constructor <;> omega
  · exact absurd hM (by revert M; decide)
  · right; right; right; right; constructor <;> omega

def cntGood : Int := total 8 (fun y => bind (good (β8 f g) y))
def cntPerp : Int := total 8 (fun y => bind (perp (β8 f g) y))

include res in
theorem global_levels :
    (rr (β8 f g) = 1 ∧ cntGood f g = 256) ∨ (rr (β8 f g) = 4 ∧ cntGood f g = 64) ∨
    (rr (β8 f g) = 16 ∧ cntGood f g = 16) ∨ (rr (β8 f g) = 64 ∧ cntGood f g = 4) ∨
    (rr (β8 f g) = 256 ∧ cntGood f g = 1) := by
  have hrc := rr_good (β8 f g) (cube8 f g res)
  have h256 : many 8 = 256 := by decide
  rw [h256] at hrc
  have r1 := rr_pos (β8 f g)
  have c0 : 0 ≤ cntGood f g :=
    Balanced242Plateau.total_nonneg' _ (fun y => Balanced242Plateau.ind_nonneg _)
  cases hb : (worlds 8).any (good (β8 f g))
  · exfalso
    rw [List.any_eq_false] at hb
    have z : cntGood f g = 0 := by
      unfold cntGood
      have : (fun y => bind (good (β8 f g) y)) = fun _ => 0 := by
        funext y
        have := hb y (all_worlds 8 y)
        cases h : good (β8 f g) y
        · rfl
        · exact absurd h this
      rw [this, total_zero]
    change rr (β8 f g) * cntGood f g = 256 at hrc
    rw [z, Int.mul_zero] at hrc; omega
  · rw [List.any_eq_true] at hb
    obtain ⟨y, _, hy⟩ := hb
    have sq := spec_good (β8 f g) (cube8 f g res) y
    rw [hy, h256] at sq
    simp only [Balanced242Plateau.ind, if_true, Int.mul_one] at sq
    exact levels256 _ _ hrc r1 c0 _ sq

theorem perp_zero : perp (β8 f g) (zero 8) = true := by
  rw [perp_spec]; intro e _; exact dot_zero 8 e

include res in
theorem cnt_perp_eq : cntPerp f g = cntGood f g := by
  have a := rr_perp (β8 f g)
  have b := rr_good (β8 f g) (cube8 f g res)
  have r1 := rr_pos (β8 f g)
  change rr (β8 f g) * cntPerp f g = many 8 at a
  change rr (β8 f g) * cntGood f g = many 8 at b
  rw [← b] at a
  exact Int.eq_of_mul_eq_mul_left (by omega) a

include res in
/-- Rank-drop count: 2^r - 1 nonzero directions lie in R^perp. -/
theorem drop_count : total 8 (fun w => nz w * (if perp (β8 f g) w then 1 else 0)) =
    cntGood f g - 1 := by
  rw [nz_total, ← cnt_perp_eq f g res, perp_zero]
  rfl

theorem two_perp (w : W 8) (hw : w ≠ zero 8) (hp : perp (β8 f g) w = true) : 2 ≤ cntPerp f g := by
  unfold cntPerp
  have e := nz_total (n := 8) (fun y => bind (perp (β8 f g) y))
  have pt := point_le_total 8 (fun y => nz y * bind (perp (β8 f g) y))
    (fun y => by
      show 0 ≤ nz y * bind (perp (β8 f g) y)
      unfold nz Balanced242Plateau.ind; split <;> split <;> decide) w
  have one : nz w * bind (perp (β8 f g) w) = 1 := by
    simp [nz, hw, hp, Balanced242Plateau.ind]
  rw [one] at pt
  rw [perp_zero] at e
  have b1 : bind true = 1 := rfl
  rw [b1] at e
  omega

theorem all_perp (h : cntPerp f g = 256) (w : W 8) : perp (β8 f g) w = true := by
  cases hp : perp (β8 f g) w
  · exfalso
    have pt := point_le_total 8 (fun y => 1 - bind (perp (β8 f g) y))
      (fun y => by
        show 0 ≤ 1 - bind (perp (β8 f g) y)
        unfold Balanced242Plateau.ind; split <;> decide) w
    simp only [hp, Balanced242Plateau.ind, Bool.false_eq_true, if_false] at pt
    rw [total_sub, total_const] at pt
    change 1 - 0 ≤ many 8 * 1 - cntPerp f g at pt
    rw [h] at pt
    have : many 8 = 256 := by decide
    omega
  · rfl

end


section
variable (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)

include res cap in
theorem cnt_abs (w : W 8) (c : Bool) (P : W 8 → Bool) (k j : Nat)
    (hP : ∀ a, P a = ((hi f g a).natAbs == k)) (hk : ∀ h : Int, h % 8 = 4 → h.natAbs ≤ 28 →
      ((h.natAbs == k) = true ↔ (h / 4).natAbs = j)) :
    secCnt P w c = total 7 (fun a => if (secH f g w c a).natAbs = j then 1 else 0) := by
  unfold secCnt
  apply congrArg (total 7); funext a
  unfold Balanced242Reduction.ind secH
  have := hk _ (res (secPt 7 w c a)) (cap (secPt 7 w c a))
  rw [hP]
  by_cases h : ((hi f g (secPt 7 w c a)).natAbs == k) = true
  · rw [if_pos h, if_pos (this.1 h)]
  · rw [if_neg h, if_neg (fun e => h (this.2 e))]

include res cap in
theorem side_half (ht : agreements f g % 2 = 0) (enum : SectionEnum) (w : W 8)
    (hw : w ≠ zero 8) (c : Bool) (X Y Z s : Nat)
    (hX : (X : Int) = secCnt (clsA f g) w c) (hY : (Y : Int) = secCnt (clsB f g) w c)
    (hZ : (Z : Int) = secCnt (clsC f g) w c) (m : Int)
    (hms : (m = 16 ∧ s = 6) ∨ (m = 32 ∧ s = 4) ∨ (m = 64 ∧ s = 2) ∨ (m = 128 ∧ s = 0))
    (hplat : ∀ y, transform (fun a => phase (secH f g w c a)) y = 0 ∨
      transform (fun a => phase (secH f g w c a)) y = m ∨
      transform (fun a => phase (secH f g w c a)) y = -m) :
    half X Y Z s = true := by
  have cA := cnt_abs f g res cap w c (clsA f g) 4 1 (fun a => rfl) (fun h h1 h2 => by
    simp only [beq_iff_eq]; exact ⟨fun e => by omega, fun e => by omega⟩)
  have cB := cnt_abs f g res cap w c (clsB f g) 20 5 (fun a => rfl) (fun h h1 h2 => by
    simp only [beq_iff_eq]; exact ⟨fun e => by omega, fun e => by omega⟩)
  have cC := cnt_abs f g res cap w c (clsC f g) 12 3 (fun a => rfl) (fun h h1 h2 => by
    simp only [beq_iff_eq]; exact ⟨fun e => by omega, fun e => by omega⟩)
  have hval (a : W 7) : secH f g w c a % 2 = 1 ∧ (secH f g w c a).natAbs ≤ 7 := by
    refine ⟨secH_odd f g res w c a, ?_⟩
    unfold secH; have := res (secPt 7 w c a); have := cap (secPt 7 w c a); omega
  obtain ⟨h88, h19, hA, h6⟩ := enum (secD f g w c) (secH f g w c) (secD_bound f g w c)
    (secH_spec f g res w hw c) hval (secD_sq_even f g w hw c ht) X Y Z
    (hX.trans cA) (hY.trans cB) (hZ.trans cC)
  have hm8 := hyperplane_mass f g res cap w hw c ht
  rw [← hX, ← hY, ← hZ] at hm8
  have hm : m = 16 ∨ m = 32 ∨ m = 64 ∨ m = 128 := by
    rcases hms with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have t7 := t7_of_plateau (secD f g w c) (secH f g w c) (secD_bound f g w c)
    (secH_spec f g res w hw c) m hm hplat
  rw [t7_sum f g res cap w c, ← hX, ← hY, ← hZ] at t7
  apply half_true X Y Z s h88 (by omega) h19 (by omega)
  · obtain ⟨t1, t2⟩ := t7
    rcases hms with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [show (2:Nat) ^ (6/2) = 8 from rfl, show (2:Nat) ^ (4/2) = 4 from rfl,
        show (2:Nat) ^ (2/2) = 2 from rfl, show (2:Nat) ^ (0/2) = 1 from rfl] <;> omega
  · intro hx hz
    have := hyperplane_0b0 f g res cap w hw c (by rw [← hX, hx]; rfl) (by rw [← hZ, hz]; rfl)
    rw [← hY] at this; omega
  · exact hA
  · intro h; apply h6
    have : m = 16 := by omega
    rw [← this]; exact hplat

include res in
theorem side_plateau (w : W 8) (hw : w ≠ zero 8) (c : Bool) (M : Int)
    (hMM : M * M = many 8 * rr (β8 f g)) (m : Int)
    (hm : (perp (β8 f g) w = true ∧ m = M) ∨ (perp (β8 f g) w = false ∧ 2 * m = M)) (y : W 7) :
    transform (fun a => phase (secH f g w c a)) y = 0 ∨
      transform (fun a => phase (secH f g w c a)) y = m ∨
      transform (fun a => phase (secH f g w c a)) y = -m := by
  rw [sec_phase f g res w c]
  have L := section_levels (β8 f g) (cube8 f g res) w hw c M hMM y
  rcases hm with ⟨hp, rfl⟩ | ⟨hp, hm⟩
  · exact L.1 hp
  · have := L.2 hp; omega

include res cap in
theorem dir_admissible (ht : agreements f g % 2 = 0) (enum : SectionEnum) (r : Nat) (M : Int)
    (hrM : (r = 8 ∧ M = 16 ∧ rr (β8 f g) = 1) ∨ (r = 6 ∧ M = 32 ∧ rr (β8 f g) = 4) ∨
      (r = 4 ∧ M = 64 ∧ rr (β8 f g) = 16) ∨ (r = 2 ∧ M = 128 ∧ rr (β8 f g) = 64) ∨
      (r = 0 ∧ M = 256 ∧ rr (β8 f g) = 256))
    (hcp : cntPerp f g = 2 ^ r) (w : W 8) (hw : w ≠ zero 8) :
    admissible (pa f g) (pb f g) (pc f g) r (sx f g w) (sy f g w) (sz f g w)
      (perp (β8 f g) w) = true := by
  have hMM : M * M = many 8 * rr (β8 f g) := by
    have : many 8 = 256 := by decide
    rw [this]; rcases hrM with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;>
      rw [h1, h2] <;> decide
  -- section rank and plateau height for this direction
  obtain ⟨m, hm, hms⟩ : ∃ m : Int,
      ((perp (β8 f g) w = true ∧ m = M) ∨ (perp (β8 f g) w = false ∧ 2 * m = M)) ∧
      ((m = 16 ∧ secRank r (perp (β8 f g) w) = 6) ∨ (m = 32 ∧ secRank r (perp (β8 f g) w) = 4) ∨
       (m = 64 ∧ secRank r (perp (β8 f g) w) = 2) ∨ (m = 128 ∧ secRank r (perp (β8 f g) w) = 0)) := by
    cases hp : perp (β8 f g) w
    · rcases hrM with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
      · exact absurd (all_perp f g (by rw [hcp]; rfl) w) (by rw [hp]; decide)
      · exact ⟨16, Or.inr ⟨rfl, rfl⟩, by simp [secRank]⟩
      · exact ⟨32, Or.inr ⟨rfl, rfl⟩, by simp [secRank]⟩
      · exact ⟨64, Or.inr ⟨rfl, rfl⟩, by simp [secRank]⟩
      · exact ⟨128, Or.inr ⟨rfl, rfl⟩, by simp [secRank]⟩
    · rcases hrM with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
      · exact ⟨16, Or.inl ⟨rfl, rfl⟩, by simp [secRank]⟩
      · exact ⟨32, Or.inl ⟨rfl, rfl⟩, by simp [secRank]⟩
      · exact ⟨64, Or.inl ⟨rfl, rfl⟩, by simp [secRank]⟩
      · exact ⟨128, Or.inl ⟨rfl, rfl⟩, by simp [secRank]⟩
      · have := two_perp f g w hw hp; rw [hcp] at this; exact absurd this (by decide)
  have plat (c : Bool) := side_plateau f g res w hw c M hMM m hm
  have l0 := low_nonneg (clsA f g) w
  have l1 := low_nonneg (clsB f g) w
  have l2 := low_nonneg (clsC f g) w
  have m0 := low_le_cnt (clsA f g) w
  have m1 := low_le_cnt (clsB f g) w
  have m2 := low_le_cnt (clsC f g) w
  have eA := low_eq_secCnt w hw (clsA f g)
  have eB := low_eq_secCnt w hw (clsB f g)
  have eC := low_eq_secCnt w hw (clsC f g)
  have sA := cnt_split w hw (clsA f g)
  have sB := cnt_split w hw (clsB f g)
  have sC := cnt_split w hw (clsC f g)
  have hlo := side_half f g res cap ht enum w hw false (sx f g w) (sy f g w) (sz f g w)
    (secRank r (perp (β8 f g) w)) (by unfold sx; omega) (by unfold sy; omega) (by unfold sz; omega)
    m hms (plat false)
  have hhi := side_half f g res cap ht enum w hw true (pa f g - sx f g w) (pb f g - sy f g w)
    (pc f g - sz f g w) (secRank r (perp (β8 f g) w))
    (by unfold pa sx Balanced242Reduction.cnt at *; omega)
    (by unfold pb sy Balanced242Reduction.cnt at *; omega)
    (by unfold pc sz Balanced242Reduction.cnt at *; omega)
    m hms (plat true)
  have h2 : (!perp (β8 f g) w || decide (2 ≤ r)) = true := by
    cases hp : perp (β8 f g) w
    · rfl
    · rcases hm with ⟨-, rfl⟩ | ⟨hp', -⟩
      · rcases hrM with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -, -⟩
        all_goals first | rfl | (have := two_perp f g w hw hp; rw [hcp] at this; exact absurd this (by decide))
      · rw [hp] at hp'; exact absurd hp' (by decide)
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨h2, ?_⟩, ?_⟩, ?_⟩, hlo⟩, hhi⟩
  · unfold sx pa Balanced242Reduction.cnt at *; omega
  · unfold sy pb Balanced242Reduction.cnt at *; omega
  · unfold sz pc Balanced242Reduction.cnt at *; omega

end

end Balanced242Global

#print axioms Balanced242Global.global_levels
#print axioms Balanced242Global.drop_count
#print axioms Balanced242Global.half_true
#print axioms Balanced242Global.dir_admissible
