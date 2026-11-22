/-
  End-to-end verified Farkas & Anchor-Pair refutation engine for global rank-8 profiles
  (`t ≥ 94`), bridging actual 9-variable Boolean functions (`f, g : Half` with `res`, `hicap`,
  `agreements f g = t`, `rr (β8 f g) = 1`) directly to exact integer certificates:

    1. `rank6_exc_closed_bound`: derives the closed-form lower bound `eminClosed M k ≤ secExc`
       directly from `Balanced242SectionBounds.rank6_exc_buckets` (matches `rank8filter.emin`
       on 100% of all 3,943 half-sections across all 18 `t = 94` / `t = 96` frontier profiles).
    2. `liftPt` & `quarter_hyperplane_counts`: proves the 2-plane four-quarter coupling —
       for any anchor `w ≠ 0` in `W 8` and quotient `v ≠ 0` in `W 7`, the lifted directions
       `u0 = liftPt 7 w v ≠ 0` and `u1 = add 8 w u0 ≠ 0` have half-counts `p00 + p10` and
       `p00 + p11`, forcing both combinations into the surviving admissible half set `both`.
    3. `farkas_refute`: generic exact-integer Farkas refutation theorem over `W n \ {0}`.
    4. `affine_cert_refute`: verifies any sparse all-degree Krawtchouk Farkas certificate
       `List (Nat × Nat × Nat × Int)` against real `(f, g)` using `Balanced242Krawtchouk`.
    5. `cond_cert_refute`: verifies any 14-row anchor-pair Farkas certificate for a fixed
       anchor `lo` (`hi = (a,b,c) - lo`), using a provably sound separable fast checker
       (`checkCondCertFast`) backed by `anchor_pair_ranks_63_64`, `six_section_jensen`,
       `six_bc_ge_4`, `six_bc_ge_8`, and `kraw_deg2_200` / `kraw_deg2_110`.
    6. `exclude_rank8_profile`: master theorem combining arbitrary peeling layers of
       anchor-pair certificates plus a final affine Krawtchouk certificate to derive `False`
       from `SectionEnumE`.
-/
import Balanced242Krawtchouk
import Balanced242LowRange

namespace Balanced242Farkas
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Hyperplane Balanced242Plateau Balanced242Rank
open Balanced242Reduction (clsA clsB clsC)
open Balanced242SectionFacts (U U_bound secD secH secD_bound secH_spec secH_odd hyperplane_0b0 secD_sq_even)
open Balanced242Global (H8 β8 odd8)
open Balanced242Rank8 (secExc sec_phase_transform rank8_secExc_sum rank8_Nplus_formula)
open Balanced242Pair (inRange testBit factIndex)
open Balanced242AnchorPair (sec_cube anchor_pair_ranks_63_64 six_section_div4 six_section_jensen)
open Balanced242Quartic (secPt_dot sec_sum half_mass_div8 six_bc_ge_4 six_bc_ge_8 half_yz_ge_16)
open Balanced242Krawtchouk (nz nz_total choose sumInt sumInt_nonneg kraw kraw_at_zero
  suppList halfCnt halfCntFalse halfCnt_add_false halfCnt_le
  kraw_triple_nonneg_and_mod kraw_even_flip kraw_triple_deg2_eq)

local notation "phase" => Balanced242Section0320.phase
local notation "bind" => Balanced242Plateau.ind

/-! ## Part 1: Closed-form arithmetic lower bound on `secExc` (`eminClosed`) -/

/-- Closed-form arithmetic lower bound on `secExc` for a rank-6 section of mass `M` and `k = x + z`. -/
def eminClosed (M k : Nat) : Nat :=
  let tau : Int := -112 + (M : Int) / 2 - 2 * (k : Int)
  let s : Int := (784 - (M : Int)) / 4
  let e1 : Int := if 0 ≤ tau then tau else 0
  let num : Int := s + 2 * tau - 61
  let e2 : Int := if 0 ≤ num then num / 4 else 0
  (if e1 ≤ e2 then e2 else e1).toNat

/-- Soundness of `eminClosed`: proved directly from `Balanced242SectionBounds.rank6_exc_buckets`. -/
theorem eminClosed_le_secExc (D H : W 7 → Int) (hD : ∀ u, -2 ≤ D u ∧ D u ≤ 2)
    (hspec : ∀ a, transform D a = 2 * H a) (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7)
    (hplat : ∀ u, transform (fun a => phase (H a)) u = 0 ∨
      transform (fun a => phase (H a)) u = 16 ∨ transform (fun a => phase (H a)) u = -16)
    (x y z : Nat)
    (hx : (x : Int) = total 7 (fun a => if (H a).natAbs = 1 then 1 else 0))
    (hy : (y : Int) = total 7 (fun a => if (H a).natAbs = 5 then 1 else 0))
    (hz : (z : Int) = total 7 (fun a => if (H a).natAbs = 3 then 1 else 0)) :
    (eminClosed (6 * x + 3 * y + 5 * z) (x + z) : Int) ≤
      secExc D (transform (fun a => phase (H a))) := by
  have hb := Balanced242SectionBounds.rank6_exc_buckets D H hD hspec hH hplat
  dsimp only at hb
  rw [← hx, ← hy, ← hz] at hb
  have h8 := half_mass_div8 D H hspec hH
  dsimp only at h8
  rw [← hx, ← hy, ← hz] at h8
  obtain ⟨hnn1, hnn2, hnn3, hnn4, hnn5, hnn6, hR, hM, htau, hene, hexc⟩ := hb
  unfold eminClosed
  dsimp only
  omega

/-! ## Part 2: Exact trust boundary `SectionEnumE` for 7-variable enumeration facts -/

/-- Lookup the logged `sel_e` lower bound for a rank-6 section `(x, y, z)` (`0` if absent). -/
def lookupBound (bounds : List (Nat × Nat × Nat × Nat)) (x y z : Nat) : Nat :=
  match bounds.find? (fun e => e.1 == x && e.2.1 == y && e.2.2.1 == z) with
  | some e => e.2.2.2
  | none => 0

/-- The sole enumeration hypothesis for rank-8 `t ≥ 94` exclusions:
    1. Every 7-variable section has `19 ≤ x + y + z` (`e ≤ 18` enumeration).
    2. No rank-6 section matches a bit set in `excl6Mask` (the 234 completed 0-hit logs).
    3. Every rank-6 section `(x, y, z)` satisfies `lookupBound eBounds x y z ≤ secExc`
       (the 59 completed `sel_e` exception-weight logs). -/
def SectionEnumE (excl6Mask : Nat) (eBounds : List (Nat × Nat × Nat × Nat)) : Prop :=
  ∀ (D H : W 7 → Int),
    (∀ u, -2 ≤ D u ∧ D u ≤ 2) →
    (∀ a, transform D a = 2 * H a) →
    (∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7) →
    total 7 (fun u => D u * D u) % 2 = 0 →
    (∀ u, transform (fun a => phase (H a)) u = 0 ∨
      transform (fun a => phase (H a)) u = 16 ∨ transform (fun a => phase (H a)) u = -16) →
    ∀ x y z : Nat,
      (x : Int) = total 7 (fun a => if (H a).natAbs = 1 then 1 else 0) →
      (y : Int) = total 7 (fun a => if (H a).natAbs = 5 then 1 else 0) →
      (z : Int) = total 7 (fun a => if (H a).natAbs = 3 then 1 else 0) →
      88 ≤ 6 * x + 3 * y + 5 * z ∧ 19 ≤ x + y + z ∧
      (inRange x z (6 * x + 3 * y + 5 * z) &&
        testBit excl6Mask (factIndex x z (6 * x + 3 * y + 5 * z))) = false ∧
      (lookupBound eBounds x y z : Int) ≤ secExc D (transform (fun a => phase (H a)))

/-! ## Part 3: Linking `suppList` / `halfCnt` / `halfCntFalse` to `total` and `secPt` -/

theorem suppList_length_eq_total {n : Nat} (P : W n → Bool) :
    ((suppList P).length : Int) = total n (fun a => bind (P a)) := by
  induction n with
  | zero =>
    show (([()] : List (W 0)).filter P).length = bind (P ())
    cases hp : P () <;> simp [List.filter, hp, Balanced242Plateau.ind]
  | succ m ih =>
    unfold suppList at ih ⊢
    show ((((worlds m).map (fun x => (false, x)) ++ (worlds m).map (fun x => (true, x))).filter P).length : Int) =
      total m (fun x => bind (P (false, x))) + total m (fun x => bind (P (true, x)))
    rw [List.filter_append, List.length_append, Int.natCast_add,
        List.filter_map, List.filter_map, List.length_map, List.length_map,
        ih (P ∘ fun x => (false, x)), ih (P ∘ fun x => (true, x))]
    rfl

private theorem filter_filter_eq {α : Type} (p q : α → Bool) :
    ∀ (L : List α), (L.filter p).filter q = L.filter (fun x => p x && q x)
  | [] => rfl
  | a :: t => by
    simp only [List.filter_cons]
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq, filter_filter_eq p q t]

theorem halfCnt_eq_total {n : Nat} (v : W n) (P : W n → Bool) :
    (halfCnt v P : Int) = total n (fun a => bind (P a && dot n v a)) := by
  unfold halfCnt suppList
  rw [filter_filter_eq]
  exact suppList_length_eq_total (fun a => P a && dot n v a)

theorem halfCntFalse_eq_total {n : Nat} (v : W n) (P : W n → Bool) :
    (halfCntFalse v P : Int) = total n (fun a => bind (P a && !(dot n v a))) := by
  unfold halfCntFalse suppList
  rw [filter_filter_eq]
  exact suppList_length_eq_total (fun a => P a && !(dot n v a))

theorem sec_suppList_eq_halfCnt {n : Nat} (w : W (n + 1)) (hw : w ≠ zero (n + 1))
    (P : W (n + 1) → Bool) :
    (suppList (fun a => P (secPt n w false a))).length = halfCntFalse w P ∧
    (suppList (fun a => P (secPt n w true a))).length = halfCnt w P := by
  have hF : total n (fun a => bind (P (secPt n w false a))) =
      total (n + 1) (fun x => bind (P x && !(dot (n + 1) w x))) := by
    rw [sec_sum n w hw]
    have h0 (a : W n) : bind (P (secPt n w false a) && !(dot (n + 1) w (secPt n w false a))) =
        bind (P (secPt n w false a)) := by
      rw [secPt_dot n w hw false a]; simp
    have h1 (a : W n) : bind (P (secPt n w true a) && !(dot (n + 1) w (secPt n w true a))) = 0 := by
      rw [secPt_dot n w hw true a]; simp [Balanced242Plateau.ind]
    rw [funext h0, funext h1, total_zero, Int.add_zero]
  have hT : total n (fun a => bind (P (secPt n w true a))) =
      total (n + 1) (fun x => bind (P x && dot (n + 1) w x)) := by
    rw [sec_sum n w hw]
    have h0 (a : W n) : bind (P (secPt n w false a) && dot (n + 1) w (secPt n w false a)) = 0 := by
      rw [secPt_dot n w hw false a]; simp [Balanced242Plateau.ind]
    have h1 (a : W n) : bind (P (secPt n w true a) && dot (n + 1) w (secPt n w true a)) =
        bind (P (secPt n w true a)) := by
      rw [secPt_dot n w hw true a]; simp
    rw [funext h0, funext h1, total_zero, Int.zero_add]
  have eF : ((suppList (fun a => P (secPt n w false a))).length : Int) = (halfCntFalse w P : Int) := by
    rw [suppList_length_eq_total, hF, ← halfCntFalse_eq_total]
  have eT : ((suppList (fun a => P (secPt n w true a))).length : Int) = (halfCnt w P : Int) := by
    rw [suppList_length_eq_total, hT, ← halfCnt_eq_total]
  exact ⟨Int.ofNat.inj eF, Int.ofNat.inj eT⟩

/-! ## Part 4: 2-Plane Four-Quarter Lifting Lemma (`liftPt`) -/

/-- Lift a quotient direction `v : W n` to `W (n+1)` by inserting `false` at the pivot bit of `w`. -/
def liftPt : (n : Nat) → W (n + 1) → W n → W (n + 1)
  | _, (true, _), v => (false, v)
  | 0, (false, _), _ => (false, ())
  | m + 1, (false, w'), (bv, v') => (bv, liftPt m w' v')

theorem liftPt_ne_zero : ∀ (n : Nat) (w : W (n + 1)), w ≠ zero (n + 1) →
    ∀ (v : W n), v ≠ zero n → liftPt n w v ≠ zero (n + 1)
  | 0, (true, _), _, (), hv => absurd rfl hv
  | 0, (false, _), hw, _, _ => absurd rfl hw
  | m + 1, (true, _), _, v, hv => fun h => hv (Prod.mk.inj h).2
  | m + 1, (false, w'), hw, (bv, v'), hv => by
    have hw' : w' ≠ zero (m + 1) := fun h => hw (by rw [h]; rfl)
    intro h0
    have hb : bv = false := (Prod.mk.inj h0).1
    have hrec : liftPt m w' v' = zero (m + 1) := (Prod.mk.inj h0).2
    subst hb
    have hv' : v' ≠ zero m := fun h => hv (by rw [h]; rfl)
    exact liftPt_ne_zero m w' hw' v' hv' hrec

theorem add_liftPt_ne_zero : ∀ (n : Nat) (w : W (n + 1)), w ≠ zero (n + 1) →
    ∀ (v : W n), add (n + 1) w (liftPt n w v) ≠ zero (n + 1)
  | 0, (true, _), _, _ => fun h => Bool.noConfusion (Prod.mk.inj h).1
  | 0, (false, _), hw, _ => absurd rfl hw
  | m + 1, (true, _), _, _ => fun h => Bool.noConfusion (Prod.mk.inj h).1
  | m + 1, (false, w'), hw, (_, v') => by
    have hw' : w' ≠ zero (m + 1) := fun h => hw (by rw [h]; rfl)
    intro h0
    exact add_liftPt_ne_zero m w' hw' v' (Prod.mk.inj h0).2

theorem liftPt_dot_secPt : ∀ (n : Nat) (w : W (n + 1)), w ≠ zero (n + 1) →
    ∀ (c : Bool) (v a : W n), dot (n + 1) (liftPt n w v) (secPt n w c a) = dot n v a
  | 0, (true, _), _, _, (), () => rfl
  | 0, (false, _), hw, _, _, _ => absurd rfl hw
  | m + 1, (true, w'), _, c, v, a => by
    rw [secPt_true]
    show xor (false && xor c (dot (m + 1) w' a)) (dot (m + 1) v a) = dot (m + 1) v a
    simp
  | m + 1, (false, w'), hw, c, (bv, v'), (ba, a') => by
    have hw' : w' ≠ zero (m + 1) := fun h => hw (by rw [h]; rfl)
    show xor (bv && ba) (dot (m + 1) (liftPt m w' v') (secPt m w' c a')) =
         xor (bv && ba) (dot m v' a')
    rw [liftPt_dot_secPt m w' hw' c v' a']

/-- 2-plane four-quarter coupling: for anchor `w ≠ 0` in `W 8` and quotient `v ≠ 0` in `W 7`,
    the lifted directions `u0 = liftPt 7 w v ≠ 0` and `u1 = add 8 w u0 ≠ 0` satisfy
      `halfCntFalse u0 P = q00 + q10`  and  `halfCntFalse u1 P = q00 + q11`. -/
theorem quarter_hyperplane_counts (P : W 8 → Bool) (w : W 8) (hw : w ≠ zero 8) (v : W 7) :
    let u0 := liftPt 7 w v
    let u1 := add 8 w u0
    let P0 := fun a => P (secPt 7 w false a)
    let P1 := fun a => P (secPt 7 w true a)
    halfCntFalse u0 P = halfCntFalse v P0 + halfCntFalse v P1 ∧
    halfCntFalse u1 P = halfCntFalse v P0 + halfCnt v P1 := by
  intro u0 u1 P0 P1
  have hu0_sum : (halfCntFalse u0 P : Int) = (halfCntFalse v P0 : Int) + (halfCntFalse v P1 : Int) := by
    rw [halfCntFalse_eq_total, halfCntFalse_eq_total, halfCntFalse_eq_total, sec_sum 7 w hw]
    congr 1
    · apply congrArg (total 7); funext a; rw [liftPt_dot_secPt 7 w hw false v a]
    · apply congrArg (total 7); funext a; rw [liftPt_dot_secPt 7 w hw true v a]
  have hu1_sum : (halfCntFalse u1 P : Int) = (halfCntFalse v P0 : Int) + (halfCnt v P1 : Int) := by
    rw [halfCntFalse_eq_total, halfCntFalse_eq_total, halfCnt_eq_total, sec_sum 7 w hw]
    congr 1
    · apply congrArg (total 7); funext a
      dsimp only [u1, u0]
      rw [dot_add, secPt_dot 7 w hw false a, liftPt_dot_secPt 7 w hw false v a]; simp
    · apply congrArg (total 7); funext a
      dsimp only [u1, u0]
      rw [dot_add, secPt_dot 7 w hw true a, liftPt_dot_secPt 7 w hw true v a]
      cases dot 7 v a <;> rfl
  exact ⟨by omega, by omega⟩

/-! ## Part 5: Generic Exact-Integer Farkas Refutation Engine -/

/-- Sum of weighted row evaluations `∑ (f, wt) ∈ rows, wt * f c`. -/
def evalWeighted {α : Type} (rows : List ((α → Int) × Int)) (c : α) : Int :=
  match rows with
  | [] => 0
  | (f, wt) :: t => wt * f c + evalWeighted t c

/-- Sum of weighted RHS targets `∑ (rhs, wt) ∈ rhss, wt * rhs`. -/
def evalRhs (rhss : List (Int × Int)) : Int :=
  match rhss with
  | [] => 0
  | (rhs, wt) :: t => wt * rhs + evalRhs t

private theorem evalWeighted_total_ge {n : Nat} {α : Type} (classify : W n → α) :
    ∀ (rows : List ((α → Int) × Int × Int)),
      (∀ r, r ∈ rows → (0 ≤ r.2.2 ∧ r.2.1 ≤ total n (fun v => nz v * r.1 (classify v))) ∨
                        total n (fun v => nz v * r.1 (classify v)) = r.2.1) →
      evalRhs (rows.map (fun r => (r.2.1, r.2.2))) ≤
        total n (fun v => nz v * evalWeighted (rows.map (fun r => (r.1, r.2.2))) (classify v))
  | [], _ => by simp [evalRhs, evalWeighted, total_zero]
  | (f, rhs, wt) :: t, h => by
    have hhead := h (f, rhs, wt) (List.Mem.head _)
    dsimp only at hhead
    have htail := evalWeighted_total_ge classify t (fun r hr => h r (List.Mem.tail _ hr))
    simp only [List.map_cons, evalRhs, evalWeighted]
    have hsplit : total n (fun v => nz v * (wt * f (classify v) +
        evalWeighted (t.map (fun r => (r.1, r.2.2))) (classify v))) =
        wt * total n (fun v => nz v * f (classify v)) +
        total n (fun v => nz v * evalWeighted (t.map (fun r => (r.1, r.2.2))) (classify v)) := by
      have hpt (v : W n) : nz v * (wt * f (classify v) +
          evalWeighted (t.map (fun r => (r.1, r.2.2))) (classify v)) =
          wt * (nz v * f (classify v)) +
          nz v * evalWeighted (t.map (fun r => (r.1, r.2.2))) (classify v) := by
        rw [Int.mul_add, Int.mul_left_comm]
      rw [funext hpt, total_add, total_scale]
    rw [hsplit]
    rcases hhead with ⟨hwt, hge⟩ | heq
    · have hm := Int.mul_le_mul_of_nonneg_left hge hwt
      omega
    · rw [heq]; omega

/-- Core Farkas refutation over `W n \ {0}`: if every nonzero direction classifies into `cols`,
    every row constraint is sound (`=` or `≥` with `wt ≥ 0`), every `c ∈ cols` has weighted sum `≤ 0`,
    and the weighted RHS is `> 0`, then `False`. -/
theorem farkas_refute {n : Nat} {α : Type} (classify : W n → α) (cols : List α)
    (hmem : ∀ v : W n, v ≠ zero n → classify v ∈ cols)
    (rows : List ((α → Int) × Int × Int))
    (hsound : ∀ r, r ∈ rows →
      (0 ≤ r.2.2 ∧ r.2.1 ≤ total n (fun v => nz v * r.1 (classify v))) ∨
      total n (fun v => nz v * r.1 (classify v)) = r.2.1)
    (hcols : ∀ c, c ∈ cols → evalWeighted (rows.map (fun r => (r.1, r.2.2))) c ≤ 0)
    (hrhs : 0 < evalRhs (rows.map (fun r => (r.2.1, r.2.2)))) : False := by
  have hge := evalWeighted_total_ge classify rows hsound
  have hle : total n (fun v => nz v * evalWeighted (rows.map (fun r => (r.1, r.2.2))) (classify v)) ≤ 0 := by
    rw [← total_zero n]
    apply total_mono n; intro v
    if hv : v = zero n then
      subst hv; simp [nz]
    else
      simp only [nz, hv, if_false, Int.one_mul]
      exact hcols (classify v) (hmem v hv)
  omega

/-! ## Part 6: Computable `six`, `halfR6`, `splits`, `affine`, and `conditional` checkers -/

abbrev Triple := Nat × Nat × Nat

/-- Lexicographic `≤` on triples matching Python's `lo <= hi`. -/
def tripleLe (p q : Triple) : Bool :=
  p.1 < q.1 || (p.1 == q.1 && (p.2.1 < q.2.1 || (p.2.1 == q.2.1 && p.2.2 ≤ q.2.2)))

def canonPair (a b c x y z : Nat) : Triple :=
  let lo : Triple := (x, y, z)
  let hi : Triple := (a - x, b - y, c - z)
  if tripleLe lo hi then lo else hi

/-- Exact 6-variable admissibility predicate (`replay.py`'s `six(p, r)` for `r ∈ {4, 6}`). -/
def sixOK (a b c r : Nat) : Bool :=
  let mass := 6 * a + 3 * b + 5 * c
  let m := b + c
  let ph : Int := -448 + 8 * (a : Int) + 12 * (b : Int) + 4 * (c : Int)
  let scale : Int := if r == 6 then 4 else 8
  let sz : Int := if r == 6 then 64 else 16
  let tau : Int := (ph / scale).natAbs
  let q : Int := tau / sz
  let j : Int := tau % sz
  mass % 4 == 0 && decide (a + b + c ≤ 64) && m % 2 == 0 &&
  decide ((if r == 6 then 8 else 4) ≤ m) &&
  ph % scale == 0 && decide (tau ≤ 4 * sz) &&
  decide ((sz - j) * (q * q) + j * ((q + 1) * (q + 1)) ≤ 196 - (mass : Int) / 2)

/-- Exact 7-variable rank-6 section admissibility predicate (`replay.py`'s `half(x, y, z, 6)` + `excl6Mask`). -/
def halfR6OK (excl6Mask : Nat) (x y z : Nat) : Bool :=
  let mass := 6 * x + 3 * y + 5 * z
  let ph : Int := -896 + 8 * (x : Int) + 12 * (y : Int) + 4 * (z : Int)
  let tau : Int := (ph / 8).natAbs
  let over : Int := if 64 ≤ tau then tau - 64 else 0
  decide (88 ≤ mass) && mass % 8 == 0 && decide (19 ≤ x + y + z) && decide (x + y + z ≤ 128) &&
  decide (16 ≤ y + z) && (y + z) % 2 == 0 && !(x == 0 && z == 0 && y != 80) &&
  ph % 8 == 0 && decide (tau ≤ 128) &&
  decide (4 * (tau + 2 * over) ≤ 784 - (mass : Int)) &&
  !(inRange x z mass && testBit excl6Mask (factIndex x z mass))

/-- Exact rank-6 section cost (`check_frontier_96_98.py`'s `cost(half)`). -/
def costR6 (excl6Mask : Nat) (eBounds : List (Nat × Nat × Nat × Nat)) (budget x y z : Nat) : Nat :=
  if !halfR6OK excl6Mask x y z then budget + 1
  else
    let m := 6 * x + 3 * y + 5 * z
    let eb := eminClosed m (x + z)
    let lb := lookupBound eBounds x y z
    if eb ≤ lb then lb else eb

/-- Enumerate all canonical `(x, y, z)` (`lo ≤ hi`) splits with `cost(lo) + cost(hi) ≤ budget`. -/
def genSplits (excl6Mask : Nat) (eBounds : List (Nat × Nat × Nat × Nat)) (t a b c : Nat) : List Triple :=
  let budget := (3 * t - 208) / 2 - a - c
  (List.range (a + 1)).flatMap fun x =>
    (List.range (c + 1)).flatMap fun z =>
      (List.range (b + 1)).filterMap fun y =>
        let lo : Triple := (x, y, z)
        let hi : Triple := (a - x, b - y, c - z)
        if tripleLe lo hi &&
           costR6 excl6Mask eBounds budget x y z + costR6 excl6Mask eBounds budget hi.1 hi.2.1 hi.2.2 ≤ budget
        then some lo
        else none

/-- Enumerate all canonical 6-var sub-splits `p ≤ q` (`p + q = n`) where `sixOK p r ∧ sixOK q r`. -/
def genSubtypes (n : Triple) (r : Nat) : List Triple :=
  let (a, b, c) := n
  (List.range (a + 1)).flatMap fun x =>
    (List.range (c + 1)).flatMap fun z =>
      (List.range (b + 1)).filterMap fun y =>
        let p : Triple := (x, y, z)
        let q : Triple := (a - x, b - y, c - z)
        if tripleLe p q && sixOK x y z r && sixOK q.1 q.2.1 q.2.2 r
        then some p
        else none

/-- Bit index for fast `O(1)` membership in the surviving half set `both` (`x, y, z < 64`). -/
def halfBitIdx (p : Triple) : Nat := (p.1 * 64 + p.2.2) * 64 + p.2.1

/-- Build bitset of `anchors ∪ {n - p | p ∈ anchors}`. -/
def buildAllowedMask (a b c : Nat) (anchors : List Triple) : Nat :=
  anchors.foldl (fun acc p =>
    let q : Triple := (a - p.1, b - p.2.1, c - p.2.2)
    acc ||| (1 <<< halfBitIdx p) ||| (1 <<< halfBitIdx q)) 0

def inAllowedMask (mask : Nat) (p : Triple) : Bool :=
  p.1 < 64 && p.2.1 < 64 && p.2.2 < 64 && testBit mask (halfBitIdx p)

/-! ### Proof that `buildAllowedMask` / `genSplits` / `genSubtypes` are complete -/

private theorem testBit_eq_nat (a i : Nat) : testBit a i = a.testBit i := by
  unfold testBit Nat.testBit
  rw [Nat.and_comm 1, Nat.and_one_is_mod]
  have h : (a >>> i) % 2 = 0 ∨ (a >>> i) % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> decide

private theorem testBit_or (a b i : Nat) : testBit (a ||| b) i = (testBit a i || testBit b i) := by
  rw [testBit_eq_nat, testBit_eq_nat, testBit_eq_nat, Nat.testBit_or]

private theorem testBit_one_shift_self (i : Nat) : testBit (1 <<< i) i = true := by
  unfold testBit
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow, Nat.div_self (Nat.two_pow_pos i)]
  rfl

private theorem testBit_foldl_mono (a b c : Nat) :
    ∀ (L : List Triple) (init : Nat) (idx : Nat),
      testBit init idx = true → testBit (L.foldl (fun acc p =>
        let q : Triple := (a - p.1, b - p.2.1, c - p.2.2)
        acc ||| (1 <<< halfBitIdx p) ||| (1 <<< halfBitIdx q)) init) idx = true
  | [], _, _, h => h
  | p :: t, init, idx, h => by
    apply testBit_foldl_mono a b c t
    rw [testBit_or, testBit_or, h]; rfl

private theorem testBit_buildAllowedMask_of_mem (a b c : Nat) (anchors : List Triple)
    (p : Triple) (hp : p ∈ anchors) :
    testBit (buildAllowedMask a b c anchors) (halfBitIdx p) = true ∧
    testBit (buildAllowedMask a b c anchors) (halfBitIdx (a - p.1, b - p.2.1, c - p.2.2)) = true := by
  have gen : ∀ (L : List Triple) (init : Nat), p ∈ L →
      testBit (L.foldl (fun acc r =>
        let q : Triple := (a - r.1, b - r.2.1, c - r.2.2)
        acc ||| (1 <<< halfBitIdx r) ||| (1 <<< halfBitIdx q)) init) (halfBitIdx p) = true ∧
      testBit (L.foldl (fun acc r =>
        let q : Triple := (a - r.1, b - r.2.1, c - r.2.2)
        acc ||| (1 <<< halfBitIdx r) ||| (1 <<< halfBitIdx q)) init) (halfBitIdx (a - p.1, b - p.2.1, c - p.2.2)) = true := by
    intro L
    induction L with
    | nil => intro _ h; exact nomatch h
    | cons r t ih =>
      intro init hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · constructor
        · apply testBit_foldl_mono a b c t
          rw [testBit_or, testBit_or, testBit_one_shift_self]; simp
        · apply testBit_foldl_mono a b c t
          rw [testBit_or, testBit_one_shift_self]; simp
      · exact ih _ htail
  exact gen anchors 0 hp

private theorem tripleLe_total (p q : Triple) : tripleLe p q = true ∨ tripleLe q p = true := by
  unfold tripleLe
  if h1 : p.1 < q.1 then
    exact Or.inl (by simp [h1])
  else if h1' : q.1 < p.1 then
    exact Or.inr (by simp [h1'])
  else
    have e1 : p.1 = q.1 := by omega
    if h2 : p.2.1 < q.2.1 then
      exact Or.inl (by simp [e1, h2])
    else if h2' : q.2.1 < p.2.1 then
      exact Or.inr (by simp [e1, h2'])
    else
      have e2 : p.2.1 = q.2.1 := by omega
      if h3 : p.2.2 ≤ q.2.2 then
        exact Or.inl (by simp [e1, e2, h3])
      else
        have h3' : q.2.2 ≤ p.2.2 := by omega
        exact Or.inr (by simp [e1, e2, h3'])

private theorem canonPair_le (a b c x y z : Nat) (hx : x ≤ a) (hy : y ≤ b) (hz : z ≤ c) :
    let lo := canonPair a b c x y z
    tripleLe lo (a - lo.1, b - lo.2.1, c - lo.2.2) = true := by
  unfold canonPair
  dsimp only
  cases h : tripleLe (x, y, z) (a - x, b - y, c - z)
  · simp only [Bool.false_eq_true, if_false]
    rw [Nat.sub_sub_self hx, Nat.sub_sub_self hy, Nat.sub_sub_self hz]
    rcases tripleLe_total (x, y, z) (a - x, b - y, c - z) with ht | ht
    · rw [ht] at h; exact Bool.noConfusion h
    · exact ht
  · simp [h]

theorem mem_genSplits {excl6Mask : Nat} {eBounds : List (Nat × Nat × Nat × Nat)} {t a b c x y z : Nat}
    (hx : x ≤ a) (hy : y ≤ b) (hz : z ≤ c)
    (hcost : costR6 excl6Mask eBounds ((3 * t - 208) / 2 - a - c) x y z +
             costR6 excl6Mask eBounds ((3 * t - 208) / 2 - a - c) (a - x) (b - y) (c - z) ≤
             (3 * t - 208) / 2 - a - c) :
    canonPair a b c x y z ∈ genSplits excl6Mask eBounds t a b c := by
  let lo := canonPair a b c x y z
  have hle : tripleLe lo (a - lo.1, b - lo.2.1, c - lo.2.2) = true := canonPair_le a b c x y z hx hy hz
  have hlo_b : lo.1 ≤ a ∧ lo.2.1 ≤ b ∧ lo.2.2 ≤ c ∧
      costR6 excl6Mask eBounds ((3 * t - 208) / 2 - a - c) lo.1 lo.2.1 lo.2.2 +
      costR6 excl6Mask eBounds ((3 * t - 208) / 2 - a - c) (a - lo.1) (b - lo.2.1) (c - lo.2.2) ≤
      (3 * t - 208) / 2 - a - c := by
    dsimp only [lo, canonPair]
    split
    · exact ⟨hx, hy, hz, hcost⟩
    · refine ⟨Nat.sub_le a x, Nat.sub_le b y, Nat.sub_le c z, ?_⟩
      rw [Nat.sub_sub_self hx, Nat.sub_sub_self hy, Nat.sub_sub_self hz, Nat.add_comm]
      exact hcost
  unfold genSplits
  rw [List.mem_flatMap]
  refine ⟨lo.1, List.mem_range.mpr (by omega), ?_⟩
  rw [List.mem_flatMap]
  refine ⟨lo.2.2, List.mem_range.mpr (by omega), ?_⟩
  rw [List.mem_filterMap]
  refine ⟨lo.2.1, List.mem_range.mpr (by omega), ?_⟩
  simp only [hle, Bool.true_and, decide_eq_true hlo_b.2.2.2, if_true]

theorem mem_genSubtypes {n : Triple} {r x y z : Nat}
    (hx : x ≤ n.1) (hy : y ≤ n.2.1) (hz : z ≤ n.2.2)
    (h1 : sixOK x y z r = true) (h2 : sixOK (n.1 - x) (n.2.1 - y) (n.2.2 - z) r = true) :
    canonPair n.1 n.2.1 n.2.2 x y z ∈ genSubtypes n r := by
  let lo := canonPair n.1 n.2.1 n.2.2 x y z
  have hle : tripleLe lo (n.1 - lo.1, n.2.1 - lo.2.1, n.2.2 - lo.2.2) = true :=
    canonPair_le n.1 n.2.1 n.2.2 x y z hx hy hz
  have hlo_b : lo.1 ≤ n.1 ∧ lo.2.1 ≤ n.2.1 ∧ lo.2.2 ≤ n.2.2 ∧
      sixOK lo.1 lo.2.1 lo.2.2 r = true ∧
      sixOK (n.1 - lo.1) (n.2.1 - lo.2.1) (n.2.2 - lo.2.2) r = true := by
    dsimp only [lo, canonPair]
    split
    · exact ⟨hx, hy, hz, h1, h2⟩
    · refine ⟨Nat.sub_le n.1 x, Nat.sub_le n.2.1 y, Nat.sub_le n.2.2 z, h2, ?_⟩
      rw [Nat.sub_sub_self hx, Nat.sub_sub_self hy, Nat.sub_sub_self hz]; exact h1
  unfold genSubtypes
  rcases n with ⟨a, b, c⟩
  dsimp only at hle hlo_b ⊢
  rw [List.mem_flatMap]
  refine ⟨lo.1, List.mem_range.mpr (by omega), ?_⟩
  rw [List.mem_flatMap]
  refine ⟨lo.2.2, List.mem_range.mpr (by omega), ?_⟩
  rw [List.mem_filterMap]
  refine ⟨lo.2.1, List.mem_range.mpr (by omega), ?_⟩
  simp only [hle, hlo_b.2.2.2.1, hlo_b.2.2.2.2, Bool.and_self, if_true]

/-! ## Part 7: Soundness of `halfR6OK`, `costR6`, and `sixOK` on real sections -/

private theorem all_true_of_total {n : Nat} (p : W n → Bool)
    (h : total n (fun x => bind (p x)) = many n) (x : W n) : p x = true := by
  cases hx : p x
  · exfalso
    have hle : total n (fun y => bind (p y)) ≤ many n - 1 := by
      have hpt (y : W n) : bind (p y) ≤ (1 : Int) - hits x y := by
        unfold Balanced242Plateau.ind hits
        if hy : x = y then subst hy; simp [hx]
        else simp only [hy, if_false, Int.sub_zero]; cases p y <;> decide
      have hm := total_mono n _ _ hpt
      rw [total_sub, total_const, Int.mul_one, diagonal] at hm
      exact hm
    omega
  · rfl

private def findTrueList {α : Type} (p : α → Bool) :
    (L : List α) → L.all (fun x => !p x) = false → { x : α // p x = true }
  | [], h0 => False.elim (Bool.noConfusion h0)
  | a :: t, h0 =>
    match hp : p a with
    | true => ⟨a, hp⟩
    | false =>
      have ht : t.all (fun x => !p x) = false := by
        simp only [List.all_cons, hp, Bool.not_false, Bool.true_and] at h0; exact h0
      findTrueList p t ht

private def find_true_pos {n : Nat} (p : W n → Bool)
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
  findTrueList p (worlds n) hall

private theorem rr_of_plat {n : Nat} (β : W n → Bool) (hc : Cube β) (M : Int)
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
  let ⟨y, hy⟩ := find_true_pos (good β) hpos
  have hsg := spec_good β hc y
  rw [hy] at hsg
  simp only [Balanced242Plateau.ind, if_true, Int.mul_one] at hsg
  rcases hplat y with h | h | h
  · rw [h] at hsg; have := Int.mul_pos hmn (by omega : 0 < rr β); omega
  · rw [h] at hsg; exact hsg.symm
  · rw [h, Int.neg_mul_neg] at hsg; exact hsg.symm

private theorem total_even : ∀ (n : Nat) (F : W n → Int), (∀ x, F x % 2 = 0) → total n F % 2 = 0
  | 0, F, hF => hF ()
  | m + 1, F, hF => by
    show (total m (fun z => F (false, z)) + total m (fun z => F (true, z))) % 2 = 0
    have h0 := total_even m (fun z => F (false, z)) (fun z => hF (false, z))
    have h1 := total_even m (fun z => F (true, z)) (fun z => hF (true, z))
    omega

private theorem U_sq_even (f g : Half) (res : ∀ a, hi f g a % 8 = 4) :
    total 8 (fun u => U f g u * U f g u) % 2 = 0 := by
  have hdiff : total 8 (fun u => U f g u * U f g u - U f g u) % 2 = 0 := by
    apply total_even 8; intro u
    have hsub : U f g u * U f g u - U f g u = U f g u * (U f g u - 1) := by rw [Int.mul_sub, Int.mul_one]
    rw [hsub]
    if h0 : U f g u % 2 = 0 then rw [Int.mul_emod, h0, Int.zero_mul]; rfl
    else have h1 : (U f g u - 1) % 2 = 0 := by omega
         rw [Int.mul_emod, h1, Int.mul_zero]; rfl
  have hsum : total 8 (U f g) = hi f g (zero 8) / 2 := by
    have htr := Balanced242SectionFacts.hi_U f g (zero 8)
    have hc (u : W 8) : U f g u * chr (zero 8) u = U f g u := by simp [chr, dot_zero, sign]
    unfold transform at htr; rw [funext hc] at htr; omega
  have h0 := res (zero 8)
  rw [total_sub, hsum] at hdiff; omega

private theorem agreements_even_of_res (f g : Half) (res : ∀ a, hi f g a % 8 = 4) :
    agreements f g % 2 = 0 := by
  have hu := U_sq_even f g res
  have hpt (u : W 8) : U f g u * U f g u + (sameBit false (f u) (g u) + sameBit true (f u) (g u)) = 1 := by
    unfold U sameBit; cases f u <;> cases g u <;> decide
  have hsum := congrArg (total 8) (funext hpt)
  rw [total_add, total_add, total_const, Int.mul_one] at hsum
  have h256 : many 8 = 256 := by decide
  rw [h256] at hsum
  unfold agreements countPair
  omega

/-- For any genuine 7-variable rank-6 section of `(f, g)` (under `SectionEnumE`),
    `halfR6OK = true` and `costR6 ≤ secExc`. -/
theorem section_costR6_le (excl6Mask : Nat) (eBounds : List (Nat × Nat × Nat × Nat))
    (henum : SectionEnumE excl6Mask eBounds)
    (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (hicap : ∀ a, (hi f g a).natAbs ≤ 28)
    (hrr : rr (β8 f g) = 1) (w : W 8) (hw : w ≠ zero 8) (c : Bool) (budget : Nat) :
    let H := secH f g w c
    let D := secD f g w c
    let x := (suppList (fun a => clsA f g (secPt 7 w c a))).length
    let y := (suppList (fun a => clsB f g (secPt 7 w c a))).length
    let z := (suppList (fun a => clsC f g (secPt 7 w c a))).length
    halfR6OK excl6Mask x y z = true ∧
    (costR6 excl6Mask eBounds budget x y z : Int) ≤ secExc D (transform (fun a => phase (H a))) := by
  intro H D x y z
  have hD : ∀ u, -2 ≤ D u ∧ D u ≤ 2 := secD_bound f g w c
  have hspec : ∀ a, transform D a = 2 * H a := secH_spec f g res w hw c
  have hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7 := fun a =>
    ⟨secH_odd f g res w c a, by
      have h1 := hicap (secPt 7 w c a)
      have h2 := res (secPt 7 w c a)
      unfold H secH; omega⟩
  have hcube8 : Cube (β8 f g) := Balanced242Global.cube8 f g res
  have hph8 (a : W 8) : phase (H8 f g a) = sign (β8 f g a) :=
    phase_bt (H8 f g a) (odd8 f g res a)
  have h8 : ∀ u, transform (Balanced242RankCond.q8 f g) u = 16 ∨
      transform (Balanced242RankCond.q8 f g) u = -16 := by
    intro u
    have hrg := rr_good (β8 f g) hcube8
    rw [hrr, Int.one_mul] at hrg
    have hgu : good (β8 f g) u = true := all_true_of_total (good (β8 f g)) hrg u
    have hsg := spec_good (β8 f g) hcube8 u
    rw [hgu, hrr] at hsg
    have hm : many 8 = 256 := by decide
    rw [hm] at hsg
    have hsq : transform (Balanced242RankCond.q8 f g) u * transform (Balanced242RankCond.q8 f g) u = 256 := by
      simpa [Balanced242RankCond.q8, Balanced242Plateau.ind] using hsg
    exact sq_cases _ 16 hsq
  have hplat (u : W 7) :
      transform (fun a => phase (H a)) u = 0 ∨
      transform (fun a => phase (H a)) u = 16 ∨
      transform (fun a => phase (H a)) u = -16 := by
    rw [sec_phase_transform f g res h8 w hw c u]
    have hσ (x : W 8) : transform (Balanced242RankCond.q8 f g) x / 16 = 1 ∨
        transform (Balanced242RankCond.q8 f g) x / 16 = -1 := by
      rcases h8 x with h | h <;> rw [h] <;> decide
    obtain ⟨p, hp⟩ := secFun_pair 7 w hw c (fun x => transform (Balanced242RankCond.q8 f g) x / 16) u
    rw [hp]
    rcases hσ p with h1 | h1 <;> rcases hσ (add 8 w p) with h2 | h2 <;>
      cases c <;> simp [sign, h1, h2]
  have hx : (x : Int) = total 7 (fun a => if (H a).natAbs = 1 then 1 else 0) := by
    rw [suppList_length_eq_total]
    apply congrArg (total 7); funext a
    unfold clsA H secH Balanced242Plateau.ind
    have := res (secPt 7 w c a); have := hicap (secPt 7 w c a)
    if h1 : (hi f g (secPt 7 w c a)).natAbs = 4 then
      have h2 : (hi f g (secPt 7 w c a) / 4).natAbs = 1 := by omega
      simp [h1, h2]
    else
      have h2 : (hi f g (secPt 7 w c a) / 4).natAbs ≠ 1 := by omega
      simp [h1, h2]
  have hy : (y : Int) = total 7 (fun a => if (H a).natAbs = 5 then 1 else 0) := by
    rw [suppList_length_eq_total]
    apply congrArg (total 7); funext a
    unfold clsB H secH Balanced242Plateau.ind
    have := res (secPt 7 w c a); have := hicap (secPt 7 w c a)
    if h1 : (hi f g (secPt 7 w c a)).natAbs = 20 then
      have h2 : (hi f g (secPt 7 w c a) / 4).natAbs = 5 := by omega
      simp [h1, h2]
    else
      have h2 : (hi f g (secPt 7 w c a) / 4).natAbs ≠ 5 := by omega
      simp [h1, h2]
  have hz : (z : Int) = total 7 (fun a => if (H a).natAbs = 3 then 1 else 0) := by
    rw [suppList_length_eq_total]
    apply congrArg (total 7); funext a
    unfold clsC H secH Balanced242Plateau.ind
    have := res (secPt 7 w c a); have := hicap (secPt 7 w c a)
    if h1 : (hi f g (secPt 7 w c a)).natAbs = 12 then
      have h2 : (hi f g (secPt 7 w c a) / 4).natAbs = 3 := by omega
      simp [h1, h2]
    else
      have h2 : (hi f g (secPt 7 w c a) / 4).natAbs ≠ 3 := by omega
      simp [h1, h2]
  have hev : total 7 (fun u => D u * D u) % 2 = 0 :=
    secD_sq_even f g w hw c (agreements_even_of_res f g res)
  obtain ⟨h88, h19, hnexcl, hlb⟩ := henum D H hD hspec hH hev hplat x y z hx hy hz
  have hdiv8 : (6 * x + 3 * y + 5 * z) % 8 = 0 := by
    have h := half_mass_div8 D H hspec hH
    dsimp only at h; rw [← hx, ← hy, ← hz] at h; omega
  have hsum128 : x + y + z ≤ 128 := by
    have hpt (a : W 7) :
        (if (H a).natAbs = 1 then (1 : Int) else 0) +
        (if (H a).natAbs = 5 then (1 : Int) else 0) +
        (if (H a).natAbs = 3 then (1 : Int) else 0) ≤ 1 := by
      have h := hH a; omega
    have hm := total_mono 7 _ _ hpt
    rw [total_add, total_add, total_const, Int.mul_one, ← hx, ← hy, ← hz] at hm
    have h128 : many 7 = 128 := by decide
    rw [h128] at hm; omega
  have hyz16 : 16 ≤ y + z ∧ (y + z) % 2 = 0 := by
    have hanch := anchor_pair_ranks_63_64 (β8 f g) hcube8 hrr w hw
    dsimp only at hanch
    have hrr7 : rr (fun a => β8 f g (secPt 7 w c a)) = 2 := by
      cases c; exact hanch.1; exact hanch.2.1
    have hq := half_yz_ge_16 D H hspec hH (fun a => β8 f g (secPt 7 w c a))
      (sec_cube (β8 f g) hcube8 w c) (fun a => hph8 (secPt 7 w c a)) hrr7
    dsimp only at hq; rw [← hy, ← hz] at hq; omega
  have h0b0 : (!(x == 0 && z == 0 && y != 80)) = true := by
    if hxz : x = 0 ∧ z = 0 then
      have hsecA : Balanced242SectionFacts.secCnt (clsA f g) w c = (x : Int) := by
        unfold Balanced242SectionFacts.secCnt; rw [suppList_length_eq_total]; rfl
      have hsecB : Balanced242SectionFacts.secCnt (clsB f g) w c = (y : Int) := by
        unfold Balanced242SectionFacts.secCnt; rw [suppList_length_eq_total]; rfl
      have hsecC : Balanced242SectionFacts.secCnt (clsC f g) w c = (z : Int) := by
        unfold Balanced242SectionFacts.secCnt; rw [suppList_length_eq_total]; rfl
      have h0 := hyperplane_0b0 f g res hicap w hw c (by omega) (by omega)
      have hy80 : y = 80 := by rw [hsecB] at h0; omega
      simp [hxz.1, hxz.2, hy80]
    else if hx0 : x = 0 then
      have hz0 : z ≠ 0 := fun h => hxz ⟨hx0, h⟩
      simp [hx0, hz0]
    else
      simp [hx0]
  have hcs := Balanced242SectionBounds.section_cs_ok D H hD hspec hH 16 (Or.inl rfl) hplat
  dsimp only at hcs
  rw [← hx, ← hy, ← hz] at hcs
  have htau_cap : ((-896 + 8 * (x : Int) + 12 * (y : Int) + 4 * (z : Int)) / 8).natAbs ≤ 128 := by
    have ht7 := Balanced242Global.t7_of_plateau D H hD hspec 16 (Or.inl rfl) hplat
    have hsum := Balanced242SectionBounds.section_t7_sum H hH
    dsimp only at hsum; rw [← hx, ← hy, ← hz] at hsum
    rw [hsum] at ht7; omega
  have hhalf : halfR6OK excl6Mask x y z = true := by
    unfold halfR6OK
    dsimp only
    have h1 : decide (88 ≤ 6 * x + 3 * y + 5 * z) = true := decide_eq_true h88
    have h2 : (6 * x + 3 * y + 5 * z) % 8 == 0 := beq_iff_eq.mpr hdiv8
    have h3 : decide (19 ≤ x + y + z) = true := decide_eq_true h19
    have h4 : decide (x + y + z ≤ 128) = true := decide_eq_true hsum128
    have h5 : decide (16 ≤ y + z) = true := decide_eq_true hyz16.1
    have h6 : (y + z) % 2 == 0 := beq_iff_eq.mpr hyz16.2
    have h7 : (-896 + 8 * (x : Int) + 12 * (y : Int) + 4 * (z : Int)) % 8 == 0 :=
      beq_iff_eq.mpr hcs.1
    have h8 : decide (((-896 + 8 * (x : Int) + 12 * (y : Int) + 4 * (z : Int)) / 8).natAbs ≤ (128 : Int)) = true :=
      decide_eq_true (by omega)
    have h9 : decide (4 * ((((-896 + 8 * (x : Int) + 12 * (y : Int) + 4 * (z : Int)) / 8).natAbs : Int) +
        2 * (if 64 ≤ (((-896 + 8 * (x : Int) + 12 * (y : Int) + 4 * (z : Int)) / 8).natAbs : Int)
             then (((-896 + 8 * (x : Int) + 12 * (y : Int) + 4 * (z : Int)) / 8).natAbs : Int) - 64 else 0)) ≤
        784 - ((6 * x + 3 * y + 5 * z : Nat) : Int)) = true := by
      apply decide_eq_true
      split
      · have := hcs.2.2; omega
      · have := hcs.2.1; omega
    simp only [h1, h2, h3, h4, h5, h6, h0b0, h7, h8, h9, hnexcl, Bool.not_false, Bool.and_true]
  refine ⟨hhalf, ?_⟩
  unfold costR6
  rw [hhalf]; simp only [Bool.not_true, Bool.false_eq_true, if_false]
  have heb := eminClosed_le_secExc D H hD hspec hH hplat x y z hx hy hz
  split
  · exact hlb
  · exact heb

/-- Soundness of `sixOK` on any genuine 6-variable sub-section `secPt 7 w c0 (secPt 6 v c1 _)`. -/
theorem sixOK_of_subsection (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (hicap : ∀ a, (hi f g a).natAbs ≤ 28)
    (hrr : rr (β8 f g) = 1) (w : W 8) (hw : w ≠ zero 8) (c0 : Bool)
    (v : W 7) (hv : v ≠ zero 7) (c1 : Bool) :
    let r := if perp (fun a => β8 f g (secPt 7 w false a)) v then 4 else 6
    let P0 (a : W 6) := clsA f g (secPt 7 w c0 (secPt 6 v c1 a))
    let P1 (a : W 6) := clsB f g (secPt 7 w c0 (secPt 6 v c1 a))
    let P2 (a : W 6) := clsC f g (secPt 7 w c0 (secPt 6 v c1 a))
    sixOK (suppList P0).length (suppList P1).length (suppList P2).length r = true := by
  intro r P0 P1 P2
  let H6 (a : W 6) : Int := secH f g w c0 (secPt 6 v c1 a)
  let E6 : W 6 → Int := secFun 6 v c1 (secD f g w c0)
  have hE : ∀ y, -4 ≤ E6 y ∧ E6 y ≤ 4 := by
    intro y
    obtain ⟨p, hp⟩ := secFun_pair 6 v hv c1 (secD f g w c0) y
    have h1 := secD_bound f g w c0 p
    have h2 := secD_bound f g w c0 (add 7 v p)
    dsimp only [E6]; rw [hp]
    cases c1 <;> simp [sign] <;> omega
  have hspec : ∀ a, transform E6 a = 2 * H6 a := fun a => by
    dsimp only [E6, H6]
    rw [← sec_transform 6 v hv c1 (secD f g w c0) a, secH_spec f g res w hw c0]
  have hH : ∀ a, H6 a % 2 = 1 ∧ (H6 a).natAbs ≤ 7 := fun a =>
    ⟨secH_odd f g res w c0 (secPt 6 v c1 a), by
      have h1 := hicap (secPt 7 w c0 (secPt 6 v c1 a))
      have h2 := res (secPt 7 w c0 (secPt 6 v c1 a))
      unfold H6 secH; omega⟩
  have hx : ((suppList P0).length : Int) = total 6 (fun a => if (H6 a).natAbs = 1 then 1 else 0) := by
    rw [suppList_length_eq_total]; apply congrArg (total 6); funext a
    unfold P0 clsA H6 secH Balanced242Plateau.ind
    have := res (secPt 7 w c0 (secPt 6 v c1 a)); have := hicap (secPt 7 w c0 (secPt 6 v c1 a))
    if h1 : (hi f g (secPt 7 w c0 (secPt 6 v c1 a))).natAbs = 4 then
      have h2 : (hi f g (secPt 7 w c0 (secPt 6 v c1 a)) / 4).natAbs = 1 := by omega
      simp [h1, h2]
    else
      have h2 : (hi f g (secPt 7 w c0 (secPt 6 v c1 a)) / 4).natAbs ≠ 1 := by omega
      simp [h1, h2]
  have hy : ((suppList P1).length : Int) = total 6 (fun a => if (H6 a).natAbs = 5 then 1 else 0) := by
    rw [suppList_length_eq_total]; apply congrArg (total 6); funext a
    unfold P1 clsB H6 secH Balanced242Plateau.ind
    have := res (secPt 7 w c0 (secPt 6 v c1 a)); have := hicap (secPt 7 w c0 (secPt 6 v c1 a))
    if h1 : (hi f g (secPt 7 w c0 (secPt 6 v c1 a))).natAbs = 20 then
      have h2 : (hi f g (secPt 7 w c0 (secPt 6 v c1 a)) / 4).natAbs = 5 := by omega
      simp [h1, h2]
    else
      have h2 : (hi f g (secPt 7 w c0 (secPt 6 v c1 a)) / 4).natAbs ≠ 5 := by omega
      simp [h1, h2]
  have hz : ((suppList P2).length : Int) = total 6 (fun a => if (H6 a).natAbs = 3 then 1 else 0) := by
    rw [suppList_length_eq_total]; apply congrArg (total 6); funext a
    unfold P2 clsC H6 secH Balanced242Plateau.ind
    have := res (secPt 7 w c0 (secPt 6 v c1 a)); have := hicap (secPt 7 w c0 (secPt 6 v c1 a))
    if h1 : (hi f g (secPt 7 w c0 (secPt 6 v c1 a))).natAbs = 12 then
      have h2 : (hi f g (secPt 7 w c0 (secPt 6 v c1 a)) / 4).natAbs = 3 := by omega
      simp [h1, h2]
    else
      have h2 : (hi f g (secPt 7 w c0 (secPt 6 v c1 a)) / 4).natAbs ≠ 3 := by omega
      simp [h1, h2]
  have hdiv := six_section_div4 E6 H6 hspec hH
  dsimp only at hdiv; rw [← hx, ← hy, ← hz] at hdiv
  have hsum64 : (suppList P0).length + (suppList P1).length + (suppList P2).length ≤ 64 := by
    have hpt (a : W 6) :
        (if (H6 a).natAbs = 1 then (1 : Int) else 0) +
        (if (H6 a).natAbs = 5 then (1 : Int) else 0) +
        (if (H6 a).natAbs = 3 then (1 : Int) else 0) ≤ 1 := by
      have h := hH a; omega
    have hm := total_mono 6 _ _ hpt
    rw [total_add, total_add, total_const, Int.mul_one, ← hx, ← hy, ← hz] at hm
    have h64 : many 6 = 64 := by decide
    rw [h64] at hm; omega
  have hcube8 : Cube (β8 f g) := Balanced242Global.cube8 f g res
  let β6 (a : W 6) : Bool := β8 f g (secPt 7 w c0 (secPt 6 v c1 a))
  have hcube6 : Cube β6 := sec_cube _ (sec_cube (β8 f g) hcube8 w c0) v c1
  have hph6 (a : W 6) : phase (H6 a) = sign (β6 a) :=
    phase_bt (H6 a) (odd8 f g res (secPt 7 w c0 (secPt 6 v c1 a)))
  have hanch := anchor_pair_ranks_63_64 (β8 f g) hcube8 hrr w hw
  dsimp only at hanch
  have hlv := hanch.2.2.2.2.2 v hv c0 c1
  cases hpv : perp (fun a => β8 f g (secPt 7 w false a)) v
  · -- `perp = false` => `r = 6`, `m = 8`, `rr β6 = 1`
    have hr6 : r = 6 := by simp [r, hpv]
    rw [hr6]
    have hplat (y : W 6) :
        transform (fun a => phase (H6 a)) y = 0 ∨
        transform (fun a => phase (H6 a)) y = 8 ∨
        transform (fun a => phase (H6 a)) y = -8 := by
      have h1 := (hlv y).2 hpv
      have hfn : (fun a => phase (H6 a)) = (fun a => sign (β6 a)) := funext hph6
      rw [hfn]; exact h1
    have hrr6 : rr β6 = 1 := by
      have hfn : (fun a => sign (β6 a)) = (fun a => phase (H6 a)) := (funext hph6).symm
      have h := rr_of_plat β6 hcube6 8 (fun y => by rw [hfn]; exact hplat y)
      have hm : many 6 = 64 := by decide
      rw [hm] at h; omega
    have hbc8 := six_bc_ge_8 E6 H6 hspec hH β6 hcube6 hph6 hrr6
    dsimp only at hbc8; rw [← hy, ← hz] at hbc8
    have hj := six_section_jensen E6 H6 hE hspec hH 8 (Or.inl rfl) hplat
    dsimp only at hj; rw [← hx, ← hy, ← hz] at hj
    unfold sixOK; dsimp only
    simp only [beq_self_eq_true, if_true]
    have c1 : (6 * (suppList P0).length + 3 * (suppList P1).length + 5 * (suppList P2).length) % 4 == 0 :=
      beq_iff_eq.mpr (by omega)
    have c2 : decide ((suppList P0).length + (suppList P1).length + (suppList P2).length ≤ 64) = true :=
      decide_eq_true hsum64
    have c3 : ((suppList P1).length + (suppList P2).length) % 2 == 0 :=
      beq_iff_eq.mpr (by omega)
    have c4 : decide (8 ≤ (suppList P1).length + (suppList P2).length) = true :=
      decide_eq_true (by omega)
    have c5 : (-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) % 4 == 0 := beq_iff_eq.mpr hj.1
    have c6 : decide ((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 4).natAbs : Int) ≤ 4 * 64) = true :=
      decide_eq_true (by have := hj.2.1; omega)
    have c7 : decide ((64 - (((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 4).natAbs : Int) % 64) *
        (((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 4).natAbs : Int) / 64) *
         ((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 4).natAbs : Int) / 64)) +
        (((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 4).natAbs : Int) % 64 *
        ((((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 4).natAbs : Int) / 64) + 1) *
         (((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 4).natAbs : Int) / 64) + 1)) ≤
        196 - ((6 * (suppList P0).length + 3 * (suppList P1).length + 5 * (suppList P2).length : Nat) : Int) / 2) = true := by
      apply decide_eq_true
      have hj2 := hj.2.2
      change 2 * ((64 - (((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
          4 * ((suppList P2).length : Int)) / 4).natAbs : Int) % 64) *
          (((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
          4 * ((suppList P2).length : Int)) / 4).natAbs : Int) / 64) *
           ((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
          4 * ((suppList P2).length : Int)) / 4).natAbs : Int) / 64)) +
          (((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
          4 * ((suppList P2).length : Int)) / 4).natAbs : Int) % 64 *
          ((((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
          4 * ((suppList P2).length : Int)) / 4).natAbs : Int) / 64) + 1) *
           (((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
          4 * ((suppList P2).length : Int)) / 4).natAbs : Int) / 64) + 1))) ≤
          392 - (6 * ((suppList P0).length : Int) + 3 * ((suppList P1).length : Int) +
            5 * ((suppList P2).length : Int)) at hj2
      omega
    simp only [c1, c2, c3, c4, c5, c6, c7, Bool.and_true]
  · -- `perp = true` => `r = 4`, `m = 16`, `rr β6 = 4`
    have hr4 : r = 4 := by simp [r, hpv]
    rw [hr4]
    have hplat (y : W 6) :
        transform (fun a => phase (H6 a)) y = 0 ∨
        transform (fun a => phase (H6 a)) y = 16 ∨
        transform (fun a => phase (H6 a)) y = -16 := by
      have h1 := (hlv y).1 hpv
      have hfn : (fun a => phase (H6 a)) = (fun a => sign (β6 a)) := funext hph6
      rw [hfn]; exact h1
    have hrr6 : rr β6 = 4 := by
      have hfn : (fun a => sign (β6 a)) = (fun a => phase (H6 a)) := (funext hph6).symm
      have h := rr_of_plat β6 hcube6 16 (fun y => by rw [hfn]; exact hplat y)
      have hm : many 6 = 64 := by decide
      rw [hm] at h; omega
    have hbc4 := six_bc_ge_4 E6 H6 hspec hH β6 hcube6 hph6 hrr6
    dsimp only at hbc4; rw [← hy, ← hz] at hbc4
    have hj := six_section_jensen E6 H6 hE hspec hH 16 (Or.inr rfl) hplat
    dsimp only at hj; rw [← hx, ← hy, ← hz] at hj
    unfold sixOK; dsimp only
    simp only [show (4 == 6) = false from rfl, Bool.false_eq_true, if_false]
    have c1 : (6 * (suppList P0).length + 3 * (suppList P1).length + 5 * (suppList P2).length) % 4 == 0 :=
      beq_iff_eq.mpr (by omega)
    have c2 : decide ((suppList P0).length + (suppList P1).length + (suppList P2).length ≤ 64) = true :=
      decide_eq_true hsum64
    have c3 : ((suppList P1).length + (suppList P2).length) % 2 == 0 :=
      beq_iff_eq.mpr (by omega)
    have c4 : decide (4 ≤ (suppList P1).length + (suppList P2).length) = true :=
      decide_eq_true (by omega)
    have c5 : (-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) % 8 == 0 := beq_iff_eq.mpr hj.1
    have c6 : decide ((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 8).natAbs : Int) ≤ 4 * 16) = true :=
      decide_eq_true (by have := hj.2.1; omega)
    have c7 : decide ((16 - (((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 8).natAbs : Int) % 16) *
        (((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 8).natAbs : Int) / 16) *
         ((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 8).natAbs : Int) / 16)) +
        (((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 8).natAbs : Int) % 16 *
        ((((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 8).natAbs : Int) / 16) + 1) *
         (((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
        4 * ((suppList P2).length : Int)) / 8).natAbs : Int) / 16) + 1)) ≤
        196 - ((6 * (suppList P0).length + 3 * (suppList P1).length + 5 * (suppList P2).length : Nat) : Int) / 2) = true := by
      apply decide_eq_true
      have hj2 := hj.2.2
      change 2 * ((16 - (((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
          4 * ((suppList P2).length : Int)) / 8).natAbs : Int) % 16) *
          (((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
          4 * ((suppList P2).length : Int)) / 8).natAbs : Int) / 16) *
           ((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
          4 * ((suppList P2).length : Int)) / 8).natAbs : Int) / 16)) +
          (((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
          4 * ((suppList P2).length : Int)) / 8).natAbs : Int) % 16 *
          ((((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
          4 * ((suppList P2).length : Int)) / 8).natAbs : Int) / 16) + 1) *
           (((((-448 + 8 * ((suppList P0).length : Int) + 12 * ((suppList P1).length : Int) +
          4 * ((suppList P2).length : Int)) / 8).natAbs : Int) / 16) + 1))) ≤
          392 - (6 * ((suppList P0).length : Int) + 3 * ((suppList P1).length : Int) +
            5 * ((suppList P2).length : Int)) at hj2
      omega
    simp only [c1, c2, c3, c4, c5, c6, c7, Bool.and_true]

/-! ## Part 8: Affine Krawtchouk Certificate Verifier (`checkAffineCert`) -/

/-- O(k) multiplicative binomial coefficient `C(n, k)` for fast kernel evaluation. -/
def chooseFast (n : Nat) : Nat → Int
  | 0 => 1
  | k + 1 => (chooseFast n k * ((n : Int) - (k : Int))) / ((k + 1 : Nat) : Int)

private theorem choose_one_eq_fast : ∀ (n : Nat), choose n 1 = (n : Int)
  | 0 => rfl
  | n + 1 => by rw [Balanced242Krawtchouk.choose_succ_succ, Balanced242Krawtchouk.choose_zero, choose_one_eq_fast n]; omega

private theorem choose_mul_succ : ∀ (n k : Nat),
    ((k + 1 : Nat) : Int) * choose n (k + 1) = ((n : Int) - (k : Int)) * choose n k
  | 0, k => by
    cases k with
    | zero => decide
    | succ k' => simp [Balanced242Krawtchouk.choose]
  | n + 1, 0 => by
    rw [Balanced242Krawtchouk.choose_zero, choose_one_eq_fast (n + 1)]; omega
  | n + 1, k + 1 => by
    rw [Balanced242Krawtchouk.choose_succ_succ n (k + 1),
        Balanced242Krawtchouk.choose_succ_succ n k, Int.mul_add, Int.mul_add]
    have ih1 := choose_mul_succ n (k + 1)
    have ih0 := choose_mul_succ n k
    have hc1 : (((n + 1 : Nat) : Int) - ((k + 1 : Nat) : Int)) = (n : Int) - (k : Int) := by omega
    rw [ih1, hc1, ← ih0]
    have hsum1 : (((n : Int) - ((k + 1 : Nat) : Int)) + ((k + 2 : Nat) : Int)) = ((n : Int) + 1) := by omega
    have hsum2 : (((n : Int) - (k : Int)) + ((k + 1 : Nat) : Int)) = ((n : Int) + 1) := by omega
    calc
      ((n : Int) - ((k + 1 : Nat) : Int)) * choose n (k + 1) +
          ((k + 2 : Nat) : Int) * choose n (k + 1)
        = (((n : Int) - ((k + 1 : Nat) : Int)) + ((k + 2 : Nat) : Int)) * choose n (k + 1) := by
          rw [Int.add_mul]
      _ = (((n : Int) - (k : Int)) + ((k + 1 : Nat) : Int)) * choose n (k + 1) := by rw [hsum1, hsum2]
      _ = ((n : Int) - (k : Int)) * choose n (k + 1) + ((k + 1 : Nat) : Int) * choose n (k + 1) := by
          rw [Int.add_mul]

private theorem chooseFast_eq_choose (n : Nat) : ∀ (k : Nat), chooseFast n k = choose n k
  | 0 => (Balanced242Krawtchouk.choose_zero n).symm
  | k + 1 => by
    unfold chooseFast
    rw [chooseFast_eq_choose n k, Int.mul_comm (choose n k), ← choose_mul_succ n k,
        Int.mul_ediv_cancel_left _ (by omega)]

/-- Fast O(k²) Krawtchouk evaluator (using `chooseFast`, proved equal to `kraw`). -/
def krawFast (s x k : Nat) : Int :=
  sumInt ((List.range (k + 1)).map (fun r =>
    Balanced242Krawtchouk.altSign r * chooseFast x r * chooseFast (s - x) (k - r)))

private theorem krawFast_eq_kraw (s x k : Nat) : krawFast s x k = kraw s x k := by
  unfold krawFast kraw
  congr 1; apply List.map_congr_left; intro r _
  rw [chooseFast_eq_choose, chooseFast_eq_choose]

/-- A sparse Krawtchouk Farkas entry `(i, j, l, weight)`. -/
abbrev KrawEntry := Nat × Nat × Nat × Int

def krawRowVal (a b c : Nat) (e : KrawEntry) (col : Triple) : Int :=
  krawFast a col.1 e.1 * krawFast b col.2.1 e.2.1 * krawFast c col.2.2 e.2.2.1

def krawRowRhs (a b c : Nat) (e : KrawEntry) : Int :=
  if e.1 + e.2.1 + e.2.2.1 == 0 then 255
  else -(chooseFast a e.1 * chooseFast b e.2.1 * chooseFast c e.2.2.1)

def affineEntryValid (e : KrawEntry) : Bool :=
  let deg := e.1 + e.2.1 + e.2.2.1
  deg % 2 == 0 && (decide (deg ≤ 2) || decide (0 ≤ e.2.2.2))

def evalAffineCol (a b c : Nat) (cert : List KrawEntry) (col : Triple) : Int :=
  cert.foldl (fun acc e => acc + e.2.2.2 * krawRowVal a b c e col) 0

def evalAffineRhs (a b c : Nat) (cert : List KrawEntry) : Int :=
  cert.foldl (fun acc e => acc + e.2.2.2 * krawRowRhs a b c e) 0

/-- Computable kernel verifier for an affine Krawtchouk Farkas certificate. -/
def checkAffineCert (a b c : Nat) (cols : List Triple) (cert : List KrawEntry) : Bool :=
  cert.all affineEntryValid &&
  decide (0 < evalAffineRhs a b c cert) &&
  cols.all (fun col => decide (evalAffineCol a b c cert col ≤ 0))

private theorem foldl_add_eq {α : Type} (g : α → Int) :
    ∀ (L : List α) (init : Int),
      L.foldl (fun acc x => acc + g x) init = init + sumInt (L.map g)
  | [], init => by simp [sumInt]
  | x :: t, init => by
    simp only [List.foldl_cons, List.map_cons, sumInt, foldl_add_eq g t]
    omega

private theorem cls_disj (f g : Half) :
    (∀ x, (clsA f g x && clsB f g x) = false) ∧
    (∀ x, (clsA f g x && clsC f g x) = false) ∧
    (∀ x, (clsB f g x && clsC f g x) = false) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · unfold clsA clsB; if h1 : (hi f g x).natAbs = 4 then simp [h1] else simp [h1]
  · unfold clsA clsC; if h1 : (hi f g x).natAbs = 4 then simp [h1] else simp [h1]
  · unfold clsB clsC; if h1 : (hi f g x).natAbs = 20 then simp [h1] else simp [h1]

private theorem kraw_k0 (s x : Nat) : kraw s x 0 = 1 := by
  unfold kraw; simp [List.range_succ, sumInt, Balanced242Krawtchouk.altSign, Balanced242Krawtchouk.choose_zero]

private theorem evalWeighted_kraw_eq (a b c : Nat) (col : Triple) :
    ∀ (cert : List KrawEntry),
      evalWeighted ((cert.map (fun e => (krawRowVal a b c e, krawRowRhs a b c e, e.2.2.2))).map
        (fun r => (r.1, r.2.2))) col =
      sumInt (cert.map (fun e => e.2.2.2 * krawRowVal a b c e col))
  | [] => rfl
  | e :: t => by
    simp only [List.map_cons, evalWeighted, sumInt, evalWeighted_kraw_eq a b c col t]

private theorem evalRhs_kraw_eq (a b c : Nat) :
    ∀ (cert : List KrawEntry),
      evalRhs ((cert.map (fun e => (krawRowVal a b c e, krawRowRhs a b c e, e.2.2.2))).map
        (fun r => (r.2.1, r.2.2))) =
      sumInt (cert.map (fun e => e.2.2.2 * krawRowRhs a b c e))
  | [] => rfl
  | e :: t => by
    simp only [List.map_cons, evalRhs, sumInt, evalRhs_kraw_eq a b c t]

/-- Soundness of `checkAffineCert` against real `(f, g : Half)`. -/
theorem affine_cert_refute (f g : Half) (a b c : Nat)
    (ha : (suppList (clsA f g)).length = a)
    (hb : (suppList (clsB f g)).length = b)
    (hc : (suppList (clsC f g)).length = c)
    (cols : List Triple)
    (hmem : ∀ w : W 8, w ≠ zero 8 →
      canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ∈ cols)
    (cert : List KrawEntry)
    (hcheck : checkAffineCert a b c cols cert = true) : False := by
  unfold checkAffineCert at hcheck
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hvalid, hrhs_pos⟩, hcols_le⟩ := hcheck
  let classify (w : W 8) : Triple :=
    canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g))
  let rows : List ((Triple → Int) × Int × Int) :=
    cert.map (fun e => (krawRowVal a b c e, krawRowRhs a b c e, e.2.2.2))
  have hsound : ∀ r, r ∈ rows →
      (0 ≤ r.2.2 ∧ r.2.1 ≤ total 8 (fun v => nz v * r.1 (classify v))) ∨
      total 8 (fun v => nz v * r.1 (classify v)) = r.2.1 := by
    intro r hr
    rw [List.mem_map] at hr
    rcases hr with ⟨e, he, rfl⟩
    have hv := hvalid e he
    unfold affineEntryValid at hv
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
    rcases hv with ⟨heven, hdeg_or_wt⟩
    have hcanon (w : W 8) :
        krawRowVal a b c e (classify w) =
          kraw a (halfCnt w (clsA f g)) e.1 *
          kraw b (halfCnt w (clsB f g)) e.2.1 *
          kraw c (halfCnt w (clsC f g)) e.2.2.1 := by
      dsimp only [classify, canonPair, krawRowVal]
      simp only [krawFast_eq_kraw]
      split
      · rfl
      · have hflip := kraw_even_flip (clsA f g) (clsB f g) (clsC f g) w e.1 e.2.1 e.2.2.1 heven
        dsimp only at hflip
        rw [ha, hb, hc] at hflip
        have hfA : halfCntFalse w (clsA f g) = a - halfCnt w (clsA f g) := by
          have := halfCnt_add_false w (clsA f g); omega
        have hfB : halfCntFalse w (clsB f g) = b - halfCnt w (clsB f g) := by
          have := halfCnt_add_false w (clsB f g); omega
        have hfC : halfCntFalse w (clsC f g) = c - halfCnt w (clsC f g) := by
          have := halfCnt_add_false w (clsC f g); omega
        rw [← hfA, ← hfB, ← hfC]; exact hflip
    have hsum_eq : total 8 (fun w => nz w * krawRowVal a b c e (classify w)) =
        total 8 (fun w => nz w * (kraw a (halfCnt w (clsA f g)) e.1 *
          kraw b (halfCnt w (clsB f g)) e.2.1 * kraw c (halfCnt w (clsC f g)) e.2.2.1)) := by
      apply congrArg (total 8); funext w; rw [hcanon w]
    rw [hsum_eq]
    if hd0 : e.1 + e.2.1 + e.2.2.1 = 0 then
      right
      have he1 : e.1 = 0 := by omega
      have he2 : e.2.1 = 0 := by omega
      have he3 : e.2.2.1 = 0 := by omega
      unfold krawRowRhs
      simp only [hd0, beq_self_eq_true, if_true, he1, he2, he3]
      have h1 (w : W 8) : nz w * (kraw a (halfCnt w (clsA f g)) 0 *
          kraw b (halfCnt w (clsB f g)) 0 * kraw c (halfCnt w (clsC f g)) 0) = nz w * 1 := by
        rw [kraw_k0, kraw_k0, kraw_k0]; simp
      rw [funext h1, nz_total (fun _ => (1 : Int)), total_const, Int.mul_one]
      decide
    else
      unfold krawRowRhs
      simp only [chooseFast_eq_choose]
      have hbeq : (e.1 + e.2.1 + e.2.2.1 == 0) = false := beq_false_of_ne hd0
      rw [hbeq]; simp only [Bool.false_eq_true, if_false]
      if hd2 : e.1 + e.2.1 + e.2.2.1 = 2 then
        right
        have hd := cls_disj f g
        have h2 := kraw_triple_deg2_eq (clsA f g) (clsB f g) (clsC f g) hd.1 hd.2.1 hd.2.2
          e.1 e.2.1 e.2.2.1 hd2
        dsimp only at h2; rw [ha, hb, hc] at h2; exact h2
      else
        left
        have hwt : 0 ≤ e.2.2.2 := by
          rcases hdeg_or_wt with hle2 | hwt
          · exfalso; omega
          · exact hwt
        have hnn := (kraw_triple_nonneg_and_mod (clsA f g) (clsB f g) (clsC f g) e.1 e.2.1 e.2.2.1).1
        rw [ha, hb, hc] at hnn
        exact ⟨hwt, hnn⟩
  have heval_col (col : Triple) :
      evalWeighted (rows.map (fun r => (r.1, r.2.2))) col = evalAffineCol a b c cert col := by
    unfold evalAffineCol
    rw [foldl_add_eq, Int.zero_add]
    exact evalWeighted_kraw_eq a b c col cert
  have heval_rhs : evalRhs (rows.map (fun r => (r.2.1, r.2.2))) = evalAffineRhs a b c cert := by
    unfold evalAffineRhs
    rw [foldl_add_eq, Int.zero_add]
    exact evalRhs_kraw_eq a b c cert
  exact farkas_refute classify cols hmem rows hsound
    (fun col hcol => by rw [heval_col col]; exact hcols_le col hcol)
    (by rw [heval_rhs]; exact hrhs_pos)

/-! ## Part 9: Anchor-Pair 14-Equality Separable Fast Verifier (`checkCondCertFast`) -/

/-- Unpacked 14 Farkas multipliers for `conditional`: `(w0, w1, wl0..wl5, wh0..wh5)`. -/
structure CondWeights where
  w0 : Int
  w1 : Int
  wl0 : Int
  wl1 : Int
  wl2 : Int
  wl3 : Int
  wl4 : Int
  wl5 : Int
  wh0 : Int
  wh1 : Int
  wh2 : Int
  wh3 : Int
  wh4 : Int
  wh5 : Int

def getW (ws : List (Nat × Int)) (idx : Nat) : Int :=
  ws.foldl (fun acc p => if p.1 == idx then acc + p.2 else acc) 0

def unpackCondWeights (ws : List (Nat × Int)) : CondWeights :=
  ⟨getW ws 0, getW ws 1,
   getW ws 2, getW ws 3, getW ws 4, getW ws 5, getW ws 6, getW ws 7,
   getW ws 8, getW ws 9, getW ws 10, getW ws 11, getW ws 12, getW ws 13⟩

def scoreMoments (c0 c1 c2 c3 c4 c5 : Int) (n p : Triple) : Int :=
  let A : Int := 2 * (p.1 : Int) - (n.1 : Int)
  let B : Int := 2 * (p.2.1 : Int) - (n.2.1 : Int)
  let C : Int := 2 * (p.2.2 : Int) - (n.2.2 : Int)
  c0 * (A * A) + c1 * (B * B) + c2 * (C * C) + c3 * (A * B) + c4 * (A * C) + c5 * (B * C)

def scoreTargets (c0 c1 c2 c3 c4 c5 : Int) (n : Triple) : Int :=
  let a : Int := n.1; let b : Int := n.2.1; let c : Int := n.2.2
  c0 * (a * (128 - a)) + c1 * (b * (128 - b)) + c2 * (c * (128 - c)) +
  c3 * (-(a * b)) + c4 * (-(a * c)) + c5 * (-(b * c))

def condRhs (lo hi : Triple) (W : CondWeights) : Int :=
  W.w0 * 127 + W.w1 * 63 +
  scoreTargets W.wl0 W.wl1 W.wl2 W.wl3 W.wl4 W.wl5 lo +
  scoreTargets W.wh0 W.wh1 W.wh2 W.wh3 W.wh4 W.wh5 hi

def scoreLo (lo : Triple) (W : CondWeights) (r : Nat) (p : Triple) : Int :=
  W.w0 + (if r == 4 then W.w1 else 0) +
  scoreMoments W.wl0 W.wl1 W.wl2 W.wl3 W.wl4 W.wl5 lo p

def scoreHi (hi : Triple) (W : CondWeights) (v : Triple) : Int :=
  scoreMoments W.wh0 W.wh1 W.wh2 W.wh3 W.wh4 W.wh5 hi v

def listMaxInt : List Int → Int → Int
  | [], m => m
  | x :: t, m => listMaxInt t (if m ≤ x then x else m)

private theorem listMaxInt_base : ∀ (L : List Int) (m : Int), m ≤ listMaxInt L m
  | [], m => Int.le_refl m
  | b :: rest, m => by
    unfold listMaxInt
    have h1 := listMaxInt_base rest (if m ≤ b then b else m)
    if h : m ≤ b then
      rw [if_pos h] at h1 ⊢; omega
    else
      rw [if_neg h] at h1 ⊢; omega

private theorem listMaxInt_ge : ∀ (L : List Int) (m x : Int),
    x ∈ L → x ≤ listMaxInt L m
  | [], _, _, h => nomatch h
  | a :: t, m, x, h => by
    unfold listMaxInt
    rcases List.mem_cons.mp h with rfl | ht
    · have h1 := listMaxInt_base t (if m ≤ x then x else m)
      if hc : m ≤ x then
        rw [if_pos hc] at h1 ⊢; omega
      else
        rw [if_neg hc] at h1 ⊢; omega
    · exact listMaxInt_ge t _ x ht

/-- Check one rank `r ∈ {4, 6}` of `localrows` using separable max-pruning and `O(1)` bitset lookup. -/
def checkCondRankFast (lo hi : Triple) (allowedMask : Nat) (W : CondWeights) (r : Nat) : Bool :=
  let subL := genSubtypes lo r
  let subH := genSubtypes hi r
  let hiScored := subH.map (fun v => (v, scoreHi hi W v))
  match hiScored with
  | [] => true
  | (_, s0) :: rest =>
    let maxH := listMaxInt (rest.map Prod.snd) s0
    subL.all fun p =>
      let sL := scoreLo lo W r p
      if decide (sL + maxH ≤ 0) then true
      else hiScored.all fun (v, sH) =>
        if decide (sL + sH ≤ 0) then true
        else
          let pv : Triple := (p.1 + v.1, p.2.1 + v.2.1, p.2.2 + v.2.2)
          let pw : Triple := (p.1 + (hi.1 - v.1), p.2.1 + (hi.2.1 - v.2.1), p.2.2 + (hi.2.2 - v.2.2))
          !(inAllowedMask allowedMask pv && inAllowedMask allowedMask pw)

/-- Fast separable verifier for a 14-row anchor-pair Farkas certificate. -/
def checkCondCertFast (lo hi : Triple) (allowedMask : Nat) (ws : List (Nat × Int)) : Bool :=
  let W := unpackCondWeights ws
  decide (0 < condRhs lo hi W) &&
  checkCondRankFast lo hi allowedMask W 4 &&
  checkCondRankFast lo hi allowedMask W 6

private theorem checkCondRankFast_sound (lo hi : Triple) (allowedMask : Nat) (W : CondWeights) (r : Nat)
    (hok : checkCondRankFast lo hi allowedMask W r = true)
    (p v : Triple) (hp : p ∈ genSubtypes lo r) (hv : v ∈ genSubtypes hi r)
    (hpv : inAllowedMask allowedMask (p.1 + v.1, p.2.1 + v.2.1, p.2.2 + v.2.2) = true)
    (hpw : inAllowedMask allowedMask (p.1 + (hi.1 - v.1), p.2.1 + (hi.2.1 - v.2.1), p.2.2 + (hi.2.2 - v.2.2)) = true) :
    scoreLo lo W r p + scoreHi hi W v ≤ 0 := by
  unfold checkCondRankFast at hok
  dsimp only at hok
  cases hhs : (genSubtypes hi r).map (fun v => (v, scoreHi hi W v)) with
  | nil =>
    have hmem : (v, scoreHi hi W v) ∈ (genSubtypes hi r).map (fun v => (v, scoreHi hi W v)) :=
      List.mem_map.mpr ⟨v, hv, rfl⟩
    rw [hhs] at hmem; exact nomatch hmem
  | cons hd rest =>
    rw [hhs] at hok
    dsimp only at hok
    rw [List.all_eq_true] at hok
    have hp_ok := hok p hp
    if hmax : scoreLo lo W r p + listMaxInt (rest.map Prod.snd) hd.2 ≤ 0 then
      have hmem : (v, scoreHi hi W v) ∈ hd :: rest := by
        rw [← hhs]; exact List.mem_map.mpr ⟨v, hv, rfl⟩
      have hle_max : scoreHi hi W v ≤ listMaxInt (rest.map Prod.snd) hd.2 := by
        rcases List.mem_cons.mp hmem with heq | htail
        · have : scoreHi hi W v = hd.2 := congrArg Prod.snd heq
          rw [this]; exact listMaxInt_base _ _
        · exact listMaxInt_ge (rest.map Prod.snd) hd.2 (scoreHi hi W v)
            (List.mem_map.mpr ⟨(v, scoreHi hi W v), htail, rfl⟩)
      omega
    else
      simp only [decide_eq_false hmax, Bool.false_eq_true, if_false] at hp_ok
      rw [List.all_eq_true] at hp_ok
      have hmem : (v, scoreHi hi W v) ∈ hd :: rest := by
        rw [← hhs]; exact List.mem_map.mpr ⟨v, hv, rfl⟩
      have hv_ok := hp_ok (v, scoreHi hi W v) hmem
      if hle : scoreLo lo W r p + scoreHi hi W v ≤ 0 then
        exact hle
      else
        simp only [decide_eq_false hle, Bool.false_eq_true, if_false, hpv, hpw,
          Bool.and_self, Bool.not_true] at hv_ok

private theorem moments_canon_eq (n : Triple) (p : Triple) (h1 : p.1 ≤ n.1) (h2 : p.2.1 ≤ n.2.1) (h3 : p.2.2 ≤ n.2.2)
    (c0 c1 c2 c3 c4 c5 : Int) :
    scoreMoments c0 c1 c2 c3 c4 c5 n (canonPair n.1 n.2.1 n.2.2 p.1 p.2.1 p.2.2) =
      scoreMoments c0 c1 c2 c3 c4 c5 n p := by
  unfold canonPair
  dsimp only
  split
  · rfl
  · unfold scoreMoments
    have e1 : 2 * ((n.1 - p.1 : Nat) : Int) - (n.1 : Int) = -(2 * (p.1 : Int) - (n.1 : Int)) := by omega
    have e2 : 2 * ((n.2.1 - p.2.1 : Nat) : Int) - (n.2.1 : Int) = -(2 * (p.2.1 : Int) - (n.2.1 : Int)) := by omega
    have e3 : 2 * ((n.2.2 - p.2.2 : Nat) : Int) - (n.2.2 : Int) = -(2 * (p.2.2 : Int) - (n.2.2 : Int)) := by omega
    rw [e1, e2, e3]
    simp only [Int.neg_mul_neg]

private theorem choose_one_eq : ∀ (n : Nat), choose n 1 = (n : Int)
  | 0 => rfl
  | n + 1 => by rw [Balanced242Krawtchouk.choose_succ_succ, Balanced242Krawtchouk.choose_zero, choose_one_eq n]; omega

private theorem kraw_one_eq (s x : Nat) (hx : x ≤ s) :
    kraw s x 1 = (s : Int) - 2 * (x : Int) := by
  have ha0 : Balanced242Krawtchouk.altSign 0 = 1 := rfl
  have ha1 : Balanced242Krawtchouk.altSign 1 = -1 := rfl
  unfold kraw
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, sumInt, Balanced242Krawtchouk.sumInt_append, ha0, ha1,
    Nat.sub_zero, Nat.sub_self, Balanced242Krawtchouk.choose_zero, choose_one_eq]
  omega

private theorem choose_two_eq : ∀ (n : Nat), 2 * choose n 2 = (n : Int) * ((n : Int) - 1)
  | 0 => rfl
  | n + 1 => by
    rw [Balanced242Krawtchouk.choose_succ_succ, Int.mul_add, choose_two_eq n, choose_one_eq n]
    have hexp : ((n + 1 : Nat) : Int) * (((n + 1 : Nat) : Int) - 1) = (n : Int) * (n : Int) + (n : Int) := by
      have : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
      rw [this, Int.add_sub_cancel, Int.add_mul, Int.one_mul]
    have hexp2 : (n : Int) * ((n : Int) - 1) = (n : Int) * (n : Int) - (n : Int) := by
      rw [Int.mul_sub, Int.mul_one]
    rw [hexp, hexp2]; omega

private theorem kraw_two_eq (s x : Nat) (hx : x ≤ s) :
    2 * kraw s x 2 + (s : Int) = (2 * (x : Int) - (s : Int)) * (2 * (x : Int) - (s : Int)) := by
  have ha0 : Balanced242Krawtchouk.altSign 0 = 1 := rfl
  have ha1 : Balanced242Krawtchouk.altSign 1 = -1 := rfl
  have ha2 : Balanced242Krawtchouk.altSign 2 = 1 := rfl
  have hs21 : 2 - 1 = 1 := rfl
  unfold kraw
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, sumInt, Balanced242Krawtchouk.sumInt_append, ha0, ha1, ha2,
    Nat.sub_zero, Nat.sub_self, hs21, Balanced242Krawtchouk.choose_zero, choose_one_eq]
  simp only [Int.one_mul, Int.mul_one, Int.add_zero, Int.zero_add, Int.mul_add]
  have h2a := choose_two_eq (s - x)
  have h2b := choose_two_eq x
  have hsub : ((s - x : Nat) : Int) = (s : Int) - (x : Int) := by omega
  rw [h2a, h2b, hsub]
  have e1 : ((s : Int) - (x : Int)) * ((s : Int) - (x : Int) - 1) =
      (s : Int) * (s : Int) - 2 * ((s : Int) * (x : Int)) + (x : Int) * (x : Int) - (s : Int) + (x : Int) := by
    simp only [Int.sub_mul, Int.mul_sub, Int.mul_one]
    have : (x : Int) * (s : Int) = (s : Int) * (x : Int) := Int.mul_comm _ _
    rw [this]; omega
  have e2 : 2 * (-1 * (x : Int) * ((s : Int) - (x : Int))) =
      -2 * ((s : Int) * (x : Int)) + 2 * ((x : Int) * (x : Int)) := by
    simp only [Int.neg_mul, Int.one_mul, Int.mul_sub]
    have : (x : Int) * (s : Int) = (s : Int) * (x : Int) := Int.mul_comm _ _
    rw [this]; omega
  have e3 : (x : Int) * ((x : Int) - 1) = (x : Int) * (x : Int) - (x : Int) := by
    rw [Int.mul_sub, Int.mul_one]
  have e4 : (2 * (x : Int) - (s : Int)) * (2 * (x : Int) - (s : Int)) =
      4 * ((x : Int) * (x : Int)) - 4 * ((s : Int) * (x : Int)) + (s : Int) * (s : Int) := by
    simp only [Int.sub_mul, Int.mul_sub]
    have a1 : 2 * (x : Int) * (2 * (x : Int)) = 4 * ((x : Int) * (x : Int)) := by
      have : 2 * (x : Int) * (2 * (x : Int)) = (2 * 2) * ((x : Int) * (x : Int)) := by ac_rfl
      rw [this]; rfl
    have a2 : 2 * (x : Int) * (s : Int) = 2 * ((s : Int) * (x : Int)) := by ac_rfl
    have a3 : (s : Int) * (2 * (x : Int)) = 2 * ((s : Int) * (x : Int)) := by ac_rfl
    rw [a1, a2, a3]; omega
  rw [e1, e2, e3, e4]; omega

/-- Degree-2 Parseval/moment equalities on `W 7` for any pairwise disjoint `P, Q, R`. -/
private theorem moment_sums_W7 (P Q R : W 7 → Bool)
    (hPQ : ∀ x, (P x && Q x) = false) (hPR : ∀ x, (P x && R x) = false)
    (hQR : ∀ x, (Q x && R x) = false) :
    let a := (suppList P).length
    let b := (suppList Q).length
    let c := (suppList R).length
    let A (v : W 7) : Int := 2 * (halfCnt v P : Int) - (a : Int)
    let B (v : W 7) : Int := 2 * (halfCnt v Q : Int) - (b : Int)
    let C (v : W 7) : Int := 2 * (halfCnt v R : Int) - (c : Int)
    total 7 (fun v => nz v * (A v * A v)) = (a : Int) * (128 - (a : Int)) ∧
    total 7 (fun v => nz v * (B v * B v)) = (b : Int) * (128 - (b : Int)) ∧
    total 7 (fun v => nz v * (C v * C v)) = (c : Int) * (128 - (c : Int)) ∧
    total 7 (fun v => nz v * (A v * B v)) = -((a : Int) * (b : Int)) ∧
    total 7 (fun v => nz v * (A v * C v)) = -((a : Int) * (c : Int)) ∧
    total 7 (fun v => nz v * (B v * C v)) = -((b : Int) * (c : Int)) := by
  intro a b c A B C
  have hsq (S : W 7 → Bool) :
      let s := (suppList S).length
      total 7 (fun v => nz v * ((2 * (halfCnt v S : Int) - (s : Int)) *
          (2 * (halfCnt v S : Int) - (s : Int)))) = (s : Int) * (128 - (s : Int)) := by
    intro s
    have hdisjF : ∀ x, (S x && false) = false := fun _ => Bool.and_false _
    have hk := kraw_triple_deg2_eq S (fun _ => false) (fun _ => false) hdisjF hdisjF
      (fun _ => rfl) 2 0 0 rfl
    dsimp only at hk
    have hpt (v : W 7) :
        nz v * ((2 * (halfCnt v S : Int) - (s : Int)) * (2 * (halfCnt v S : Int) - (s : Int))) =
        2 * (nz v * (kraw s (halfCnt v S) 2 * kraw (suppList (fun _ : W 7 => false)).length (halfCnt v (fun _ : W 7 => false)) 0 *
          kraw (suppList (fun _ : W 7 => false)).length (halfCnt v (fun _ : W 7 => false)) 0)) + nz v * (s : Int) := by
      rw [kraw_k0, Int.mul_one, Int.mul_one, ← kraw_two_eq s (halfCnt v S) (halfCnt_le v S),
          Int.mul_add, Int.mul_left_comm]
    rw [funext hpt, total_add, total_scale, hk]
    have hnzs : total 7 (fun v => nz v * (s : Int)) = 127 * (s : Int) := by
      rw [nz_total (fun _ => (s : Int)), total_const]
      have h128 : many 7 = 128 := by decide
      rw [h128]; omega
    rw [hnzs, Balanced242Krawtchouk.choose_zero, Int.mul_one, Int.mul_one]
    have h2c := choose_two_eq s
    have halg : (s : Int) * (128 - (s : Int)) = 127 * (s : Int) - (s : Int) * ((s : Int) - 1) := by
      simp only [Int.mul_sub, Int.mul_one]; omega
    rw [Int.mul_neg, h2c]; omega
  have hcross (S T : W 7 → Bool) (hST : ∀ x, (S x && T x) = false) :
      let s := (suppList S).length
      let t := (suppList T).length
      total 7 (fun v => nz v * ((2 * (halfCnt v S : Int) - (s : Int)) *
          (2 * (halfCnt v T : Int) - (t : Int)))) = -((s : Int) * (t : Int)) := by
    intro s t
    have hdisjF1 : ∀ x, (S x && false) = false := fun _ => Bool.and_false _
    have hdisjF2 : ∀ x, (T x && false) = false := fun _ => Bool.and_false _
    have hk := kraw_triple_deg2_eq S T (fun _ => false) hST hdisjF1 hdisjF2 1 1 0 rfl
    dsimp only at hk
    have hpt (v : W 7) :
        nz v * ((2 * (halfCnt v S : Int) - (s : Int)) * (2 * (halfCnt v T : Int) - (t : Int))) =
        nz v * (kraw s (halfCnt v S) 1 * kraw t (halfCnt v T) 1 *
          kraw (suppList (fun _ : W 7 => false)).length (halfCnt v (fun _ : W 7 => false)) 0) := by
      rw [kraw_k0, Int.mul_one, kraw_one_eq s (halfCnt v S) (halfCnt_le v S),
          kraw_one_eq t (halfCnt v T) (halfCnt_le v T)]
      have h1 : (s : Int) - 2 * (halfCnt v S : Int) = -(2 * (halfCnt v S : Int) - (s : Int)) := by omega
      have h2 : (t : Int) - 2 * (halfCnt v T : Int) = -(2 * (halfCnt v T : Int) - (t : Int)) := by omega
      rw [h1, h2, Int.neg_mul_neg]
    rw [funext hpt, hk, choose_one_eq s, choose_one_eq t, Balanced242Krawtchouk.choose_zero, Int.mul_one]
  exact ⟨hsq P, hsq Q, hsq R, hcross P Q hPQ, hcross P R hPR, hcross Q R hQR⟩

private theorem triple_ext {a1 b1 c1 a2 b2 c2 : Nat}
    (h1 : a1 = a2) (h2 : b1 = b2) (h3 : c1 = c2) : (a1, b1, c1) = (a2, b2, c2) := by
  rw [h1, h2, h3]

private theorem sub_add_eq {a l h p q x y : Nat}
    (hlh : l + h = a) (hpl : p ≤ l) (hqh : q ≤ h) (hxy : x + y = a) (hx : x = (l - p) + q) :
    p + (h - q) = y := by omega

private theorem sub_add_eq_comm {a l h p q x y : Nat}
    (hlh : l + h = a) (hpl : p ≤ l) (hqh : q ≤ h) (hxy : x + y = a) (hx : x = (h - q) + p) :
    (l - p) + q = y := by omega

private theorem add_eq_of_sub {a l h p q x y : Nat}
    (hlh : l + h = a) (hpl : p ≤ l) (hqh : q ≤ h) (hxy : x + y = a) (hx : x = (l - p) + (h - q)) :
    p + q = y := by omega

private theorem add_eq_of_sub_comm {a l h p q x y : Nat}
    (hlh : l + h = a) (hpl : p ≤ l) (hqh : q ≤ h) (hxy : x + y = a) (hx : x = (h - q) + (l - p)) :
    p + q = y := by omega

/-- Soundness of `checkCondCertFast`: if `checkCondCertFast lo hi allowedMask ws = true`,
    then NO nonzero anchor direction `w` of `(f, g)` can have canonical split `lo`
    (assuming every nonzero direction of `(f, g)` maps both its halves into `allowedMask`). -/
theorem cond_cert_refute (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (hrr : rr (β8 f g) = 1) (a b c : Nat)
    (ha : (suppList (clsA f g)).length = a)
    (hb : (suppList (clsB f g)).length = b)
    (hc : (suppList (clsC f g)).length = c)
    (allowedMask : Nat)
    (hallow : ∀ u : W 8, u ≠ zero 8 →
      inAllowedMask allowedMask (halfCntFalse u (clsA f g), halfCntFalse u (clsB f g), halfCntFalse u (clsC f g)) = true ∧
      inAllowedMask allowedMask (halfCnt u (clsA f g), halfCnt u (clsB f g), halfCnt u (clsC f g)) = true)
    (w : W 8) (hw : w ≠ zero 8)
    (lo : Triple)
    (hlo_eq : canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) = lo)
    (ws : List (Nat × Int))
    (hcheck : checkCondCertFast lo (a - lo.1, b - lo.2.1, c - lo.2.2) allowedMask ws = true) : False := by
  -- Pick `c0 : Bool` so that the `c0` half has counts `lo` and the `!c0` half has counts `hi`!
  let hiT : Triple := (a - lo.1, b - lo.2.1, c - lo.2.2)
  have hleA : halfCnt w (clsA f g) ≤ a := ha ▸ halfCnt_le w (clsA f g)
  have hleB : halfCnt w (clsB f g) ≤ b := hb ▸ halfCnt_le w (clsB f g)
  have hleC : halfCnt w (clsC f g) ≤ c := hc ▸ halfCnt_le w (clsC f g)
  let flip : Bool := tripleLe (halfCnt w (clsA f g), halfCnt w (clsB f g), halfCnt w (clsC f g))
    (a - halfCnt w (clsA f g), b - halfCnt w (clsB f g), c - halfCnt w (clsC f g))
  -- `cLo = flip` (`true` if `halfCnt` is `lo`, `false` if `halfCntFalse` is `lo`)
  let cLo : Bool := flip
  let cHi : Bool := !flip
  let A_lo (x : W 7) := clsA f g (secPt 7 w cLo x)
  let B_lo (x : W 7) := clsB f g (secPt 7 w cLo x)
  let C_lo (x : W 7) := clsC f g (secPt 7 w cLo x)
  let A_hi (x : W 7) := clsA f g (secPt 7 w cHi x)
  let B_hi (x : W 7) := clsB f g (secPt 7 w cHi x)
  let C_hi (x : W 7) := clsC f g (secPt 7 w cHi x)
  have hlo_cnts : (suppList A_lo).length = lo.1 ∧ (suppList B_lo).length = lo.2.1 ∧ (suppList C_lo).length = lo.2.2 := by
    have sA := sec_suppList_eq_halfCnt w hw (clsA f g)
    have sB := sec_suppList_eq_halfCnt w hw (clsB f g)
    have sC := sec_suppList_eq_halfCnt w hw (clsC f g)
    have fA : halfCntFalse w (clsA f g) = a - halfCnt w (clsA f g) := by
      have := halfCnt_add_false w (clsA f g); omega
    have fB : halfCntFalse w (clsB f g) = b - halfCnt w (clsB f g) := by
      have := halfCnt_add_false w (clsB f g); omega
    have fC : halfCntFalse w (clsC f g) = c - halfCnt w (clsC f g) := by
      have := halfCnt_add_false w (clsC f g); omega
    dsimp only [A_lo, B_lo, C_lo, cLo, flip]
    unfold canonPair at hlo_eq
    cases hfl : tripleLe (halfCnt w (clsA f g), halfCnt w (clsB f g), halfCnt w (clsC f g))
        (a - halfCnt w (clsA f g), b - halfCnt w (clsB f g), c - halfCnt w (clsC f g))
    · simp only [hfl, Bool.false_eq_true, if_false] at hlo_eq
      rw [← hlo_eq]; exact ⟨sA.1.trans fA, sB.1.trans fB, sC.1.trans fC⟩
    · simp only [hfl, if_true] at hlo_eq
      rw [← hlo_eq]; exact ⟨sA.2, sB.2, sC.2⟩
  have hhi_cnts : (suppList A_hi).length = hiT.1 ∧ (suppList B_hi).length = hiT.2.1 ∧ (suppList C_hi).length = hiT.2.2 := by
    have sA := sec_suppList_eq_halfCnt w hw (clsA f g)
    have sB := sec_suppList_eq_halfCnt w hw (clsB f g)
    have sC := sec_suppList_eq_halfCnt w hw (clsC f g)
    have fA : halfCntFalse w (clsA f g) = a - halfCnt w (clsA f g) := by
      have := halfCnt_add_false w (clsA f g); omega
    have fB : halfCntFalse w (clsB f g) = b - halfCnt w (clsB f g) := by
      have := halfCnt_add_false w (clsB f g); omega
    have fC : halfCntFalse w (clsC f g) = c - halfCnt w (clsC f g) := by
      have := halfCnt_add_false w (clsC f g); omega
    dsimp only [A_hi, B_hi, C_hi, cHi, hiT, flip]
    unfold canonPair at hlo_eq
    cases hfl : tripleLe (halfCnt w (clsA f g), halfCnt w (clsB f g), halfCnt w (clsC f g))
        (a - halfCnt w (clsA f g), b - halfCnt w (clsB f g), c - halfCnt w (clsC f g))
    · simp only [hfl, Bool.false_eq_true, if_false] at hlo_eq
      rw [← hlo_eq, Nat.sub_sub_self hleA, Nat.sub_sub_self hleB, Nat.sub_sub_self hleC]
      exact ⟨sA.2, sB.2, sC.2⟩
    · simp only [hfl, if_true] at hlo_eq
      rw [← hlo_eq]; exact ⟨sA.1.trans fA, sB.1.trans fB, sC.1.trans fC⟩
  unfold checkCondCertFast at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hrhs_pos, hok4⟩, hok6⟩ := hcheck
  let cw := unpackCondWeights ws
  let β0 (a : W 7) := β8 f g (secPt 7 w false a)
  have hcube8 : Cube (β8 f g) := Balanced242Global.cube8 f g res
  have hanch := anchor_pair_ranks_63_64 (β8 f g) hcube8 hrr w hw
  dsimp only at hanch
  -- Direct pointwise upper bound: for every `v ≠ 0` in `W 7`,
  -- `scoreLo lo cw r_v p_v + scoreHi hiT cw q_v ≤ 0`!
  let F (v : W 7) : Int :=
    let r := if perp β0 v then 4 else 6
    let p : Triple := (halfCnt v A_lo, halfCnt v B_lo, halfCnt v C_lo)
    let q : Triple := (halfCnt v A_hi, halfCnt v B_hi, halfCnt v C_hi)
    scoreLo lo cw r p + scoreHi hiT cw q
  have hF_le (v : W 7) (hv : v ≠ zero 7) : F v ≤ 0 := by
    let r := if perp β0 v then 4 else 6
    let pRaw : Triple := (halfCnt v A_lo, halfCnt v B_lo, halfCnt v C_lo)
    let qRaw : Triple := (halfCnt v A_hi, halfCnt v B_hi, halfCnt v C_hi)
    have hp_le : pRaw.1 ≤ lo.1 ∧ pRaw.2.1 ≤ lo.2.1 ∧ pRaw.2.2 ≤ lo.2.2 :=
      ⟨hlo_cnts.1 ▸ halfCnt_le v A_lo, hlo_cnts.2.1 ▸ halfCnt_le v B_lo, hlo_cnts.2.2 ▸ halfCnt_le v C_lo⟩
    have hq_le : qRaw.1 ≤ hiT.1 ∧ qRaw.2.1 ≤ hiT.2.1 ∧ qRaw.2.2 ≤ hiT.2.2 :=
      ⟨hhi_cnts.1 ▸ halfCnt_le v A_hi, hhi_cnts.2.1 ▸ halfCnt_le v B_hi, hhi_cnts.2.2 ▸ halfCnt_le v C_hi⟩
    let pC := canonPair lo.1 lo.2.1 lo.2.2 pRaw.1 pRaw.2.1 pRaw.2.2
    let qC := canonPair hiT.1 hiT.2.1 hiT.2.2 qRaw.1 qRaw.2.1 qRaw.2.2
    have hscore_eq : F v = scoreLo lo cw r pC + scoreHi hiT cw qC := by
      dsimp only [F, scoreLo, scoreHi]
      rw [moments_canon_eq lo pRaw hp_le.1 hp_le.2.1 hp_le.2.2,
          moments_canon_eq hiT qRaw hq_le.1 hq_le.2.1 hq_le.2.2]
    rw [hscore_eq]
    have hp_six_T := sixOK_of_subsection f g res hicap hrr w hw cLo v hv true
    have hp_six_F := sixOK_of_subsection f g res hicap hrr w hw cLo v hv false
    have hq_six_T := sixOK_of_subsection f g res hicap hrr w hw cHi v hv true
    have hq_six_F := sixOK_of_subsection f g res hicap hrr w hw cHi v hv false
    dsimp only at hp_six_T hp_six_F hq_six_T hq_six_F
    have sLoA := sec_suppList_eq_halfCnt v hv A_lo
    have sLoB := sec_suppList_eq_halfCnt v hv B_lo
    have sLoC := sec_suppList_eq_halfCnt v hv C_lo
    have sHiA := sec_suppList_eq_halfCnt v hv A_hi
    have sHiB := sec_suppList_eq_halfCnt v hv B_hi
    have sHiC := sec_suppList_eq_halfCnt v hv C_hi
    have hcLoA : halfCntFalse v A_lo = lo.1 - pRaw.1 := by
      have := halfCnt_add_false v A_lo; rw [hlo_cnts.1] at this; dsimp only [pRaw]; omega
    have hcLoB : halfCntFalse v B_lo = lo.2.1 - pRaw.2.1 := by
      have := halfCnt_add_false v B_lo; rw [hlo_cnts.2.1] at this; dsimp only [pRaw]; omega
    have hcLoC : halfCntFalse v C_lo = lo.2.2 - pRaw.2.2 := by
      have := halfCnt_add_false v C_lo; rw [hlo_cnts.2.2] at this; dsimp only [pRaw]; omega
    have hcHiA : halfCntFalse v A_hi = hiT.1 - qRaw.1 := by
      have h := halfCnt_add_false v A_hi; rw [hhi_cnts.1] at h; change halfCntFalse v A_hi = hiT.1 - halfCnt v A_hi; omega
    have hcHiB : halfCntFalse v B_hi = hiT.2.1 - qRaw.2.1 := by
      have h := halfCnt_add_false v B_hi; rw [hhi_cnts.2.1] at h; change halfCntFalse v B_hi = hiT.2.1 - halfCnt v B_hi; omega
    have hcHiC : halfCntFalse v C_hi = hiT.2.2 - qRaw.2.2 := by
      have h := halfCnt_add_false v C_hi; rw [hhi_cnts.2.2] at h; change halfCntFalse v C_hi = hiT.2.2 - halfCnt v C_hi; omega
    rw [sLoA.2, sLoB.2, sLoC.2] at hp_six_T
    rw [sLoA.1, sLoB.1, sLoC.1, hcLoA, hcLoB, hcLoC] at hp_six_F
    rw [sHiA.2, sHiB.2, sHiC.2] at hq_six_T
    rw [sHiA.1, sHiB.1, sHiC.1, hcHiA, hcHiB, hcHiC] at hq_six_F
    have hp_mem : pC ∈ genSubtypes lo r :=
      mem_genSubtypes hp_le.1 hp_le.2.1 hp_le.2.2 hp_six_T hp_six_F
    have hq_mem : qC ∈ genSubtypes hiT r :=
      mem_genSubtypes hq_le.1 hq_le.2.1 hq_le.2.2 hq_six_T hq_six_F
    -- Now prove BOTH `pC + qC` and `pC + (hiT - qC)` are in `allowedMask` using `quarter_hyperplane_counts`!
    have hqA := quarter_hyperplane_counts (clsA f g) w hw v
    have hqB := quarter_hyperplane_counts (clsB f g) w hw v
    have hqC := quarter_hyperplane_counts (clsC f g) w hw v
    dsimp only at hqA hqB hqC
    let u0 := liftPt 7 w v
    let u1 := add 8 w u0
    have hu0 : u0 ≠ zero 8 := liftPt_ne_zero 7 w hw v hv
    have hu1 : u1 ≠ zero 8 := add_liftPt_ne_zero 7 w hw v
    have hallow_pair (bP bQ : Bool) :
        let pT : Triple := if bP then pRaw else (lo.1 - pRaw.1, lo.2.1 - pRaw.2.1, lo.2.2 - pRaw.2.2)
        let qT : Triple := if bQ then qRaw else (hiT.1 - qRaw.1, hiT.2.1 - qRaw.2.1, hiT.2.2 - qRaw.2.2)
        inAllowedMask allowedMask (pT.1 + qT.1, pT.2.1 + qT.2.1, pT.2.2 + qT.2.2) = true := by
      have hu0_ok := hallow u0 hu0
      have hu1_ok := hallow u1 hu1
      have hu0A := halfCnt_add_false u0 (clsA f g); rw [ha] at hu0A
      have hu0B := halfCnt_add_false u0 (clsB f g); rw [hb] at hu0B
      have hu0C := halfCnt_add_false u0 (clsC f g); rw [hc] at hu0C
      have hu1A := halfCnt_add_false u1 (clsA f g); rw [ha] at hu1A
      have hu1B := halfCnt_add_false u1 (clsB f g); rw [hb] at hu1B
      have hu1C := halfCnt_add_false u1 (clsC f g); rw [hc] at hu1C
      have hlo_le : lo.1 ≤ a ∧ lo.2.1 ≤ b ∧ lo.2.2 ≤ c := by
        rw [← hlo_eq]; unfold canonPair; dsimp only; split <;> dsimp only <;> omega
      have hlo_hi_A : lo.1 + hiT.1 = a := by dsimp only [hiT]; omega
      have hlo_hi_B : lo.2.1 + hiT.2.1 = b := by dsimp only [hiT]; omega
      have hlo_hi_C : lo.2.2 + hiT.2.2 = c := by dsimp only [hiT]; omega
      -- Case-split on `flip`, `bP`, `bQ` and match each of the 4 sums to `u0`/`u1` false/true half!
      dsimp only
      have hfl_cases : (cLo = false ∧ cHi = true) ∨ (cLo = true ∧ cHi = false) := by
        dsimp only [cLo, cHi]; cases flip <;> simp
      rcases hfl_cases with ⟨hcL, hcH⟩ | ⟨hcL, hcH⟩
      · -- `A_lo = false half`, `A_hi = true half`
        have eLA : halfCntFalse v (fun a => clsA f g (secPt 7 w false a)) = lo.1 - pRaw.1 := by
          rw [← hcLoA]; dsimp only [A_lo]; rw [hcL]
        have eLB : halfCntFalse v (fun a => clsB f g (secPt 7 w false a)) = lo.2.1 - pRaw.2.1 := by
          rw [← hcLoB]; dsimp only [B_lo]; rw [hcL]
        have eLC : halfCntFalse v (fun a => clsC f g (secPt 7 w false a)) = lo.2.2 - pRaw.2.2 := by
          rw [← hcLoC]; dsimp only [C_lo]; rw [hcL]
        have eHA : halfCntFalse v (fun a => clsA f g (secPt 7 w true a)) = hiT.1 - qRaw.1 := by
          rw [← hcHiA]; dsimp only [A_hi]; rw [hcH]
        have eHB : halfCntFalse v (fun a => clsB f g (secPt 7 w true a)) = hiT.2.1 - qRaw.2.1 := by
          rw [← hcHiB]; dsimp only [B_hi]; rw [hcH]
        have eHC : halfCntFalse v (fun a => clsC f g (secPt 7 w true a)) = hiT.2.2 - qRaw.2.2 := by
          rw [← hcHiC]; dsimp only [C_hi]; rw [hcH]
        have eHT_A : halfCnt v (fun a => clsA f g (secPt 7 w true a)) = qRaw.1 := by
          dsimp only [qRaw, A_hi]; rw [hcH]
        have eHT_B : halfCnt v (fun a => clsB f g (secPt 7 w true a)) = qRaw.2.1 := by
          dsimp only [qRaw, B_hi]; rw [hcH]
        have eHT_C : halfCnt v (fun a => clsC f g (secPt 7 w true a)) = qRaw.2.2 := by
          dsimp only [qRaw, C_hi]; rw [hcH]
        cases bP <;> cases bQ
        · -- false, false => `halfCntFalse u0`
          have eq1 : (lo.1 - pRaw.1 + (hiT.1 - qRaw.1), lo.2.1 - pRaw.2.1 + (hiT.2.1 - qRaw.2.1),
              lo.2.2 - pRaw.2.2 + (hiT.2.2 - qRaw.2.2)) =
              (halfCntFalse u0 (clsA f g), halfCntFalse u0 (clsB f g), halfCntFalse u0 (clsC f g)) := by
            rw [hqA.1, hqB.1, hqC.1, eLA, eLB, eLC, eHA, eHB, eHC]
          simpa [eq1] using hu0_ok.1
        · -- false, true => `halfCntFalse u1`
          have eq1 : (lo.1 - pRaw.1 + qRaw.1, lo.2.1 - pRaw.2.1 + qRaw.2.1, lo.2.2 - pRaw.2.2 + qRaw.2.2) =
              (halfCntFalse u1 (clsA f g), halfCntFalse u1 (clsB f g), halfCntFalse u1 (clsC f g)) := by
            rw [hqA.2, hqB.2, hqC.2, eLA, eLB, eLC, eHT_A, eHT_B, eHT_C]
          simpa [eq1] using hu1_ok.1
        · -- true, false => `halfCnt u1`
          have eq1 : (pRaw.1 + (hiT.1 - qRaw.1), pRaw.2.1 + (hiT.2.1 - qRaw.2.1), pRaw.2.2 + (hiT.2.2 - qRaw.2.2)) =
              (halfCnt u1 (clsA f g), halfCnt u1 (clsB f g), halfCnt u1 (clsC f g)) :=
            triple_ext
              (sub_add_eq hlo_hi_A hp_le.1 hq_le.1 hu1A (by rw [hqA.2, eLA, eHT_A]))
              (sub_add_eq hlo_hi_B hp_le.2.1 hq_le.2.1 hu1B (by rw [hqB.2, eLB, eHT_B]))
              (sub_add_eq hlo_hi_C hp_le.2.2 hq_le.2.2 hu1C (by rw [hqC.2, eLC, eHT_C]))
          simpa [eq1] using hu1_ok.2
        · -- true, true => `halfCnt u0`
          have eq1 : (pRaw.1 + qRaw.1, pRaw.2.1 + qRaw.2.1, pRaw.2.2 + qRaw.2.2) =
              (halfCnt u0 (clsA f g), halfCnt u0 (clsB f g), halfCnt u0 (clsC f g)) :=
            triple_ext
              (add_eq_of_sub hlo_hi_A hp_le.1 hq_le.1 hu0A (by rw [hqA.1, eLA, eHA]))
              (add_eq_of_sub hlo_hi_B hp_le.2.1 hq_le.2.1 hu0B (by rw [hqB.1, eLB, eHB]))
              (add_eq_of_sub hlo_hi_C hp_le.2.2 hq_le.2.2 hu0C (by rw [hqC.1, eLC, eHC]))
          simpa [eq1] using hu0_ok.2
      · -- `A_lo = true half`, `A_hi = false half`
        have eLA : halfCntFalse v (fun a => clsA f g (secPt 7 w true a)) = lo.1 - pRaw.1 := by
          rw [← hcLoA]; dsimp only [A_lo]; rw [hcL]
        have eLB : halfCntFalse v (fun a => clsB f g (secPt 7 w true a)) = lo.2.1 - pRaw.2.1 := by
          rw [← hcLoB]; dsimp only [B_lo]; rw [hcL]
        have eLC : halfCntFalse v (fun a => clsC f g (secPt 7 w true a)) = lo.2.2 - pRaw.2.2 := by
          rw [← hcLoC]; dsimp only [C_lo]; rw [hcL]
        have eLT_A : halfCnt v (fun a => clsA f g (secPt 7 w true a)) = pRaw.1 := by
          dsimp only [pRaw, A_lo]; rw [hcL]
        have eLT_B : halfCnt v (fun a => clsB f g (secPt 7 w true a)) = pRaw.2.1 := by
          dsimp only [pRaw, B_lo]; rw [hcL]
        have eLT_C : halfCnt v (fun a => clsC f g (secPt 7 w true a)) = pRaw.2.2 := by
          dsimp only [pRaw, C_lo]; rw [hcL]
        have eHA : halfCntFalse v (fun a => clsA f g (secPt 7 w false a)) = hiT.1 - qRaw.1 := by
          rw [← hcHiA]; dsimp only [A_hi]; rw [hcH]
        have eHB : halfCntFalse v (fun a => clsB f g (secPt 7 w false a)) = hiT.2.1 - qRaw.2.1 := by
          rw [← hcHiB]; dsimp only [B_hi]; rw [hcH]
        have eHC : halfCntFalse v (fun a => clsC f g (secPt 7 w false a)) = hiT.2.2 - qRaw.2.2 := by
          rw [← hcHiC]; dsimp only [C_hi]; rw [hcH]
        cases bP <;> cases bQ
        · -- false, false => `halfCntFalse u0`
          have eq1 : (lo.1 - pRaw.1 + (hiT.1 - qRaw.1), lo.2.1 - pRaw.2.1 + (hiT.2.1 - qRaw.2.1),
              lo.2.2 - pRaw.2.2 + (hiT.2.2 - qRaw.2.2)) =
              (halfCntFalse u0 (clsA f g), halfCntFalse u0 (clsB f g), halfCntFalse u0 (clsC f g)) := by
            rw [hqA.1, hqB.1, hqC.1, eLA, eLB, eLC, eHA, eHB, eHC]
            exact Prod.ext (Nat.add_comm _ _) (Prod.ext (Nat.add_comm _ _) (Nat.add_comm _ _))
          simpa [eq1] using hu0_ok.1
        · -- false, true => `halfCnt u1`
          have eq1 : (lo.1 - pRaw.1 + qRaw.1, lo.2.1 - pRaw.2.1 + qRaw.2.1, lo.2.2 - pRaw.2.2 + qRaw.2.2) =
              (halfCnt u1 (clsA f g), halfCnt u1 (clsB f g), halfCnt u1 (clsC f g)) :=
            triple_ext
              (sub_add_eq_comm hlo_hi_A hp_le.1 hq_le.1 hu1A (by rw [hqA.2, eHA, eLT_A]))
              (sub_add_eq_comm hlo_hi_B hp_le.2.1 hq_le.2.1 hu1B (by rw [hqB.2, eHB, eLT_B]))
              (sub_add_eq_comm hlo_hi_C hp_le.2.2 hq_le.2.2 hu1C (by rw [hqC.2, eHC, eLT_C]))
          simpa [eq1] using hu1_ok.2
        · -- true, false => `halfCntFalse u1`
          have eq1 : (pRaw.1 + (hiT.1 - qRaw.1), pRaw.2.1 + (hiT.2.1 - qRaw.2.1), pRaw.2.2 + (hiT.2.2 - qRaw.2.2)) =
              (halfCntFalse u1 (clsA f g), halfCntFalse u1 (clsB f g), halfCntFalse u1 (clsC f g)) := by
            rw [hqA.2, hqB.2, hqC.2, eHA, eHB, eHC, eLT_A, eLT_B, eLT_C]
            exact Prod.ext (Nat.add_comm _ _) (Prod.ext (Nat.add_comm _ _) (Nat.add_comm _ _))
          simpa [eq1] using hu1_ok.1
        · -- true, true => `halfCnt u0`
          have eq1 : (pRaw.1 + qRaw.1, pRaw.2.1 + qRaw.2.1, pRaw.2.2 + qRaw.2.2) =
              (halfCnt u0 (clsA f g), halfCnt u0 (clsB f g), halfCnt u0 (clsC f g)) :=
            triple_ext
              (add_eq_of_sub_comm hlo_hi_A hp_le.1 hq_le.1 hu0A (by rw [hqA.1, eHA, eLA]))
              (add_eq_of_sub_comm hlo_hi_B hp_le.2.1 hq_le.2.1 hu0B (by rw [hqB.1, eHB, eLB]))
              (add_eq_of_sub_comm hlo_hi_C hp_le.2.2 hq_le.2.2 hu0C (by rw [hqC.1, eHC, eLC]))
          simpa [eq1] using hu0_ok.2
    have hcomb : inAllowedMask allowedMask (pC.1 + qC.1, pC.2.1 + qC.2.1, pC.2.2 + qC.2.2) = true ∧
        inAllowedMask allowedMask (pC.1 + (hiT.1 - qC.1), pC.2.1 + (hiT.2.1 - qC.2.1), pC.2.2 + (hiT.2.2 - qC.2.2)) = true := by
      dsimp only [pC, qC, canonPair]
      split <;> split
      · exact ⟨hallow_pair true true, hallow_pair true false⟩
      · rw [Nat.sub_sub_self hq_le.1, Nat.sub_sub_self hq_le.2.1, Nat.sub_sub_self hq_le.2.2]
        exact ⟨hallow_pair true false, hallow_pair true true⟩
      · exact ⟨hallow_pair false true, hallow_pair false false⟩
      · rw [Nat.sub_sub_self hq_le.1, Nat.sub_sub_self hq_le.2.1, Nat.sub_sub_self hq_le.2.2]
        exact ⟨hallow_pair false false, hallow_pair false true⟩
    cases hpv : perp β0 v
    · have hr6 : r = 6 := by simp [r, hpv]
      rw [hr6] at hp_mem hq_mem ⊢
      exact checkCondRankFast_sound lo hiT allowedMask cw 6 hok6 pC qC hp_mem hq_mem hcomb.1 hcomb.2
    · have hr4 : r = 4 := by simp [r, hpv]
      rw [hr4] at hp_mem hq_mem ⊢
      exact checkCondRankFast_sound lo hiT allowedMask cw 4 hok4 pC qC hp_mem hq_mem hcomb.1 hcomb.2
  -- Now sum `nz v * F v` over `W 7`: on one hand `≤ 0`, on the other hand `= condRhs lo hiT cw > 0`!
  have hsum_le : total 7 (fun v => nz v * F v) ≤ 0 := by
    rw [← total_zero 7]
    apply total_mono 7; intro v
    if hv : v = zero 7 then subst hv; simp [nz]
    else simp only [nz, hv, if_false, Int.one_mul]; exact hF_le v hv
  have hsum_eq : total 7 (fun v => nz v * F v) = condRhs lo hiT cw := by
    have hd := cls_disj f g
    have hdisj_lo : (∀ x, (A_lo x && B_lo x) = false) ∧ (∀ x, (A_lo x && C_lo x) = false) ∧
        (∀ x, (B_lo x && C_lo x) = false) :=
      ⟨fun x => hd.1 _, fun x => hd.2.1 _, fun x => hd.2.2 _⟩
    have hdisj_hi : (∀ x, (A_hi x && B_hi x) = false) ∧ (∀ x, (A_hi x && C_hi x) = false) ∧
        (∀ x, (B_hi x && C_hi x) = false) :=
      ⟨fun x => hd.1 _, fun x => hd.2.1 _, fun x => hd.2.2 _⟩
    have hmL := moment_sums_W7 A_lo B_lo C_lo hdisj_lo.1 hdisj_lo.2.1 hdisj_lo.2.2
    have hmH := moment_sums_W7 A_hi B_hi C_hi hdisj_hi.1 hdisj_hi.2.1 hdisj_hi.2.2
    dsimp only at hmL hmH
    rw [hlo_cnts.1, hlo_cnts.2.1, hlo_cnts.2.2] at hmL
    rw [hhi_cnts.1, hhi_cnts.2.1, hhi_cnts.2.2] at hmH
    have h127 : total 7 (fun v => nz v * (1 : Int)) = 127 := by
      rw [nz_total (fun _ => (1 : Int)), total_const, Int.mul_one]; decide
    have h63 : total 7 (fun v => nz v * (if (if perp β0 v then 4 else 6) == 4 then cw.w1 else 0)) = cw.w1 * 63 := by
      have hpt (v : W 7) : nz v * (if (if perp β0 v then 4 else 6) == 4 then cw.w1 else 0) =
          cw.w1 * (nz v * bind (perp β0 v)) := by
        cases perp β0 v <;> simp [nz, Balanced242Plateau.ind] <;> ac_rfl
      have h63_eq : total 7 (fun v => nz v * bind (perp β0 v)) = 63 := hanch.2.2.2.1
      rw [funext hpt, total_scale, h63_eq]
    have hsplit (v : W 7) : nz v * F v =
        cw.w0 * (nz v * 1) +
        nz v * (if (if perp β0 v then 4 else 6) == 4 then cw.w1 else 0) +
        cw.wl0 * (nz v * ((2 * (halfCnt v A_lo : Int) - lo.1) * (2 * (halfCnt v A_lo : Int) - lo.1))) +
        cw.wl1 * (nz v * ((2 * (halfCnt v B_lo : Int) - lo.2.1) * (2 * (halfCnt v B_lo : Int) - lo.2.1))) +
        cw.wl2 * (nz v * ((2 * (halfCnt v C_lo : Int) - lo.2.2) * (2 * (halfCnt v C_lo : Int) - lo.2.2))) +
        cw.wl3 * (nz v * ((2 * (halfCnt v A_lo : Int) - lo.1) * (2 * (halfCnt v B_lo : Int) - lo.2.1))) +
        cw.wl4 * (nz v * ((2 * (halfCnt v A_lo : Int) - lo.1) * (2 * (halfCnt v C_lo : Int) - lo.2.2))) +
        cw.wl5 * (nz v * ((2 * (halfCnt v B_lo : Int) - lo.2.1) * (2 * (halfCnt v C_lo : Int) - lo.2.2))) +
        cw.wh0 * (nz v * ((2 * (halfCnt v A_hi : Int) - hiT.1) * (2 * (halfCnt v A_hi : Int) - hiT.1))) +
        cw.wh1 * (nz v * ((2 * (halfCnt v B_hi : Int) - hiT.2.1) * (2 * (halfCnt v B_hi : Int) - hiT.2.1))) +
        cw.wh2 * (nz v * ((2 * (halfCnt v C_hi : Int) - hiT.2.2) * (2 * (halfCnt v C_hi : Int) - hiT.2.2))) +
        cw.wh3 * (nz v * ((2 * (halfCnt v A_hi : Int) - hiT.1) * (2 * (halfCnt v B_hi : Int) - hiT.2.1))) +
        cw.wh4 * (nz v * ((2 * (halfCnt v A_hi : Int) - hiT.1) * (2 * (halfCnt v C_hi : Int) - hiT.2.2))) +
        cw.wh5 * (nz v * ((2 * (halfCnt v B_hi : Int) - hiT.2.1) * (2 * (halfCnt v C_hi : Int) - hiT.2.2))) := by
      dsimp only [F, scoreLo, scoreHi, scoreMoments]
      simp only [Int.mul_add, Int.mul_left_comm (nz v), Int.mul_one, Int.mul_comm (nz v) cw.w0]
      omega
    rw [funext hsplit]
    simp only [total_add, total_scale, h127, h63,
      hmL.1, hmL.2.1, hmL.2.2.1, hmL.2.2.2.1, hmL.2.2.2.2.1, hmL.2.2.2.2.2,
      hmH.1, hmH.2.1, hmH.2.2.1, hmH.2.2.2.1, hmH.2.2.2.2.1, hmH.2.2.2.2.2]
    unfold condRhs scoreTargets; dsimp only; omega
  change 0 < condRhs lo hiT cw at hrhs_pos
  omega

/-! ## Part 10: Master Profile Exclusion Verifier (`checkProfileCert` & `exclude_rank8_profile`) -/

/-- Apply one peeling layer of anchor-pair certificates using a precomputed allowed-half bitmask. -/
def checkLayerWithMask (a b c : Nat) (mask : Nat)
    (layer : List (Triple × List (Nat × Int))) : Bool :=
  layer.all fun (lo, ws) =>
    checkCondCertFast lo (a - lo.1, b - lo.2.1, c - lo.2.2) mask ws

/-- Apply one peeling layer of anchor-pair certificates to a surviving split list. -/
def checkLayer (a b c : Nat) (splits : List Triple)
    (layer : List (Triple × List (Nat × Int))) : Bool :=
  checkLayerWithMask a b c (buildAllowedMask a b c splits) layer

theorem checkLayerWithMask_append (a b c : Nat) (mask : Nat)
    (L1 L2 : List (Triple × List (Nat × Int))) :
    checkLayerWithMask a b c mask (L1 ++ L2) =
      (checkLayerWithMask a b c mask L1 && checkLayerWithMask a b c mask L2) := by
  unfold checkLayerWithMask
  exact List.all_append

def peelSplits (splits : List Triple) (layer : List (Triple × List (Nat × Int))) : List Triple :=
  let killed := layer.map Prod.fst
  splits.filter (fun p => !killed.contains p)

/-- Full computable profile verifier (arbitrary layers + final Krawtchouk Farkas certificate). -/
def checkProfileCert (excl6Mask : Nat) (eBounds : List (Nat × Nat × Nat × Nat))
    (t a b c : Nat) (layers : List (List (Triple × List (Nat × Int))))
    (finalCert : List KrawEntry) : Bool :=
  let rec go (splits : List Triple) : List (List (Triple × List (Nat × Int))) → Bool
    | [] => checkAffineCert a b c splits finalCert
    | layer :: rest => checkLayer a b c splits layer && go (peelSplits splits layer) rest
  decide (a < 64 ∧ b < 64 ∧ c < 64) && go (genSplits excl6Mask eBounds t a b c) layers

/-- Modular assembly of a 1-layer `checkProfileCert` from precomputed `splits`, `mask`,
    layer check (which can be split via `checkLayerWithMask_append`), and final affine check. -/
theorem checkProfileCert_layer1 (excl6Mask : Nat) (eBounds : List (Nat × Nat × Nat × Nat))
    (t a b c : Nat) (splits : List Triple) (mask : Nat)
    (layer : List (Triple × List (Nat × Int))) (finalCert : List KrawEntry)
    (hbnd : decide (a < 64 ∧ b < 64 ∧ c < 64) = true)
    (hsplits : genSplits excl6Mask eBounds t a b c = splits)
    (hmask : buildAllowedMask a b c splits = mask)
    (hlay : checkLayerWithMask a b c mask layer = true)
    (hfin : checkAffineCert a b c (peelSplits splits layer) finalCert = true) :
    checkProfileCert excl6Mask eBounds t a b c [layer] finalCert = true := by
  unfold checkProfileCert
  rw [hbnd, hsplits]
  simp only [Bool.true_and, checkProfileCert.go, checkLayer, hmask, hlay, hfin, Bool.and_true]

/-- Master theorem: if `checkProfileCert = true`, then NO balanced 9-variable rank-8 halves `(f, g)`
    with agreement count `t` and global class counts `(a, b, c)` can exist (assuming `SectionEnumE`). -/
theorem exclude_rank8_profile
    (excl6Mask : Nat) (eBounds : List (Nat × Nat × Nat × Nat))
    (henum : SectionEnumE excl6Mask eBounds)
    (t a b c : Nat) (layers : List (List (Triple × List (Nat × Int))))
    (finalCert : List KrawEntry)
    (hcheck : checkProfileCert excl6Mask eBounds t a b c layers finalCert = true)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = t) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = a)
    (hb : (suppList (clsB f g)).length = b)
    (hc : (suppList (clsC f g)).length = c) : False := by
  unfold checkProfileCert at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨ha64, hb64, hc64⟩, hgo⟩ := hcheck
  have hcube8 : Cube (β8 f g) := Balanced242Global.cube8 f g res
  have h8 : ∀ u, transform (Balanced242RankCond.q8 f g) u = 16 ∨
      transform (Balanced242RankCond.q8 f g) u = -16 := by
    intro u
    have hrg := rr_good (β8 f g) hcube8
    rw [hrr, Int.one_mul] at hrg
    have hgu : good (β8 f g) u = true := all_true_of_total (good (β8 f g)) hrg u
    have hsg := spec_good (β8 f g) hcube8 u
    rw [hgu, hrr] at hsg
    have hm : many 8 = 256 := by decide
    rw [hm] at hsg
    have hsq : transform (Balanced242RankCond.q8 f g) u * transform (Balanced242RankCond.q8 f g) u = 256 := by
      simpa [Balanced242RankCond.q8, Balanced242Plateau.ind] using hsg
    exact sq_cases _ 16 hsq
  have hmem0 : ∀ w : W 8, w ≠ zero 8 →
      canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ∈
        genSplits excl6Mask eBounds t a b c := by
    intro w hw
    have hleA : halfCnt w (clsA f g) ≤ a := ha ▸ halfCnt_le w (clsA f g)
    have hleB : halfCnt w (clsB f g) ≤ b := hb ▸ halfCnt_le w (clsB f g)
    have hleC : halfCnt w (clsC f g) ≤ c := hc ▸ halfCnt_le w (clsC f g)
    let budget := (3 * t - 208) / 2 - a - c
    have hcF := (section_costR6_le excl6Mask eBounds henum f g res hicap hrr w hw false budget).2
    have hcT := (section_costR6_le excl6Mask eBounds henum f g res hicap hrr w hw true budget).2
    have sA := sec_suppList_eq_halfCnt w hw (clsA f g)
    have sB := sec_suppList_eq_halfCnt w hw (clsB f g)
    have sC := sec_suppList_eq_halfCnt w hw (clsC f g)
    have fA : halfCntFalse w (clsA f g) = a - halfCnt w (clsA f g) := by
      have := halfCnt_add_false w (clsA f g); omega
    have fB : halfCntFalse w (clsB f g) = b - halfCnt w (clsB f g) := by
      have := halfCnt_add_false w (clsB f g); omega
    have fC : halfCntFalse w (clsC f g) = c - halfCnt w (clsC f g) := by
      have := halfCnt_add_false w (clsC f g); omega
    rw [sA.1, sB.1, sC.1, fA, fB, fC] at hcF
    rw [sA.2, sB.2, sC.2] at hcT
    have hsum_exc := rank8_secExc_sum f g res h8 w hw
    have hnp := rank8_Nplus_formula f g res hicap h8
    have hpa : Balanced242Reduction.cnt (clsA f g) = (a : Int) := by
      unfold Balanced242Reduction.cnt; rw [← ha, suppList_length_eq_total]; rfl
    have hpc : Balanced242Reduction.cnt (clsC f g) = (c : Int) := by
      unfold Balanced242Reduction.cnt; rw [← hc, suppList_length_eq_total]; rfl
    rw [ht, hpa, hpc] at hnp
    have hcost_le : costR6 excl6Mask eBounds budget (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) +
        costR6 excl6Mask eBounds budget (a - halfCnt w (clsA f g)) (b - halfCnt w (clsB f g)) (c - halfCnt w (clsC f g)) ≤
        budget := by
      dsimp only [budget] at hcF hcT ⊢; omega
    exact mem_genSplits hleA hleB hleC hcost_le
  -- Induction on peeling layers!
  have hpeel : ∀ (Ls : List (List (Triple × List (Nat × Int)))) (splits : List Triple),
      (∀ w : W 8, w ≠ zero 8 →
        canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ∈ splits) →
      checkProfileCert.go a b c finalCert splits Ls = true → False := by
    intro Ls
    induction Ls with
    | nil =>
      intro splits hmem hok
      exact affine_cert_refute f g a b c ha hb hc splits hmem finalCert hok
    | cons layer rest ih =>
      intro splits hmem hok
      unfold checkProfileCert.go at hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨hlay, hrest⟩ := hok
      apply ih (peelSplits splits layer) _ hrest
      intro w hw
      have hmw := hmem w hw
      unfold peelSplits
      rw [List.mem_filter]
      refine ⟨hmw, ?_⟩
      cases hct : (layer.map Prod.fst).contains
          (canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)))
      · rfl
      · exfalso
        have hmem_k : canonPair a b c (halfCnt w (clsA f g)) (halfCnt w (clsB f g)) (halfCnt w (clsC f g)) ∈
            layer.map Prod.fst := by
          rw [List.contains_iff_mem] at hct; exact hct
        rw [List.mem_map] at hmem_k
        rcases hmem_k with ⟨⟨lo, ws⟩, hpair_mem, hlo_eq⟩
        dsimp only at hlo_eq
        unfold checkLayer checkLayerWithMask at hlay
        rw [List.all_eq_true] at hlay
        have hws_ok := hlay (lo, ws) hpair_mem
        have hallow : ∀ u : W 8, u ≠ zero 8 →
            inAllowedMask (buildAllowedMask a b c splits) (halfCntFalse u (clsA f g), halfCntFalse u (clsB f g), halfCntFalse u (clsC f g)) = true ∧
            inAllowedMask (buildAllowedMask a b c splits) (halfCnt u (clsA f g), halfCnt u (clsB f g), halfCnt u (clsC f g)) = true := by
          intro u hu
          have hmu := hmem u hu
          have hbits := testBit_buildAllowedMask_of_mem a b c splits _ hmu
          have huA : halfCnt u (clsA f g) ≤ a := ha ▸ halfCnt_le u (clsA f g)
          have huB : halfCnt u (clsB f g) ≤ b := hb ▸ halfCnt_le u (clsB f g)
          have huC : halfCnt u (clsC f g) ≤ c := hc ▸ halfCnt_le u (clsC f g)
          have hfA : halfCntFalse u (clsA f g) = a - halfCnt u (clsA f g) := by
            have := halfCnt_add_false u (clsA f g); omega
          have hfB : halfCntFalse u (clsB f g) = b - halfCnt u (clsB f g) := by
            have := halfCnt_add_false u (clsB f g); omega
          have hfC : halfCntFalse u (clsC f g) = c - halfCnt u (clsC f g) := by
            have := halfCnt_add_false u (clsC f g); omega
          have hltF : halfCntFalse u (clsA f g) < 64 ∧ halfCntFalse u (clsB f g) < 64 ∧ halfCntFalse u (clsC f g) < 64 := by omega
          have hltT : halfCnt u (clsA f g) < 64 ∧ halfCnt u (clsB f g) < 64 ∧ halfCnt u (clsC f g) < 64 := by omega
          unfold canonPair at hbits
          cases hfl : tripleLe (halfCnt u (clsA f g), halfCnt u (clsB f g), halfCnt u (clsC f g))
              (a - halfCnt u (clsA f g), b - halfCnt u (clsB f g), c - halfCnt u (clsC f g))
          · simp only [hfl, Bool.false_eq_true, if_false,
              Nat.sub_sub_self huA, Nat.sub_sub_self huB, Nat.sub_sub_self huC] at hbits
            rw [← hfA, ← hfB, ← hfC] at hbits
            exact ⟨by unfold inAllowedMask; simp [hltF.1, hltF.2.1, hltF.2.2, hbits.1],
                   by unfold inAllowedMask; simp [hltT.1, hltT.2.1, hltT.2.2, hbits.2]⟩
          · simp only [hfl, if_true] at hbits
            rw [← hfA, ← hfB, ← hfC] at hbits
            exact ⟨by unfold inAllowedMask; simp [hltF.1, hltF.2.1, hltF.2.2, hbits.2],
                   by unfold inAllowedMask; simp [hltT.1, hltT.2.1, hltT.2.2, hbits.1]⟩
        exact cond_cert_refute f g res hicap hrr a b c ha hb hc (buildAllowedMask a b c splits)
          hallow w hw lo hlo_eq.symm ws hws_ok
  exact hpeel layers (genSplits excl6Mask eBounds t a b c) hmem0 hgo

end Balanced242Farkas

#print axioms Balanced242Farkas.eminClosed_le_secExc
#print axioms Balanced242Farkas.quarter_hyperplane_counts
#print axioms Balanced242Farkas.farkas_refute
#print axioms Balanced242Farkas.section_costR6_le
#print axioms Balanced242Farkas.sixOK_of_subsection
#print axioms Balanced242Farkas.affine_cert_refute
#print axioms Balanced242Farkas.cond_cert_refute
#print axioms Balanced242Farkas.exclude_rank8_profile
