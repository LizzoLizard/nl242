/-
  Exact 7-variable section bounds for `t ≥ 94`:

    1. `section_energy`: `4 * ∑ D² = 784 - M`, where `M = 6x + 3y + 5z`.
    2. `section_cs_ok`: for any section of plateau height `m ∈ {16, 32, 64, 128}`
       (rank `s ∈ {6, 4, 2, 0}`, `scale = m/2`, `Rsz = 16384/m² = 2^s`),
       `scale ∣ T7` and `4 * (|τ| + 2 * max(0, |τ| - Rsz)) ≤ 784 - M` (`τ = T7 / scale`).
       This formalizes `mid2.cs_ok`.
    3. `rank6_exc_buckets`: for any rank-6 section (`m = 16`), the six pointwise
       multiplicity buckets `(p1, p2, n1, n2, m1, m2)` satisfy
         * `p1 + p2 + n1 + n2 ≤ 64`, `m1 + m2 ≤ 64`,
         * `p1 + 2p2 - n1 - 2n2 = -112 + M/2 - 2(x + z)`,
         * `4 * (p1 + 4p2 + n1 + 4n2 + m1 + 4m2) = 784 - M`,
         * `secExc D (transform q) = p1 + 2p2 + m2`.
       Consequently both `rank8filter.emin` (minimizing `p1 + p2 + m2`) and the
       tighter `secExc` arithmetic minimum (minimizing `p1 + 2p2 + m2`) are valid
       lower bounds on `secExc D (transform q)`.
-/
import Balanced242Rank8

namespace Balanced242SectionBounds
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Plateau
open Balanced242Rank8 (excPt secExc)

local notation "phase" => Balanced242Section0320.phase

private theorem H_vals (h : Int) (ho : h % 2 = 1) (hc : h.natAbs ≤ 7) :
    h = -7 ∨ h = -5 ∨ h = -3 ∨ h = -1 ∨ h = 1 ∨ h = 3 ∨ h = 5 ∨ h = 7 := by
  omega

private theorem sq_point7 (h : Int) (ho : h % 2 = 1) (hc : h.natAbs ≤ 7) :
    h * h = 49 - 8 * (6 * (if h.natAbs = 1 then (1 : Int) else 0) +
                      3 * (if h.natAbs = 5 then (1 : Int) else 0) +
                      5 * (if h.natAbs = 3 then (1 : Int) else 0)) := by
  rcases H_vals h ho hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem t7_point7 (h : Int) (ho : h % 2 = 1) (hc : h.natAbs ≤ 7) :
    phase h * h = -7 + 8 * (if h.natAbs = 1 then (1 : Int) else 0) +
                      12 * (if h.natAbs = 5 then (1 : Int) else 0) +
                       4 * (if h.natAbs = 3 then (1 : Int) else 0) := by
  rcases H_vals h ho hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Exact section energy identity: `4 * ∑ D² = 784 - (6x + 3y + 5z)`. -/
theorem section_energy (D H : W 7 → Int) (hspec : ∀ a, transform D a = 2 * H a)
    (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7) :
    let x := total 7 (fun a => if (H a).natAbs = 1 then (1 : Int) else 0)
    let y := total 7 (fun a => if (H a).natAbs = 5 then (1 : Int) else 0)
    let z := total 7 (fun a => if (H a).natAbs = 3 then (1 : Int) else 0)
    4 * total 7 (fun u => D u * D u) = 784 - (6 * x + 3 * y + 5 * z) := by
  intro x y z
  have hpar := Balanced242Section0320.parseval D
  have hlhs : total 7 (fun a => transform D a * transform D a) = 4 * total 7 (fun a => H a * H a) := by
    rw [← total_scale]
    apply congrArg (total 7); funext a
    rw [hspec a, Int.mul_assoc 2 (H a), Int.mul_left_comm (H a) 2 (H a), ← Int.mul_assoc 2 2]
    rfl
  have hsq : total 7 (fun a => H a * H a) = 128 * 49 - 8 * (6 * x + 3 * y + 5 * z) := by
    have pt (a : W 7) := sq_point7 (H a) (hH a).1 (hH a).2
    rw [funext pt, total_sub, total_const, total_scale, total_add, total_add,
        total_scale, total_scale, total_scale]
    change (128 : Int) * 49 - 8 * (6 * x + 3 * y + 5 * z) = _
    rfl
  have hm128 : many 7 = 128 := by decide
  rw [hlhs, hsq, hm128] at hpar
  omega

/-- Exact section `T7` identity: `∑ phase(H) * H = -896 + 8x + 12y + 4z`. -/
theorem section_t7_sum (H : W 7 → Int) (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7) :
    let x := total 7 (fun a => if (H a).natAbs = 1 then (1 : Int) else 0)
    let y := total 7 (fun a => if (H a).natAbs = 5 then (1 : Int) else 0)
    let z := total 7 (fun a => if (H a).natAbs = 3 then (1 : Int) else 0)
    total 7 (fun a => phase (H a) * H a) = -896 + 8 * x + 12 * y + 4 * z := by
  intro x y z
  have pt (a : W 7) := t7_point7 (H a) (hH a).1 (hH a).2
  rw [funext pt, total_add, total_add, total_add, total_const,
      total_scale, total_scale, total_scale]
  change (128 : Int) * (-7) + 8 * x + 12 * y + 4 * z = _
  omega

private theorem cs_pt (d s : Int) (hd : -2 ≤ d ∧ d ≤ 2) (hs : s = -1 ∨ s = 0 ∨ s = 1) :
    d * s ≤ d * d ∧ -1 * (d * s) ≤ d * d ∧
    3 * (d * s) - 2 * (if s = 0 then (0 : Int) else 1) ≤ d * d ∧
    -3 * (d * s) - 2 * (if s = 0 then (0 : Int) else 1) ≤ d * d := by
  have hd' : d = -2 ∨ d = -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hd' with rfl | rfl | rfl | rfl | rfl <;>
  rcases hs with rfl | rfl | rfl <;> decide

/-- General Cauchy–Schwarz refinement on the dual flat `R` (`mid2.cs_ok`). -/
theorem section_cs_ok (D H : W 7 → Int) (hD : ∀ u, -2 ≤ D u ∧ D u ≤ 2)
    (hspec : ∀ a, transform D a = 2 * H a) (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7)
    (m : Int) (hm : m = 16 ∨ m = 32 ∨ m = 64 ∨ m = 128)
    (hplat : ∀ u, transform (fun a => phase (H a)) u = 0 ∨
      transform (fun a => phase (H a)) u = m ∨ transform (fun a => phase (H a)) u = -m) :
    let x := total 7 (fun a => if (H a).natAbs = 1 then (1 : Int) else 0)
    let y := total 7 (fun a => if (H a).natAbs = 5 then (1 : Int) else 0)
    let z := total 7 (fun a => if (H a).natAbs = 3 then (1 : Int) else 0)
    let M := 6 * x + 3 * y + 5 * z
    let T7 := -896 + 8 * x + 12 * y + 4 * z
    let scale := m / 2
    let Rsz := 16384 / (m * m)
    T7 % scale = 0 ∧
    let tau : Int := (T7 / scale).natAbs
    4 * tau ≤ 784 - M ∧ 4 * (tau + 2 * (tau - Rsz)) ≤ 784 - M := by
  intro x y z M T7 scale Rsz
  let q : W 7 → Int := fun a => phase (H a)
  let σ : W 7 → Int := fun u => transform q u / m
  have hσ (u : W 7) : σ u = -1 ∨ σ u = 0 ∨ σ u = 1 := by
    dsimp only [σ]
    rcases hm with rfl | rfl | rfl | rfl <;> rcases hplat u with h | h | h <;> rw [h] <;> decide
  have hmσ (u : W 7) : transform q u = m * σ u := by
    dsimp only [σ]
    rcases hm with rfl | rfl | rfl | rfl <;> rcases hplat u with h | h | h <;> rw [h] <;> decide
  have hdual : m * total 7 (fun u => D u * σ u) = 2 * T7 := by
    have hd := Balanced242Section0320.duality D q
    have hlhs : total 7 (fun u => D u * transform q u) = m * total 7 (fun u => D u * σ u) := by
      rw [← total_scale]; apply congrArg (total 7); funext u
      rw [hmσ u, Int.mul_left_comm]
    have hrhs : total 7 (fun a => q a * transform D a) = 2 * T7 := by
      have ht7 := section_t7_sum H hH
      change total 7 (fun a => q a * H a) = T7 at ht7
      rw [← ht7, ← total_scale]
      apply congrArg (total 7); funext a
      rw [hspec a, Int.mul_left_comm]
    rw [← hlhs, ← hrhs]; exact hd.symm
  have hsc : scale * total 7 (fun u => D u * σ u) = T7 := by
    dsimp only [scale]; rcases hm with rfl | rfl | rfl | rfl <;> omega
  have hdiv : T7 % scale = 0 := by
    rw [← hsc, Int.mul_emod_right]
  have htau_val : total 7 (fun u => D u * σ u) = T7 / scale := by
    have hpos : scale ≠ 0 := by dsimp only [scale]; rcases hm with rfl | rfl | rfl | rfl <;> decide
    rw [← hsc, Int.mul_ediv_cancel_left _ hpos]
  have hRsz : total 7 (fun u => if σ u = 0 then (0 : Int) else 1) = Rsz := by
    have hpar := Balanced242Section0320.parseval q
    have hq1 (a : W 7) : q a * q a = 1 := by
      dsimp only [q]; unfold Balanced242Section0320.phase
      split <;> decide
    have hqsq (u : W 7) : transform q u * transform q u = (m * m) * (if σ u = 0 then (0 : Int) else 1) := by
      rw [hmσ u]
      rcases hσ u with h | h | h <;> rw [h] <;> simp
    rw [funext hqsq, total_scale, funext hq1, total_const] at hpar
    have hm128 : many 7 = 128 := by decide
    rw [hm128] at hpar
    dsimp only [Rsz]
    rcases hm with rfl | rfl | rfl | rfl <;> omega
  have hene := section_energy D H hspec hH
  have h1 := total_mono 7 _ _ (fun u => (cs_pt (D u) (σ u) (hD u) (hσ u)).1)
  have h2 := total_mono 7 _ _ (fun u => (cs_pt (D u) (σ u) (hD u) (hσ u)).2.1)
  have h3 := total_mono 7 _ _ (fun u => (cs_pt (D u) (σ u) (hD u) (hσ u)).2.2.1)
  have h4 := total_mono 7 _ _ (fun u => (cs_pt (D u) (σ u) (hD u) (hσ u)).2.2.2)
  rw [total_scale] at h2
  rw [total_sub, total_scale, total_scale, hRsz] at h3 h4
  rw [htau_val] at h1 h2 h3 h4
  dsimp only at hene
  refine ⟨hdiv, ?_, ?_⟩ <;> omega

private def bP1 (d qh : Int) : Int := if qh ≠ 0 ∧ d * (qh / 16) = 1 then 1 else 0
private def bP2 (d qh : Int) : Int := if qh ≠ 0 ∧ d * (qh / 16) = 2 then 1 else 0
private def bN1 (d qh : Int) : Int := if qh ≠ 0 ∧ d * (qh / 16) = -1 then 1 else 0
private def bN2 (d qh : Int) : Int := if qh ≠ 0 ∧ d * (qh / 16) = -2 then 1 else 0
private def bM1 (d qh : Int) : Int := if qh = 0 ∧ (d = 1 ∨ d = -1) then 1 else 0
private def bM2 (d qh : Int) : Int := if qh = 0 ∧ (d = 2 ∨ d = -2) then 1 else 0

private theorem b_nonneg (F : W 7 → Int) (h : ∀ u, 0 ≤ F u) : 0 ≤ total 7 F := by
  rw [← total_zero 7]; exact total_mono 7 _ _ h

private theorem bucket_pt (d qh : Int) (hd : -2 ≤ d ∧ d ≤ 2)
    (hq : qh = 0 ∨ qh = 16 ∨ qh = -16) :
    bP1 d qh + bP2 d qh + bN1 d qh + bN2 d qh ≤ (if qh = 0 then (0 : Int) else 1) ∧
    bM1 d qh + bM2 d qh ≤ (if qh = 0 then (1 : Int) else 0) ∧
    bP1 d qh + 2 * bP2 d qh - bN1 d qh - 2 * bN2 d qh = d * (qh / 16) ∧
    bP1 d qh + 4 * bP2 d qh + bN1 d qh + 4 * bN2 d qh + bM1 d qh + 4 * bM2 d qh = d * d ∧
    bP1 d qh + 2 * bP2 d qh + bM2 d qh = excPt d qh := by
  have hd' : d = -2 ∨ d = -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hd' with rfl | rfl | rfl | rfl | rfl <;>
  rcases hq with rfl | rfl | rfl <;> decide

/-- Exact rank-6 exception-weight bucket decomposition (backing `rank8filter.emin` and `sel_e`). -/
theorem rank6_exc_buckets (D H : W 7 → Int) (hD : ∀ u, -2 ≤ D u ∧ D u ≤ 2)
    (hspec : ∀ a, transform D a = 2 * H a) (hH : ∀ a, H a % 2 = 1 ∧ (H a).natAbs ≤ 7)
    (h6 : ∀ u, transform (fun a => phase (H a)) u = 0 ∨
      transform (fun a => phase (H a)) u = 16 ∨ transform (fun a => phase (H a)) u = -16) :
    let x := total 7 (fun a => if (H a).natAbs = 1 then (1 : Int) else 0)
    let y := total 7 (fun a => if (H a).natAbs = 5 then (1 : Int) else 0)
    let z := total 7 (fun a => if (H a).natAbs = 3 then (1 : Int) else 0)
    let M := 6 * x + 3 * y + 5 * z
    ∃ p1 p2 n1 n2 m1 m2 : Nat,
      p1 + p2 + n1 + n2 ≤ 64 ∧
      m1 + m2 ≤ 64 ∧
      2 * ((p1 : Int) + 2 * p2 - n1 - 2 * n2) = -224 + M - 4 * (x + z) ∧
      4 * ((p1 : Int) + 4 * p2 + n1 + 4 * n2 + m1 + 4 * m2) = 784 - M ∧
      secExc D (transform (fun a => phase (H a))) = (p1 : Int) + 2 * p2 + m2 := by
  intro x y z M
  let q : W 7 → Int := fun a => phase (H a)
  let qh : W 7 → Int := transform q
  let cP1 := total 7 (fun u => bP1 (D u) (qh u))
  let cP2 := total 7 (fun u => bP2 (D u) (qh u))
  let cN1 := total 7 (fun u => bN1 (D u) (qh u))
  let cN2 := total 7 (fun u => bN2 (D u) (qh u))
  let cM1 := total 7 (fun u => bM1 (D u) (qh u))
  let cM2 := total 7 (fun u => bM2 (D u) (qh u))
  have hnn1 : 0 ≤ cP1 := b_nonneg _ (fun u => by unfold bP1; split <;> decide)
  have hnn2 : 0 ≤ cP2 := b_nonneg _ (fun u => by unfold bP2; split <;> decide)
  have hnn3 : 0 ≤ cN1 := b_nonneg _ (fun u => by unfold bN1; split <;> decide)
  have hnn4 : 0 ≤ cN2 := b_nonneg _ (fun u => by unfold bN2; split <;> decide)
  have hnn5 : 0 ≤ cM1 := b_nonneg _ (fun u => by unfold bM1; split <;> decide)
  have hnn6 : 0 ≤ cM2 := b_nonneg _ (fun u => by unfold bM2; split <;> decide)
  have hR : total 7 (fun u => if qh u = 0 then (0 : Int) else 1) = 64 := by
    have hpar := Balanced242Section0320.parseval q
    have hq1 (a : W 7) : q a * q a = 1 := by
      dsimp only [q]; unfold Balanced242Section0320.phase; split <;> decide
    have hqsq (u : W 7) : qh u * qh u = 256 * (if qh u = 0 then (0 : Int) else 1) := by
      dsimp only [qh]; rcases h6 u with h | h | h <;> rw [h] <;> decide
    change total 7 (fun u => qh u * qh u) = many 7 * total 7 (fun a => q a * q a) at hpar
    rw [funext hqsq, total_scale, funext hq1, total_const] at hpar
    have hm128 : many 7 = 128 := by decide
    rw [hm128] at hpar; omega
  have hRc : total 7 (fun u => if qh u = 0 then (1 : Int) else 0) = 64 := by
    have hsum : total 7 (fun u => (if qh u = 0 then (1 : Int) else 0) + (if qh u = 0 then 0 else 1)) = 128 := by
      have pt (u : W 7) : (if qh u = 0 then (1 : Int) else 0) + (if qh u = 0 then 0 else 1) = 1 := by
        split <;> decide
      rw [funext pt, total_const]; decide
    rw [total_add, hR] at hsum; omega
  have hdual : 8 * total 7 (fun u => D u * (qh u / 16)) = -896 + 8 * x + 12 * y + 4 * z := by
    have hd := Balanced242Section0320.duality D q
    have hlhs : total 7 (fun u => D u * qh u) = 16 * total 7 (fun u => D u * (qh u / 16)) := by
      rw [← total_scale]; apply congrArg (total 7); funext u
      have hmσ : D u * qh u = 16 * (D u * (qh u / 16)) := by
        dsimp only [qh]; rcases h6 u with h | h | h <;> rw [h] <;> omega
      exact hmσ
    have hrhs : total 7 (fun a => q a * transform D a) = 2 * (-896 + 8 * x + 12 * y + 4 * z) := by
      have ht7 := section_t7_sum H hH
      change total 7 (fun a => q a * H a) = -896 + 8 * x + 12 * y + 4 * z at ht7
      rw [← ht7, ← total_scale]
      apply congrArg (total 7); funext a
      rw [hspec a, Int.mul_left_comm]
    change total 7 (fun a => q a * transform D a) = total 7 (fun u => D u * qh u) at hd
    rw [hlhs, hrhs] at hd; omega
  have hene := section_energy D H hspec hH
  dsimp only at hene
  have hpt (u : W 7) := bucket_pt (D u) (qh u) (hD u) (h6 u)
  have hleR : cP1 + cP2 + cN1 + cN2 ≤ 64 := by
    rw [← hR]
    have hm := total_mono 7 _ _ (fun u => (hpt u).1)
    rw [total_add, total_add, total_add] at hm; exact hm
  have hleRc : cM1 + cM2 ≤ 64 := by
    rw [← hRc]
    have hm := total_mono 7 _ _ (fun u => (hpt u).2.1)
    rw [total_add] at hm; exact hm
  have htau : cP1 + 2 * cP2 - cN1 - 2 * cN2 = total 7 (fun u => D u * (qh u / 16)) := by
    have he := congrArg (total 7) (funext fun u => (hpt u).2.2.1)
    rw [total_sub, total_sub, total_add, total_scale, total_scale] at he; exact he
  have hsq : cP1 + 4 * cP2 + cN1 + 4 * cN2 + cM1 + 4 * cM2 = total 7 (fun u => D u * D u) := by
    have he := congrArg (total 7) (funext fun u => (hpt u).2.2.2.1)
    rw [total_add, total_add, total_add, total_add, total_add, total_scale, total_scale, total_scale] at he
    exact he
  have hexc : cP1 + 2 * cP2 + cM2 = secExc D qh := by
    have he := congrArg (total 7) (funext fun u => (hpt u).2.2.2.2)
    rw [total_add, total_add, total_scale] at he; exact he
  have hMdef : 4 * M - 16 * (x + z) = 8 * x + 12 * y + 4 * z := by dsimp only [M]; omega
  refine ⟨cP1.toNat, cP2.toNat, cN1.toNat, cN2.toNat, cM1.toNat, cM2.toNat, ?_, ?_, ?_, ?_, ?_⟩
  · have := hnn1; have := hnn2; have := hnn3; have := hnn4
    generalize cP1 = a1 at *; generalize cP2 = a2 at *; generalize cN1 = a3 at *; generalize cN2 = a4 at *
    omega
  · have := hnn5; have := hnn6
    generalize cM1 = a5 at *; generalize cM2 = a6 at *
    omega
  · have h1 : (cP1.toNat : Int) = cP1 := by omega
    have h2 : (cP2.toNat : Int) = cP2 := by omega
    have h3 : (cN1.toNat : Int) = cN1 := by omega
    have h4 : (cN2.toNat : Int) = cN2 := by omega
    rw [h1, h2, h3, h4, htau]
    omega
  · have h1 : (cP1.toNat : Int) = cP1 := by omega
    have h2 : (cP2.toNat : Int) = cP2 := by omega
    have h3 : (cN1.toNat : Int) = cN1 := by omega
    have h4 : (cN2.toNat : Int) = cN2 := by omega
    have h5 : (cM1.toNat : Int) = cM1 := by omega
    have h6' : (cM2.toNat : Int) = cM2 := by omega
    rw [h1, h2, h3, h4, h5, h6', hsq]
    exact hene
  · have h1 : (cP1.toNat : Int) = cP1 := by omega
    have h2 : (cP2.toNat : Int) = cP2 := by omega
    have h6' : (cM2.toNat : Int) = cM2 := by omega
    rw [h1, h2, h6']
    exact hexc.symm

end Balanced242SectionBounds

#print axioms Balanced242SectionBounds.section_energy
#print axioms Balanced242SectionBounds.section_t7_sum
#print axioms Balanced242SectionBounds.section_cs_ok
#print axioms Balanced242SectionBounds.rank6_exc_buckets
