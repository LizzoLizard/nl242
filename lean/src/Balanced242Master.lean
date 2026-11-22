/-
  Balanced242Master.lean — Top-level coordinate-free master theorem proving that NO balanced
  9-variable Boolean function `F : W 9 → Bool` has nonlinearity 242 (`∀ a, |W_F(a)| ≤ 28`).

  Zero Mathlib, zero `sorry`, zero `native_decide`, zero custom axioms.

  This module unites the entire zero-Mathlib Lean 4 formalization across ALL even agreement
  counts `t ∈ [0, 256]`:
    * Coordinate-free reduction (`Balanced242No244`, `Balanced242Coord`):
      `∀ a, |W_F(a)| ≤ 28` automatically forces `supportXor F ≠ 0` and adapts `(F)` to halves
      `(f, g)` with `lo(0) = 0`, `8 ∣ lo`, `|lo| ≤ 24`, `hi ≡ 4 (mod 8)`, `|hi| ≤ 28`.
    * `t ≤ 84` & `t ∈ {86, 88, 90, 92}`: closed in Lean (`Balanced242LowRange`, `Balanced242Complete`)
      modulo `SectionEnum`.
    * `t = 94`: all 17 rank-8 frontier profiles closed in Lean (`Balanced242T94`) modulo
      `SectionEnumE excl6MaskT94 eBoundsT94`; non-frontier cases in `ComputationalClosures`.
    * `t = 96`: `Zc ∈ {64, 160, 192, 256}` closed unconditionally (`Balanced242LowBlock`,
      `Balanced242Z64Switch`); `(0, 51, 27)` & `(21, 34, 12)` closed in Lean (`Balanced242T96_0_51_27`,
      `Balanced242T94`); remaining rank-6 & rank-8 profiles in `ComputationalClosures`
      (`nl242_t96_closure.zip`). (Plus `Balanced242T96Centered`, `Balanced242T96Arith`,
      `Balanced242T96Quartic`.)
    * `t = 98`: `Zc ∈ {64, 160, 192, 256}` closed unconditionally (`Balanced242LowBlock`,
      `Balanced242Z64Switch`); `Balanced242T98R6Z144` excludes the rank-6, `|Z| = 144` normal form.
      The master uses `ComputationalClosures.t98_remaining` for all six remaining `Zc` values (`nl242_t98_closure.zip`).
    * `t = 100, 102`: `Zc ∈ {64, 144, 160, 192, 256}` (and `Zc = 136` at `t = 102`) closed
      unconditionally in Lean (`Balanced242LowBlock`, `Balanced242Z64Switch`); remaining cases in
      `ComputationalClosures` (`nl242_top_closure.zip`).
    * `t = 104, 106`: ranks `0, 2, 8` ALL closed unconditionally in Lean (`Balanced242T104R8`,
      `Balanced242LowBlock`, `Balanced242Z64Switch`), plus `r = 4, Zc ∈ {128, 160}` and
      `r = 6, Zc ∈ {128, 144}`; only `(r = 4, Zc = 96)` and `(r = 6, Zc = 112)` in
      `ComputationalClosures` (`nl242_middle_closure.zip`, `nl242_top_closure.zip`).
    * `t = 108`: ranks `0, 2, 6, 8` ALL closed unconditionally in Lean (`Balanced242T108R6`,
      `Balanced242T104R8`, `Balanced242LowBlock`, `Balanced242Z64Switch`); only `(r = 4, Zc = 96)`
      in `ComputationalClosures` (`nl242_middle_closure.zip`).
    * `t = 110`: ranks `0, 2, 6, 8` ALL closed unconditionally in Lean (`Balanced242T104R8`,
      `Balanced242LowBlock`, `Balanced242Z64Switch`); only `(r = 4, Zc = 96)` (with `n0 ≥ 8`
      proved in `Balanced242T112.rank4_Z96_n0_ge8`) in `ComputationalClosures` (`nl242_top_closure.zip`).
    * `t = 112`: **100% UNCONDITIONALLY CLOSED IN LEAN 4** (`Balanced242T112.no_t112`)!
    * `t = 114`: **100% UNCONDITIONALLY CLOSED IN LEAN 4** (`Balanced242T114.no_t114`)!
    * `t = 116`: `k = 12` **100% UNCONDITIONALLY CLOSED IN LEAN 4** (`Balanced242T114.t116_forces_k16`);
      `k = 16` closed cleanly under EITHER `EndpointK16Direct` (`nl242_endpoint_closure.zip` /
      `nl242_endpoint_crosscheck.zip`) OR `CoveringRadius244` (`nl244_verify.zip`).
    * `t = 118`: **100% UNCONDITIONALLY CLOSED IN LEAN 4** (`Balanced242T118.no_t118`)!
    * `t ≥ 120`: **100% UNCONDITIONALLY CLOSED IN LEAN 4** (`Balanced242Endpoint.low_agreements_below_120`)!

  Main exported theorems:
    * `endpointK16_of_coveringRadius`: `CoveringRadius244 → EndpointK16Direct`.
    * `no_balanced_9var_nl242_direct`: coordinate-free master theorem using `EndpointK16Direct`
      (zero `CoveringRadius244`!).
    * `no_balanced_9var_nl242`: coordinate-free master theorem using `CoveringRadius244`.
-/
import Balanced242LowRange
import Balanced242T94
import Balanced242T96Centered
import Balanced242T96_0_51_27
import Balanced242T96Arith
import Balanced242T96Quartic
import Balanced242T98R6Z144
import Balanced242T108R6
import Balanced242T104R8
import Balanced242T112
import Balanced242T114
import Balanced242T118

namespace Balanced242Master

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Blocks Balanced242Support Balanced242Hyperplane
open Balanced242Reduction Balanced242Plateau Balanced242Rank Balanced242Global
open Balanced242RankCond Balanced242Coord Balanced242No244 Balanced242LowRange
open Balanced242Krawtchouk (suppList)
open Balanced242Farkas (SectionEnumE suppList_length_eq_total)
open Balanced242T94Data (excl6MaskT94 eBoundsT94)
open Balanced242T96Data (excl6MaskT96)
open Balanced242T94 (t94FrontierProfiles t94_all_17_frontier_excluded t96_21_34_12_excluded)
open Balanced242T96_0_51_27 (excl_96_0_51_27)
open Balanced242LowBlock
open Balanced242Z64Switch
open Balanced242T108R6
open Balanced242T104R8
open Balanced242T112
open Balanced242T114
open Balanced242T118
open Balanced242HighSections (complementary)

/-- Adapted balanced-242 halves predicate shared across the trust-boundary interfaces. -/
def Adapted242 (f g : Half) : Prop :=
  (∀ a, hi f g a % 8 = 4) ∧
  (∀ a, (hi f g a).natAbs ≤ 28) ∧
  lo f g (zero 8) = 0 ∧
  (∀ a, lo f g a % 8 = 0) ∧
  (∀ a, (lo f g a).natAbs ≤ 24) ∧
  agreements f g % 2 = 0

/-- Direct exclusion of the sole surviving `t = 116, k = 16` switched complementary ternary pair
    (verified independently by `nl242_endpoint_closure.zip` and `nl242_endpoint_crosscheck.zip`). -/
def EndpointK16Direct : Prop :=
  ¬ ∃ (u v : W 8 → Int),
      (∀ x, complementary (v x) (u x)) ∧
      (∀ a, (transform v a).natAbs = 4 ∨ (transform v a).natAbs = 12) ∧
      (∀ a, (transform u a).natAbs = 4 ∨ (transform u a).natAbs = 12) ∧
      total 8 (fun a => if (transform u a).natAbs = 4 then (1 : Int) else 0) = 16

/-- The unrestricted covering-radius bound `CoveringRadius244` (`nl244_verify.zip`) directly
    implies `EndpointK16Direct`: any complementary pair `(u, v)` with `|Ŵ_v|, |Ŵ_u| ≤ 12` yields
    a 9-variable Boolean function `(f', g')` with `|lo|, |hi| ≤ 24`. -/
theorem endpointK16_of_coveringRadius (hcov : CoveringRadius244) : EndpointK16Direct := by
  intro ⟨u, v, hcomp, hv, hu, _⟩
  apply hcov
  let f' : Half := fun x => decide (v x + u x < 0)
  let g' : Half := fun x => decide (v x - u x < 0)
  have hsum (x : W 8) : sign (f' x) + sign (g' x) = 2 * v x := by
    have h := hcomp x
    rcases h with ⟨h1, h2 | h2⟩ | ⟨h2, h1 | h1⟩ <;>
      simp [f', g', h1, h2, sign]
  have hdiff (x : W 8) : sign (f' x) - sign (g' x) = 2 * u x := by
    have h := hcomp x
    rcases h with ⟨h1, h2 | h2⟩ | ⟨h2, h1 | h1⟩ <;>
      simp [f', g', h1, h2, sign]
  refine ⟨f', g', fun a => ?_⟩
  have hlo : lo f' g' a = 2 * transform v a := by
    unfold lo spec transform
    rw [← total_add, ← total_scale]
    apply congrArg (total 8); funext x
    rw [← Int.add_mul, hsum x, Int.mul_assoc]
  have hhi : hi f' g' a = 2 * transform u a := by
    unfold hi spec transform
    rw [← total_sub, ← total_scale]
    apply congrArg (total 8); funext x
    rw [← Int.sub_mul, hdiff x, Int.mul_assoc]
  have h1 := hv a; have h2 := hu a
  rw [hlo, hhi]
  constructor <;> omega

/-- Layer B section-enumeration hypotheses (discharged by `sel`, `sel2`, `sel_e`). -/
structure SectionHypotheses : Prop where
  enum7  : SectionEnum
  enum94 : SectionEnumE excl6MaskT94 eBoundsT94
  enum96 : SectionEnumE excl6MaskT96 []

/-- Layer C residual large-search computational closures (each corresponding 1-to-1 to a
    SHA-256-manifested replay packet; notice `t ≤ 92`, `t = 112`, `t = 114`, `t = 116 (k=12)`,
    `t = 118`, `t ≥ 120`, `t = 94` frontier, `t = 96 (0,51,27)/(21,34,12)`, `t ≥ 104` rank 8,
    `t ≥ 108` rank 6, and `t ≤ 112` `|Z| = 64` are ALL discharged directly in Lean!). -/
structure ComputationalClosures : Prop where
  /-- `t = 94` non-frontier profiles (all 17 rank-8 frontier profiles are closed in Lean). -/
  t94_nonfrontier : ∀ f g : Half, Adapted242 f g → agreements f g = 94 →
    Zc f g ∈ [96, 112, 120, 128, 136, 144] →
    ¬ (rr (β8 f g) = 1 ∧
        ((suppList (clsA f g)).length, (suppList (clsB f g)).length,
         (suppList (clsC f g)).length) ∈ t94FrontierProfiles) → False
  /-- `t = 96` profiles outside Lean-closed `Zc ∈ {64,160,192,256}`, `(0,51,27)`, `(21,34,12)`
      (`nl242_t96_closure.zip`). -/
  t96_remaining : ∀ f g : Half, Adapted242 f g → agreements f g = 96 →
    Zc f g ∈ [96, 112, 120, 128, 136, 144] →
    ¬ (rr (β8 f g) = 1 ∧ (pa f g = 0 ∧ pb f g = 51 ∧ pc f g = 27)) →
    ¬ (rr (β8 f g) = 1 ∧ (pa f g = 21 ∧ pb f g = 34 ∧ pc f g = 12)) → False
  /-- `t = 98` profiles outside Lean-closed `Zc ∈ {64,160,192,256}` (`nl242_t98_closure.zip`;
      this field includes the rank-6 case `|Z| = 144`). -/
  t98_remaining : ∀ f g : Half, Adapted242 f g → agreements f g = 98 →
    Zc f g ∈ [96, 112, 120, 128, 136, 144] → False
  /-- `t = 100` surviving cases with `Zc ∈ {96,112,120,128,136}` (`nl242_top_closure.zip`). -/
  t100_remaining : ∀ f g : Half, Adapted242 f g → agreements f g = 100 →
    Zc f g ∈ [96, 112, 120, 128, 136] → False
  /-- `t = 102` surviving cases with `Zc ∈ {96,112,120,128}` (`nl242_top_closure.zip`). -/
  t102_remaining : ∀ f g : Half, Adapted242 f g → agreements f g = 102 →
    Zc f g ∈ [96, 112, 120, 128] → False
  /-- `t = 104` surviving `(r = 4, Zc = 96)` and `(r = 6, Zc = 112)` (`nl242_middle_closure.zip` /
      `nl242_top_closure.zip`; ranks `0, 2, 8` are ALL unconditionally closed in Lean!). -/
  t104_r4_r6 : ∀ f g : Half, Adapted242 f g → agreements f g = 104 →
    ((rr (β8 f g) = 16 ∧ Zc f g = 96) ∨ (rr (β8 f g) = 4 ∧ Zc f g = 112)) → False
  /-- `t = 106` surviving `(r = 4, Zc = 96)` and `(r = 6, Zc = 112)` (`nl242_middle_closure.zip` /
      `nl242_top_closure.zip`; ranks `0, 2, 8` are ALL unconditionally closed in Lean!). -/
  t106_r4_r6 : ∀ f g : Half, Adapted242 f g → agreements f g = 106 →
    ((rr (β8 f g) = 16 ∧ Zc f g = 96) ∨ (rr (β8 f g) = 4 ∧ Zc f g = 112)) → False
  /-- `t = 108` surviving `(r = 4, Zc = 96)` (`nl242_middle_closure.zip`; ranks `0, 2, 6, 8`
      are ALL unconditionally closed in Lean!). -/
  t108_r4_Z96 : ∀ f g : Half, Adapted242 f g → agreements f g = 108 →
    rr (β8 f g) = 16 → Zc f g = 96 → False
  /-- `t = 110` surviving `(r = 4, Zc = 96)` with `n0 ≥ 8` (`nl242_top_closure.zip`; ranks
      `0, 2, 6, 8` and `n0 ≥ 8` are ALL unconditionally closed in Lean!). -/
  t110_r4_Z96 : ∀ f g : Half, Adapted242 f g → agreements f g = 110 →
    rr (β8 f g) = 16 → Zc f g = 96 → 8 ≤ n0 f g → False

private theorem no_Zc_192_of_t_ge_94 (f g : Half) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (ht : 94 ≤ agreements f g) (hZ : Zc f g = 192) : False := by
  have ⟨hb, hn0, hn8⟩ := low_defect_budget f g dc lores locap
  omega

private theorem pa_eq_suppList_len (f g : Half) : pa f g = (suppList (clsA f g)).length := by
  have h := suppList_length_eq_total (clsA f g)
  unfold Balanced242Plateau.ind at h
  unfold pa cnt Balanced242Reduction.ind
  omega

private theorem pb_eq_suppList_len (f g : Half) : pb f g = (suppList (clsB f g)).length := by
  have h := suppList_length_eq_total (clsB f g)
  unfold Balanced242Plateau.ind at h
  unfold pb cnt Balanced242Reduction.ind
  omega

private theorem pc_eq_suppList_len (f g : Half) : pc f g = (suppList (clsC f g)).length := by
  have h := suppList_length_eq_total (clsC f g)
  unfold Balanced242Plateau.ind at h
  unfold pc cnt Balanced242Reduction.ind
  omega

/-- Helper: at `t ∈ {94..112}`, Lean unconditionally eliminates `Zc ∈ {64, 160, 192, 256}` and all of rank 2. -/
private theorem zc_range_94_98 (f g : Half) (had : Adapted242 f g)
    (ht_lo : 94 ≤ agreements f g) (ht_hi : agreements f g ≤ 112) :
    Zc f g ∈ [96, 112, 120, 128, 136, 144] := by
  obtain ⟨res, hicap, dc, lores, locap, _⟩ := had
  rcases rank_Zc_values f g res dc lores with
    ⟨_, hZ | hZ⟩ | ⟨hrr, _⟩ | ⟨_, hZ | hZ | hZ⟩ | ⟨_, hZ | hZ | hZ⟩ | ⟨_, hZ | hZ⟩
  · simp [hZ]
  · exact False.elim (no_Zc_256_of_t_ge_64 f g dc lores locap hZ (by omega))
  · exact False.elim (no_Z64_of_t_le_112 f g res hicap hrr ht_hi)
  · simp [hZ]
  · simp [hZ]
  · exact False.elim (no_Zc_160_of_t_ge_94 f g dc lores locap hZ ht_lo)
  · simp [hZ]
  · simp [hZ]
  · simp [hZ]
  · simp [hZ]
  · simp [hZ]

/-- **Coordinate-free Master Theorem (Direct Endpoint Route — ZERO `CoveringRadius244`!)**:
    No balanced 9-variable Boolean function `F : W 9 → Bool` has nonlinearity 242
    (`∀ a, |booleanSpec F a| ≤ 28`), assuming only `SectionHypotheses` (Layer B),
    `ComputationalClosures` (Layer C for `t ∈ {94..110}`), and `EndpointK16Direct`
    (the sole surviving `t = 116, k = 16` switched complementary pair). -/
theorem no_balanced_9var_nl242_direct (F : W 9 → Bool)
    (hbal : total 9 (fun x => sign (F x)) = 0)
    (hcap : ∀ a : W 9, (booleanSpec F a).natAbs ≤ 28)
    (hsec : SectionHypotheses)
    (hcomp : ComputationalClosures)
    (h116 : EndpointK16Direct) : False := by
  -- Step 0: Coordinate-free reduction to adapted halves `(f, g)` (100% Lean, unconditional!)
  have hs := supportXor_ne_zero_of_cap28 F hbal hcap
  obtain ⟨f, g, haxis, hbal', hlo_m, hhi_m, _⟩ := to_adapted F hbal hs
  have hcap' : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28 := fun a => by
    obtain ⟨b1, hb1⟩ := hlo_m a; obtain ⟨b2, hb2⟩ := hhi_m a
    exact ⟨hb1 ▸ hcap b1, hb2 ▸ hcap b2⟩
  have split : total 8 (fun x => sign (f x) + sign (g x)) = 0 := by rw [total_add]; exact hbal'
  have dc : lo f g (zero 8) = 0 := by
    simpa [lo, spec, transform, chr, dot_zero, sign, total_add] using split
  have lores (a : W 8) := (adapted_blocks f g haxis hbal' a).1
  have res (a : W 8) := (adapted_blocks f g haxis hbal' a).2
  have hicap (a : W 8) := (hcap' a).2
  have locap (a : W 8) : (lo f g a).natAbs ≤ 24 := by have := (hcap' a).1; have := lores a; omega
  -- Step 1: Lean window theorem closes ALL `t ≤ 92` (via `SectionEnum`) and `t ≥ 120` (unconditional!)
  have ⟨hge94, hle118, heven⟩ := agreements_window_94_to_118 hsec.enum7 f g haxis hbal' hcap'
  have had : Adapted242 f g := ⟨res, hicap, dc, lores, locap, heven⟩
  -- Split across the 13 remaining even agreement counts `t ∈ {94, 96, ..., 118}`
  have ht_cases :
      agreements f g = 94 ∨ agreements f g = 96 ∨ agreements f g = 98 ∨
      agreements f g = 100 ∨ agreements f g = 102 ∨ agreements f g = 104 ∨
      agreements f g = 106 ∨ agreements f g = 108 ∨ agreements f g = 110 ∨
      agreements f g = 112 ∨ agreements f g = 114 ∨ agreements f g = 116 ∨
      agreements f g = 118 := by omega
  rcases ht_cases with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
  · -- t = 94: all 17 rank-8 frontier profiles closed in Lean (`Balanced242T94`)
    have hZ := zc_range_94_98 f g had (by omega) (by omega)
    by_cases hfr : rr (β8 f g) = 1 ∧
        ((suppList (clsA f g)).length, (suppList (clsB f g)).length,
         (suppList (clsC f g)).length) ∈ t94FrontierProfiles
    · exact t94_all_17_frontier_excluded hsec.enum94 f g res hicap ht hfr.1 hfr.2
    · exact hcomp.t94_nonfrontier f g had ht hZ hfr
  · -- t = 96: `Zc ∈ {64,160,192,256}`, `(0,51,27)`, `(21,34,12)` closed in Lean
    have hZ := zc_range_94_98 f g had (by omega) (by omega)
    by_cases h051 : rr (β8 f g) = 1 ∧ (pa f g = 0 ∧ pb f g = 51 ∧ pc f g = 27)
    · exact excl_96_0_51_27 f g res hicap ht h051.2.1 h051.2.2.1 h051.2.2.2 h051.1 hsec.enum96
    · by_cases h2134 : rr (β8 f g) = 1 ∧ (pa f g = 21 ∧ pb f g = 34 ∧ pc f g = 12)
      · exact t96_21_34_12_excluded hsec.enum94 f g res hicap ht h2134.1
          (by rw [← pa_eq_suppList_len]; exact h2134.2.1)
          (by rw [← pb_eq_suppList_len]; exact h2134.2.2.1)
          (by rw [← pc_eq_suppList_len]; exact h2134.2.2.2)
      · exact hcomp.t96_remaining f g had ht hZ h051 h2134
  · -- t = 98: `Zc ∈ {64,160,192,256}` closed in Lean. `t98_remaining` includes `Zc = 144`
    have hZ := zc_range_94_98 f g had (by omega) (by omega)
    exact hcomp.t98_remaining f g had ht hZ
  · -- t = 100: `Zc ∈ {64,144,160,192,256}` closed unconditionally in Lean
    have hZ0 := zc_range_94_98 f g had (by omega) (by omega)
    have hne144 : Zc f g ≠ 144 := fun h => no_Zc_144_of_t_ge_100 f g dc lores locap h (by omega)
    have hZ : Zc f g ∈ [96, 112, 120, 128, 136] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hZ0 ⊢
      rcases hZ0 with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact absurd h hne144
    exact hcomp.t100_remaining f g had ht hZ
  · -- t = 102: `Zc ∈ {64,136,144,160,192,256}` closed unconditionally in Lean
    have hZ0 := zc_range_94_98 f g had (by omega) (by omega)
    have hne144 : Zc f g ≠ 144 := fun h => no_Zc_144_of_t_ge_100 f g dc lores locap h (by omega)
    have hne136 : Zc f g ≠ 136 := fun h => no_Zc_136_of_t_ge_102 f g dc lores locap h (by omega)
    have hZ : Zc f g ∈ [96, 112, 120, 128] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hZ0 ⊢
      rcases hZ0 with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact absurd h hne136
      · exact absurd h hne144
    exact hcomp.t102_remaining f g had ht hZ
  · -- t = 104: ranks 0, 2, 8 ALL closed unconditionally in Lean (`Balanced242T104R8` + `LowBlock` + `Z64Switch`)!
    rcases rank_Zc_values f g res dc lores with
      ⟨_, hZ | hZ⟩ | ⟨hrr, _⟩ | ⟨hrr, hZ | hZ | hZ⟩ | ⟨hrr, hZ | hZ | hZ⟩ | ⟨hrr, _⟩
    · exact no_Zc_128_of_t_ge_104 f g dc lores locap hZ (by omega)
    · exact no_Zc_256_of_t_ge_64 f g dc lores locap hZ (by omega)
    · exact no_Z64_of_t_le_112 f g res hicap hrr (by omega)
    · exact hcomp.t104_r4_r6 f g had ht (Or.inl ⟨hrr, hZ⟩)
    · exact no_Zc_128_of_t_ge_104 f g dc lores locap hZ (by omega)
    · exact no_Zc_160_of_t_ge_94 f g dc lores locap hZ (by omega)
    · exact hcomp.t104_r4_r6 f g had ht (Or.inr ⟨hrr, hZ⟩)
    · exact no_Zc_128_of_t_ge_104 f g dc lores locap hZ (by omega)
    · exact no_Zc_144_of_t_ge_100 f g dc lores locap hZ (by omega)
    · exact no_rank8_of_t_ge_104 f g res dc lores locap heven (by omega) hrr
  · -- t = 106: ranks 0, 2, 8 ALL closed unconditionally in Lean!
    rcases rank_Zc_values f g res dc lores with
      ⟨_, hZ | hZ⟩ | ⟨hrr, _⟩ | ⟨hrr, hZ | hZ | hZ⟩ | ⟨hrr, hZ | hZ | hZ⟩ | ⟨hrr, _⟩
    · exact no_Zc_128_of_t_ge_104 f g dc lores locap hZ (by omega)
    · exact no_Zc_256_of_t_ge_64 f g dc lores locap hZ (by omega)
    · exact no_Z64_of_t_le_112 f g res hicap hrr (by omega)
    · exact hcomp.t106_r4_r6 f g had ht (Or.inl ⟨hrr, hZ⟩)
    · exact no_Zc_128_of_t_ge_104 f g dc lores locap hZ (by omega)
    · exact no_Zc_160_of_t_ge_94 f g dc lores locap hZ (by omega)
    · exact hcomp.t106_r4_r6 f g had ht (Or.inr ⟨hrr, hZ⟩)
    · exact no_Zc_128_of_t_ge_104 f g dc lores locap hZ (by omega)
    · exact no_Zc_144_of_t_ge_100 f g dc lores locap hZ (by omega)
    · exact no_rank8_of_t_ge_104 f g res dc lores locap heven (by omega) hrr
  · -- t = 108: ranks 0, 2, 6, 8 ALL closed unconditionally in Lean (`Balanced242T108R6` + `T104R8` + `LowBlock`)!
    rcases rank_Zc_values f g res dc lores with
      ⟨_, hZ | hZ⟩ | ⟨hrr, _⟩ | ⟨hrr, hZ | hZ | hZ⟩ | ⟨hrr, _⟩ | ⟨hrr, _⟩
    · exact no_Zc_128_of_t_ge_104 f g dc lores locap hZ (by omega)
    · exact no_Zc_256_of_t_ge_64 f g dc lores locap hZ (by omega)
    · exact no_Z64_of_t_le_112 f g res hicap hrr (by omega)
    · exact hcomp.t108_r4_Z96 f g had ht hrr hZ
    · exact no_Zc_128_of_t_ge_104 f g dc lores locap hZ (by omega)
    · exact no_Zc_160_of_t_ge_94 f g dc lores locap hZ (by omega)
    · exact no_t108_rank6 f g res dc lores locap ht hrr
    · exact no_rank8_of_t_ge_104 f g res dc lores locap heven (by omega) hrr
  · -- t = 110: ranks 0, 2, 6, 8 ALL closed unconditionally in Lean (and `n0 ≥ 8` proved for `r=4, Z=96`)!
    rcases rank_Zc_values f g res dc lores with
      ⟨_, hZ | hZ⟩ | ⟨hrr, _⟩ | ⟨hrr, hZ | hZ | hZ⟩ | ⟨_, hZ | hZ | hZ⟩ | ⟨hrr, _⟩
    · exact no_Zc_128_of_t_ge_104 f g dc lores locap hZ (by omega)
    · exact no_Zc_256_of_t_ge_64 f g dc lores locap hZ (by omega)
    · exact no_Z64_of_t_le_112 f g res hicap hrr (by omega)
    · exact hcomp.t110_r4_Z96 f g had ht hrr hZ
        (rank4_Z96_n0_ge8 f g res dc lores locap heven hrr hZ)
    · exact no_Zc_128_of_t_ge_104 f g dc lores locap hZ (by omega)
    · exact no_Zc_160_of_t_ge_94 f g dc lores locap hZ (by omega)
    · exact no_Zc_112_of_t_ge_110 f g dc lores locap hZ (by omega)
    · exact no_Zc_128_of_t_ge_104 f g dc lores locap hZ (by omega)
    · exact no_Zc_144_of_t_ge_100 f g dc lores locap hZ (by omega)
    · exact no_rank8_of_t_ge_104 f g res dc lores locap heven (by omega) hrr
  · -- t = 112: 100% UNCONDITIONALLY CLOSED IN LEAN 4 (`Balanced242T112`)!
    exact no_t112 f g res hicap dc lores locap ht
  · -- t = 114: 100% UNCONDITIONALLY CLOSED IN LEAN 4 (`Balanced242T114`)!
    exact no_t114 f g res hicap dc lores locap ht
  · -- t = 116: `k = 12` unconditionally closed in Lean (`Balanced242T114`), `k = 16` via `EndpointK16Direct`!
    have hk16 := t116_forces_k16 f g res hicap dc lores locap ht
    obtain ⟨u, v, hcomp_uv, hv_lev, hu_lev⟩ :=
      endpoint_switched_blocks f g res hicap dc lores locap (Or.inr ht)
    apply h116
    refine ⟨u, v, hcomp_uv, hv_lev, ?_, ?_⟩
    · intro a; rw [hu_lev a]; cases clsA f g a || clsC f g a <;> simp
    · have hpt (a : W 8) : (if (transform u a).natAbs = 4 then (1 : Int) else 0) =
          Balanced242Reduction.ind (clsA f g) a + Balanced242Reduction.ind (clsC f g) a := by
        rw [hu_lev a]
        unfold Balanced242Reduction.ind clsA clsC
        rcases hi_values f g res hicap a with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
      rw [funext hpt, total_add]
      exact hk16
  · -- t = 118: 100% UNCONDITIONALLY CLOSED IN LEAN 4 (`Balanced242T118`)!
    exact no_t118 f g dc lores locap ht

/-- **Coordinate-free Master Theorem (Covering-Radius Route)**:
    No balanced 9-variable Boolean function `F : W 9 → Bool` has nonlinearity 242
    (`∀ a, |booleanSpec F a| ≤ 28`), using `CoveringRadius244` (`nl244_verify.zip`) for the
    sole remaining endpoint case `t = 116, k = 16`. -/
theorem no_balanced_9var_nl242 (F : W 9 → Bool)
    (hbal : total 9 (fun x => sign (F x)) = 0)
    (hcap : ∀ a : W 9, (booleanSpec F a).natAbs ≤ 28)
    (hsec : SectionHypotheses)
    (hcomp : ComputationalClosures)
    (hcov : CoveringRadius244) : False :=
  no_balanced_9var_nl242_direct F hbal hcap hsec hcomp (endpointK16_of_coveringRadius hcov)

#print axioms endpointK16_of_coveringRadius
#print axioms no_balanced_9var_nl242_direct
#print axioms no_balanced_9var_nl242

end Balanced242Master
