/-
  End-to-end exclusion of agreement counts t = 86, 88, 90, 92, starting from any balanced
  nine-variable Boolean function `F : W 9 → Bool` of nonlinearity 242 (every Walsh value of
  absolute value at most 28, with at least one attaining 28 — or equivalently `supportXor F ≠ 0`).

  Remaining hypothesis (the sole trust boundary):
    * `SectionEnum` - the seven-variable enumeration facts (C++ enumerators + MILP).
  (The coordinate change to the adapted axis is proved in `Balanced242Coord.to_adapted`, and
   the covering-radius step `Zc f g ≠ 64` is NOT needed for t ≤ 103: at rank 2 the support
   test is met by the witness 128, see `Balanced242RankCond.rank_cond`.)
  Everything else (coordinate change, plateau theory, hyperplane sections, global rank
  structure, the pair LP rows, the phase identity and the low-support budget) is checked
  by Lean from the definitions.
-/
import Balanced242Final
import Balanced242RankCond
import Balanced242Endpoint
import Balanced242Coord

namespace Balanced242Complete
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Blocks Balanced242Support Balanced242Global
open Balanced242Final (ExcludedGivenRank excluded_86 excluded_88 excluded_90 excluded_92)
open Balanced242RankCond (Zc rank_cond)
open Balanced242Coord (axisAgreements autocorr autocorr_eq_axisAgreements
  supportXor_ne_zero_of_peak28 to_adapted)

theorem no_242_of (t : Nat) (ex : ExcludedGivenRank t) (enum : SectionEnum) (f g : Half)
    (axis : supportXor (halves f g) = (true, zero 8))
    (bal : total 9 (fun x => sign (halves f g x)) = 0)
    (cap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28)
    (hZ64 : Zc f g ≠ 64 ∨ t ≤ 103) (ht : agreements f g = t) : False := by
  have split : total 8 (fun x => sign (f x) + sign (g x)) = 0 := by rw [total_add]; exact bal
  have dc : lo f g (zero 8) = 0 := by
    simpa [lo, spec, transform, chr, dot_zero, sign, total_add] using split
  have lores (a : W 8) := (adapted_blocks f g axis bal a).1
  have res (a : W 8) := (adapted_blocks f g axis bal a).2
  have hicap (a : W 8) := (cap a).2
  have locap (a : W 8) : (lo f g a).natAbs ≤ 24 := by
    have := (cap a).1; have := lores a; omega
  exact ex enum f g res hicap ht (rank_cond f g res hicap dc lores locap t hZ64 ht)

/-- The final statement: no balanced nine-variable function in adapted coordinates with all
Walsh values in [-28, 28] has agreement count 86, 88, 90 or 92, given the seven-variable
enumeration facts. -/
theorem no_242_86_to_92 (enum : SectionEnum) (f g : Half)
    (axis : supportXor (halves f g) = (true, zero 8))
    (bal : total 9 (fun x => sign (halves f g x)) = 0)
    (cap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28) :
    agreements f g ≠ 86 ∧ agreements f g ≠ 88 ∧ agreements f g ≠ 90 ∧ agreements f g ≠ 92 :=
  ⟨fun h => no_242_of 86 excluded_86 enum f g axis bal cap (Or.inr (by decide)) h,
   fun h => no_242_of 88 excluded_88 enum f g axis bal cap (Or.inr (by decide)) h,
   fun h => no_242_of 90 excluded_90 enum f g axis bal cap (Or.inr (by decide)) h,
   fun h => no_242_of 92 excluded_92 enum f g axis bal cap (Or.inr (by decide)) h⟩

/-- Coordinate-free exclusion for any balanced nine-variable function with nonzero `supportXor`. -/
theorem no_242_any_of (t : Nat) (ex : ExcludedGivenRank t) (enum : SectionEnum) (F : W 9 → Bool)
    (bal : total 9 (fun x => sign (F x)) = 0)
    (cap : ∀ a, (booleanSpec F a).natAbs ≤ 28)
    (hs : supportXor F ≠ zero 9)
    (ht : t ≤ 103)
    (hag : axisAgreements F = 2 * (t : Int)) : False := by
  obtain ⟨f, g, haxis, hbal, hlo, hhi, h2t⟩ := to_adapted F bal hs
  have hcap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28 := fun a => by
    obtain ⟨b1, hb1⟩ := hlo a
    obtain ⟨b2, hb2⟩ := hhi a
    exact ⟨hb1 ▸ cap b1, hb2 ▸ cap b2⟩
  exact no_242_of t ex enum f g haxis hbal hcap (Or.inr ht) (by omega)

/-- Coordinate-free top-level theorem: no balanced nine-variable Boolean function of
nonlinearity 242 (`|W_F| ≤ 28` with some `|W_F(a)| = 28`) has agreement count
t ∈ {86, 88, 90, 92} along its canonical `supportXor` axis (i.e., `axisAgreements F ∈ {172, 176, 180, 184}`),
assuming only `SectionEnum`. -/
theorem no_242_86_to_92_any (enum : SectionEnum) (F : W 9 → Bool)
    (bal : total 9 (fun x => sign (F x)) = 0)
    (cap : ∀ a, (booleanSpec F a).natAbs ≤ 28)
    (peak : ∃ a, (booleanSpec F a).natAbs = 28) :
    axisAgreements F ≠ 172 ∧ axisAgreements F ≠ 176 ∧
    axisAgreements F ≠ 180 ∧ axisAgreements F ≠ 184 := by
  have hs := supportXor_ne_zero_of_peak28 F bal peak
  exact ⟨fun h => no_242_any_of 86 excluded_86 enum F bal cap hs (by decide) h,
         fun h => no_242_any_of 88 excluded_88 enum F bal cap hs (by decide) h,
         fun h => no_242_any_of 90 excluded_90 enum F bal cap hs (by decide) h,
         fun h => no_242_any_of 92 excluded_92 enum F bal cap hs (by decide) h⟩

/-- Same coordinate-free exclusion phrased directly in terms of the autocorrelation along `supportXor F`:
`Δ_F(supportXor F) ∉ {-168, -160, -152, -144}`. -/
theorem no_242_86_to_92_autocorr (enum : SectionEnum) (F : W 9 → Bool)
    (bal : total 9 (fun x => sign (F x)) = 0)
    (cap : ∀ a, (booleanSpec F a).natAbs ≤ 28)
    (peak : ∃ a, (booleanSpec F a).natAbs = 28) :
    autocorr F (supportXor F) ≠ -168 ∧ autocorr F (supportXor F) ≠ -160 ∧
    autocorr F (supportXor F) ≠ -152 ∧ autocorr F (supportXor F) ≠ -144 := by
  have hrel := autocorr_eq_axisAgreements F
  have ⟨h86, h88, h90, h92⟩ := no_242_86_to_92_any enum F bal cap peak
  have cancel2 (a b : Int) (h : 2 * a - 512 = 2 * b - 512) : a = b := by
    have h1 : 2 * a = 2 * b := by
      have := congrArg (· + 512) h
      simpa [Int.sub_add_cancel] using this
    exact Int.eq_of_mul_eq_mul_left (by decide) h1
  exact ⟨fun h => h86 (cancel2 _ 172 (hrel.symm.trans h)),
         fun h => h88 (cancel2 _ 176 (hrel.symm.trans h)),
         fun h => h90 (cancel2 _ 180 (hrel.symm.trans h)),
         fun h => h92 (cancel2 _ 184 (hrel.symm.trans h))⟩

end Balanced242Complete

#print axioms Balanced242Complete.no_242_of
#print axioms Balanced242Complete.no_242_86_to_92
#print axioms Balanced242Complete.no_242_any_of
#print axioms Balanced242Complete.no_242_86_to_92_any
#print axioms Balanced242Complete.no_242_86_to_92_autocorr
