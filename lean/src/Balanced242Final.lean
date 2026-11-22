/-
  Exclusion of t = 86, 88, 90, 92 from the halves, with the section and drop facts derived.

  The only hypotheses beyond the adapted-table conditions (hi = 4 mod 8, |hi| <= 28) are
    * `SectionEnum`: the finite enumeration claims for one 7-variable section;
    * `hrank`: the global rank condition `r ∈ ranks t k` for the polar rank r of the phase
      (2^r = number of Walsh-support points of the phase).
-/
import Balanced242Global
import Balanced242PairCheck86
import Balanced242PairCheck88
import Balanced242PairCheck90
import Balanced242PairCheck92

namespace Balanced242Final
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Global
open Balanced242Reduction (pa pc no_242_from_halves)
open Balanced242Pair (ranks rowCheck)
open Balanced242Rank (perp rr)

theorem no_242_given_rank (t : Nat) (hc : ∀ a < (8 * t - 480) / 6 + 1, rowCheck t a = true)
    (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (cap : ∀ a, (hi f g a).natAbs ≤ 28)
    (ht : agreements f g = t) (ht60 : 60 ≤ t) (hev : t % 2 = 0) (enum : SectionEnum)
    (hrank : ∀ r : Nat, cntGood f g = 2 ^ r → r ∈ ranks t (pa f g + pc f g)) : False := by
  have hev' : agreements f g % 2 = 0 := by omega
  have hcp := cnt_perp_eq f g res
  have hd := drop_count f g res
  rcases global_levels f g res with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact no_242_from_halves t hc f g res cap ht ht60 8 (perp (β8 f g)) (hrank 8 (by rw [h2]; rfl))
      (by rw [hd, h2]; rfl)
      (dir_admissible f g res cap hev' enum 8 16 (Or.inl ⟨rfl, rfl, h1⟩) (by rw [hcp, h2]; rfl))
  · exact no_242_from_halves t hc f g res cap ht ht60 6 (perp (β8 f g)) (hrank 6 (by rw [h2]; rfl))
      (by rw [hd, h2]; rfl)
      (dir_admissible f g res cap hev' enum 6 32 (Or.inr (Or.inl ⟨rfl, rfl, h1⟩)) (by rw [hcp, h2]; rfl))
  · exact no_242_from_halves t hc f g res cap ht ht60 4 (perp (β8 f g)) (hrank 4 (by rw [h2]; rfl))
      (by rw [hd, h2]; rfl)
      (dir_admissible f g res cap hev' enum 4 64 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1⟩)))
        (by rw [hcp, h2]; rfl))
  · exact no_242_from_halves t hc f g res cap ht ht60 2 (perp (β8 f g)) (hrank 2 (by rw [h2]; rfl))
      (by rw [hd, h2]; rfl)
      (dir_admissible f g res cap hev' enum 2 128 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1⟩)))) (by rw [hcp, h2]; rfl))
  · exact no_242_from_halves t hc f g res cap ht ht60 0 (perp (β8 f g)) (hrank 0 (by rw [h2]; rfl))
      (by rw [hd, h2]; rfl)
      (dir_admissible f g res cap hev' enum 0 256 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h1⟩)))) (by rw [hcp, h2]; rfl))

def ExcludedGivenRank (t : Nat) : Prop :=
  SectionEnum → ∀ (f g : Half), (∀ a, hi f g a % 8 = 4) → (∀ a, (hi f g a).natAbs ≤ 28) →
    agreements f g = t → (∀ r : Nat, cntGood f g = 2 ^ r → r ∈ ranks t (pa f g + pc f g)) → False

theorem excluded_86 : ExcludedGivenRank 86 := fun enum f g res cap ht hr =>
  no_242_given_rank 86 Balanced242Pair.rows_86 f g res cap ht (by decide) (by decide) enum hr
theorem excluded_88 : ExcludedGivenRank 88 := fun enum f g res cap ht hr =>
  no_242_given_rank 88 Balanced242Pair.rows_88 f g res cap ht (by decide) (by decide) enum hr
theorem excluded_90 : ExcludedGivenRank 90 := fun enum f g res cap ht hr =>
  no_242_given_rank 90 Balanced242Pair.rows_90 f g res cap ht (by decide) (by decide) enum hr
theorem excluded_92 : ExcludedGivenRank 92 := fun enum f g res cap ht hr =>
  no_242_given_rank 92 Balanced242Pair.rows_92 f g res cap ht (by decide) (by decide) enum hr

end Balanced242Final

#print axioms Balanced242Final.excluded_86
#print axioms Balanced242Final.excluded_92
