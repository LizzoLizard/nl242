/-
  Balanced242T94.lean — Master Lean 4 kernel-verified closure of all 17 remaining
  `t = 94` rank-8 frontier profiles (15 direct Krawtchouk Farkas + 2 anchor-pair
  layered Farkas) plus the additional `t = 96` exclusion `(21, 34, 12, 8)`.

  Zero Mathlib, zero `sorry`, zero `native_decide`.
  Only explicit assumption: `SectionEnumE excl6MaskT94 eBoundsT94` (252 distinct excluded
  rank-6 sections + 59 `sel_e` exception-weight lower bounds).
-/
import Balanced242T94Direct
import Balanced242T94Layered

namespace Balanced242T94
open FrozenShells Balanced242Parents Balanced242Support Balanced242Rank Balanced242Global
open Balanced242Reduction (clsA clsB clsC)
open Balanced242Krawtchouk (suppList)
open Balanced242Farkas (Triple SectionEnumE)
open Balanced242T94Data (excl6MaskT94 eBoundsT94)

/-- The exact 17 remaining `t = 94` rank-8 profiles from `remaining_profiles.tsv`. -/
def t94FrontierProfiles : List Triple :=
  [(0, 29, 37), (1, 32, 34), (3, 28, 34), (4, 31, 31), (5, 34, 28), (6, 27, 31), (7, 30, 28), (8, 33, 25), (9, 26, 28), (10, 29, 25), (11, 32, 22), (12, 25, 25), (13, 28, 22), (14, 31, 19), (15, 24, 22), (16, 27, 19), (17, 30, 16)]

/-- Every one of the 17 remaining `t = 94` rank-8 frontier profiles is impossible
    for real balanced 9-variable Boolean halves `(f, g)` (assuming `SectionEnumE`). -/
theorem t94_all_17_frontier_excluded (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (hprof : ((suppList (clsA f g)).length, (suppList (clsB f g)).length, (suppList (clsC f g)).length) ∈
      t94FrontierProfiles) : False := by
  generalize ha : (suppList (clsA f g)).length = a at hprof
  generalize hb : (suppList (clsB f g)).length = b at hprof
  generalize hc : (suppList (clsC f g)).length = c at hprof
  unfold t94FrontierProfiles at hprof
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hprof
  rcases hprof with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  · exact Balanced242T94Direct.excl_94_0_29_37 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_1_32_34 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_3_28_34 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_4_31_31 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_5_34_28 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_6_27_31 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_7_30_28 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_8_33_25 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_9_26_28 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_10_29_25 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_11_32_22 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Layered.excl_94_12_25_25 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_13_28_22 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_14_31_19 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Layered.excl_94_15_24_22 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_16_27_19 henum f g res hicap ht hrr ha hb hc
  · exact Balanced242T94Direct.excl_94_17_30_16 henum f g res hicap ht hrr ha hb hc

/-- Re-export of the additional `t = 96` rank-8 profile exclusion `(21, 34, 12, 8)`. -/
theorem t96_21_34_12_excluded (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 96) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 21)
    (hb : (suppList (clsB f g)).length = 34)
    (hc : (suppList (clsC f g)).length = 12) : False :=
  Balanced242T94Direct.excl_96_21_34_12 henum f g res hicap ht hrr ha hb hc

end Balanced242T94

#print axioms Balanced242T94.t94_all_17_frontier_excluded
#print axioms Balanced242T94.t96_21_34_12_excluded
