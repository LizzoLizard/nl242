/-
  Kernel-checked Lean 4 exclusion of all 15 direct `t = 94` frontier profiles
  plus the additional `t = 96` profile `(21, 34, 12, 8)` via `Balanced242Farkas`.
  Every certificate is verified by Lean's kernel (`decide`, zero `native_decide`).
-/
import Balanced242T94Data

namespace Balanced242T94Direct
open FrozenShells Balanced242Parents Balanced242Support Balanced242Rank Balanced242Global
open Balanced242Reduction (clsA clsB clsC)
open Balanced242Krawtchouk (suppList)
open Balanced242Farkas (SectionEnumE checkProfileCert exclude_rank8_profile)
open Balanced242T94Data

theorem cert_94_0_29_37 : checkProfileCert excl6MaskT94 eBoundsT94 94 0 29 37 [] final_94_0_29_37 = true := by
  decide +kernel

theorem excl_94_0_29_37 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 0)
    (hb : (suppList (clsB f g)).length = 29)
    (hc : (suppList (clsC f g)).length = 37) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 0 29 37 [] final_94_0_29_37
    cert_94_0_29_37 f g res hicap ht hrr ha hb hc

theorem cert_94_1_32_34 : checkProfileCert excl6MaskT94 eBoundsT94 94 1 32 34 [] final_94_1_32_34 = true := by
  decide +kernel

theorem excl_94_1_32_34 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 1)
    (hb : (suppList (clsB f g)).length = 32)
    (hc : (suppList (clsC f g)).length = 34) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 1 32 34 [] final_94_1_32_34
    cert_94_1_32_34 f g res hicap ht hrr ha hb hc

theorem cert_94_3_28_34 : checkProfileCert excl6MaskT94 eBoundsT94 94 3 28 34 [] final_94_3_28_34 = true := by
  decide +kernel

theorem excl_94_3_28_34 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 3)
    (hb : (suppList (clsB f g)).length = 28)
    (hc : (suppList (clsC f g)).length = 34) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 3 28 34 [] final_94_3_28_34
    cert_94_3_28_34 f g res hicap ht hrr ha hb hc

theorem cert_94_4_31_31 : checkProfileCert excl6MaskT94 eBoundsT94 94 4 31 31 [] final_94_4_31_31 = true := by
  decide +kernel

theorem excl_94_4_31_31 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 4)
    (hb : (suppList (clsB f g)).length = 31)
    (hc : (suppList (clsC f g)).length = 31) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 4 31 31 [] final_94_4_31_31
    cert_94_4_31_31 f g res hicap ht hrr ha hb hc

theorem cert_94_5_34_28 : checkProfileCert excl6MaskT94 eBoundsT94 94 5 34 28 [] final_94_5_34_28 = true := by
  decide +kernel

theorem excl_94_5_34_28 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 5)
    (hb : (suppList (clsB f g)).length = 34)
    (hc : (suppList (clsC f g)).length = 28) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 5 34 28 [] final_94_5_34_28
    cert_94_5_34_28 f g res hicap ht hrr ha hb hc

theorem cert_94_6_27_31 : checkProfileCert excl6MaskT94 eBoundsT94 94 6 27 31 [] final_94_6_27_31 = true := by
  decide +kernel

theorem excl_94_6_27_31 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 6)
    (hb : (suppList (clsB f g)).length = 27)
    (hc : (suppList (clsC f g)).length = 31) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 6 27 31 [] final_94_6_27_31
    cert_94_6_27_31 f g res hicap ht hrr ha hb hc

theorem cert_94_7_30_28 : checkProfileCert excl6MaskT94 eBoundsT94 94 7 30 28 [] final_94_7_30_28 = true := by
  decide +kernel

theorem excl_94_7_30_28 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 7)
    (hb : (suppList (clsB f g)).length = 30)
    (hc : (suppList (clsC f g)).length = 28) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 7 30 28 [] final_94_7_30_28
    cert_94_7_30_28 f g res hicap ht hrr ha hb hc

theorem cert_94_8_33_25 : checkProfileCert excl6MaskT94 eBoundsT94 94 8 33 25 [] final_94_8_33_25 = true := by
  decide +kernel

theorem excl_94_8_33_25 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 8)
    (hb : (suppList (clsB f g)).length = 33)
    (hc : (suppList (clsC f g)).length = 25) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 8 33 25 [] final_94_8_33_25
    cert_94_8_33_25 f g res hicap ht hrr ha hb hc

theorem cert_94_9_26_28 : checkProfileCert excl6MaskT94 eBoundsT94 94 9 26 28 [] final_94_9_26_28 = true := by
  decide +kernel

theorem excl_94_9_26_28 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 9)
    (hb : (suppList (clsB f g)).length = 26)
    (hc : (suppList (clsC f g)).length = 28) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 9 26 28 [] final_94_9_26_28
    cert_94_9_26_28 f g res hicap ht hrr ha hb hc

theorem cert_94_10_29_25 : checkProfileCert excl6MaskT94 eBoundsT94 94 10 29 25 [] final_94_10_29_25 = true := by
  decide +kernel

theorem excl_94_10_29_25 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 10)
    (hb : (suppList (clsB f g)).length = 29)
    (hc : (suppList (clsC f g)).length = 25) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 10 29 25 [] final_94_10_29_25
    cert_94_10_29_25 f g res hicap ht hrr ha hb hc

theorem cert_94_11_32_22 : checkProfileCert excl6MaskT94 eBoundsT94 94 11 32 22 [] final_94_11_32_22 = true := by
  decide +kernel

theorem excl_94_11_32_22 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 11)
    (hb : (suppList (clsB f g)).length = 32)
    (hc : (suppList (clsC f g)).length = 22) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 11 32 22 [] final_94_11_32_22
    cert_94_11_32_22 f g res hicap ht hrr ha hb hc

theorem cert_94_13_28_22 : checkProfileCert excl6MaskT94 eBoundsT94 94 13 28 22 [] final_94_13_28_22 = true := by
  decide +kernel

theorem excl_94_13_28_22 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 13)
    (hb : (suppList (clsB f g)).length = 28)
    (hc : (suppList (clsC f g)).length = 22) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 13 28 22 [] final_94_13_28_22
    cert_94_13_28_22 f g res hicap ht hrr ha hb hc

theorem cert_94_14_31_19 : checkProfileCert excl6MaskT94 eBoundsT94 94 14 31 19 [] final_94_14_31_19 = true := by
  decide +kernel

theorem excl_94_14_31_19 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 14)
    (hb : (suppList (clsB f g)).length = 31)
    (hc : (suppList (clsC f g)).length = 19) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 14 31 19 [] final_94_14_31_19
    cert_94_14_31_19 f g res hicap ht hrr ha hb hc

theorem cert_94_16_27_19 : checkProfileCert excl6MaskT94 eBoundsT94 94 16 27 19 [] final_94_16_27_19 = true := by
  decide +kernel

theorem excl_94_16_27_19 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 16)
    (hb : (suppList (clsB f g)).length = 27)
    (hc : (suppList (clsC f g)).length = 19) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 16 27 19 [] final_94_16_27_19
    cert_94_16_27_19 f g res hicap ht hrr ha hb hc

theorem cert_94_17_30_16 : checkProfileCert excl6MaskT94 eBoundsT94 94 17 30 16 [] final_94_17_30_16 = true := by
  decide +kernel

theorem excl_94_17_30_16 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 17)
    (hb : (suppList (clsB f g)).length = 30)
    (hc : (suppList (clsC f g)).length = 16) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 17 30 16 [] final_94_17_30_16
    cert_94_17_30_16 f g res hicap ht hrr ha hb hc

theorem cert_96_21_34_12 : checkProfileCert excl6MaskT94 eBoundsT94 96 21 34 12 [] final_96_21_34_12 = true := by
  decide +kernel

theorem excl_96_21_34_12 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 96) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 21)
    (hb : (suppList (clsB f g)).length = 34)
    (hc : (suppList (clsC f g)).length = 12) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 96 21 34 12 [] final_96_21_34_12
    cert_96_21_34_12 f g res hicap ht hrr ha hb hc

end Balanced242T94Direct

#print axioms Balanced242T94Direct.excl_94_0_29_37
#print axioms Balanced242T94Direct.excl_94_1_32_34
#print axioms Balanced242T94Direct.excl_94_3_28_34
#print axioms Balanced242T94Direct.excl_96_21_34_12
