/-
  Kernel-checked Lean 4 exclusion of the 2 layered anchor-pair `t = 94` frontier profiles:
    - `(94, 12, 25, 25, 8)` (108 anchor-pair Farkas certificates + final affine cert)
    - `(94, 15, 24, 22, 8)` (97 anchor-pair Farkas certificates + final affine cert)
  Zero `sorry`, zero `native_decide`.
-/
import Balanced242T94Data
import Balanced242FastCond
import Balanced242T94L12_base
import Balanced242T94L15_base
import Balanced242T94L12_c0
import Balanced242T94L12_c1
import Balanced242T94L12_c2
import Balanced242T94L12_c3
import Balanced242T94L12_c4
import Balanced242T94L12_c5
import Balanced242T94L12_c6
import Balanced242T94L12_c7
import Balanced242T94L15_c0
import Balanced242T94L15_c1
import Balanced242T94L15_c2
import Balanced242T94L15_c3
import Balanced242T94L15_c4
import Balanced242T94L15_c5
import Balanced242T94L15_c6

namespace Balanced242T94Layered
open FrozenShells Balanced242Parents Balanced242Support Balanced242Rank Balanced242Global
open Balanced242Reduction (clsA clsB clsC)
open Balanced242Krawtchouk (suppList)
open Balanced242Farkas (SectionEnumE checkProfileCert checkProfileCert_layer1 exclude_rank8_profile)
open Balanced242FastCond (checkLayerFast2 checkLayerFast2_append checkLayerWithMask_of_fast2)
open Balanced242T94Data

theorem layer0_94_12_25_25_fast2_ok : checkLayerFast2 12 25 25 mask_94_12_25_25 layer0_94_12_25_25 = true := by
  unfold layer0_94_12_25_25
  simp only [checkLayerFast2_append, Balanced242T94L12_c0.chunk_ok, Balanced242T94L12_c1.chunk_ok, Balanced242T94L12_c2.chunk_ok, Balanced242T94L12_c3.chunk_ok, Balanced242T94L12_c4.chunk_ok, Balanced242T94L12_c5.chunk_ok, Balanced242T94L12_c6.chunk_ok, Balanced242T94L12_c7.chunk_ok, Bool.and_true]

theorem cert_94_12_25_25 : checkProfileCert excl6MaskT94 eBoundsT94 94 12 25 25 [layer0_94_12_25_25] final_94_12_25_25 = true :=
  checkProfileCert_layer1 excl6MaskT94 eBoundsT94 94 12 25 25
    splits_94_12_25_25 mask_94_12_25_25 layer0_94_12_25_25 final_94_12_25_25
    (by decide)
    Balanced242T94L12_base.splits_eq
    Balanced242T94L12_base.mask_eq
    (checkLayerWithMask_of_fast2 12 25 25 mask_94_12_25_25 layer0_94_12_25_25 layer0_94_12_25_25_fast2_ok)
    Balanced242T94L12_base.final_ok

theorem excl_94_12_25_25 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 12)
    (hb : (suppList (clsB f g)).length = 25)
    (hc : (suppList (clsC f g)).length = 25) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 12 25 25 [layer0_94_12_25_25] final_94_12_25_25
    cert_94_12_25_25 f g res hicap ht hrr ha hb hc

theorem layer0_94_15_24_22_fast2_ok : checkLayerFast2 15 24 22 mask_94_15_24_22 layer0_94_15_24_22 = true := by
  unfold layer0_94_15_24_22
  simp only [checkLayerFast2_append, Balanced242T94L15_c0.chunk_ok, Balanced242T94L15_c1.chunk_ok, Balanced242T94L15_c2.chunk_ok, Balanced242T94L15_c3.chunk_ok, Balanced242T94L15_c4.chunk_ok, Balanced242T94L15_c5.chunk_ok, Balanced242T94L15_c6.chunk_ok, Bool.and_true]

theorem cert_94_15_24_22 : checkProfileCert excl6MaskT94 eBoundsT94 94 15 24 22 [layer0_94_15_24_22] final_94_15_24_22 = true :=
  checkProfileCert_layer1 excl6MaskT94 eBoundsT94 94 15 24 22
    splits_94_15_24_22 mask_94_15_24_22 layer0_94_15_24_22 final_94_15_24_22
    (by decide)
    Balanced242T94L15_base.splits_eq
    Balanced242T94L15_base.mask_eq
    (checkLayerWithMask_of_fast2 15 24 22 mask_94_15_24_22 layer0_94_15_24_22 layer0_94_15_24_22_fast2_ok)
    Balanced242T94L15_base.final_ok

theorem excl_94_15_24_22 (henum : SectionEnumE excl6MaskT94 eBoundsT94)
    (f g : Half) (res : ∀ x, hi f g x % 8 = 4) (hicap : ∀ x, (hi f g x).natAbs ≤ 28)
    (ht : agreements f g = 94) (hrr : rr (β8 f g) = 1)
    (ha : (suppList (clsA f g)).length = 15)
    (hb : (suppList (clsB f g)).length = 24)
    (hc : (suppList (clsC f g)).length = 22) : False :=
  exclude_rank8_profile excl6MaskT94 eBoundsT94 henum 94 15 24 22 [layer0_94_15_24_22] final_94_15_24_22
    cert_94_15_24_22 f g res hicap ht hrr ha hb hc

end Balanced242T94Layered

#print axioms Balanced242T94Layered.excl_94_12_25_25
#print axioms Balanced242T94Layered.excl_94_15_24_22
