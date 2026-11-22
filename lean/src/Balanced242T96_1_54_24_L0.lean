/- Low-RAM 1-anchor-per-theorem kernel verification of layer 0 (20 anchors) for (96,1,54,24,8). -/
import Balanced242T96Data
import Balanced242FastCond

namespace Balanced242T96_1_54_24_L0
open Balanced242FastCond Balanced242T96Data

private theorem anc_0 : checkCondCertFast2 (0, 2, 18) (Nat.sub 1 0, Nat.sub 54 2, Nat.sub 24 18) mask_96_1_54_24 [(3, (-1000000)), (4, 333333), (7, 666667)] = true := by
  decide +kernel

private theorem anc_1 : checkCondCertFast2 (0, 3, 19) (Nat.sub 1 0, Nat.sub 54 3, Nat.sub 24 19) mask_96_1_54_24 [(0, (-12)), (1, (-1000000)), (4, 64216), (7, 41176), (9, (-613)), (10, 14093), (11, 22059), (12, 66176), (13, 6127)] = true := by
  decide +kernel

private theorem anc_2 : checkCondCertFast2 (0, 4, 20) (Nat.sub 1 0, Nat.sub 54 4, Nat.sub 24 20) mask_96_1_54_24 [(3, (-1000000)), (4, 333333), (7, 666667)] = true := by
  decide +kernel

private theorem anc_3 : checkCondCertFast2 (0, 5, 21) (Nat.sub 1 0, Nat.sub 54 5, Nat.sub 24 21) mask_96_1_54_24 [(3, (-5)), (4, 3), (7, 2)] = true := by
  decide +kernel

private theorem anc_4 : checkCondCertFast2 (0, 7, 23) (Nat.sub 1 0, Nat.sub 54 7, Nat.sub 24 23) mask_96_1_54_24 [(0, (-1)), (3, (-233871)), (4, 185484), (7, (-16129)), (11, 32258), (12, 1000000), (13, 387097)] = true := by
  decide +kernel

private theorem anc_5 : checkCondCertFast2 (0, 9, 17) (Nat.sub 1 0, Nat.sub 54 9, Nat.sub 24 17) mask_96_1_54_24 [(0, (-589)), (3, 5507), (4, 58370), (7, 41850), (8, (-1000000)), (9, 5507), (10, 58370), (11, 39648), (12, 66079), (13, 41850)] = true := by
  decide +kernel

private theorem anc_6 : checkCondCertFast2 (0, 11, 19) (Nat.sub 1 0, Nat.sub 54 11, Nat.sub 24 19) mask_96_1_54_24 [(3, (-19231)), (4, 68681), (7, 38462), (8, (-1000000)), (9, 6410), (10, 94322), (11, 40293), (12, 194139), (13, 45788)] = true := by
  decide +kernel

private theorem anc_7 : checkCondCertFast2 (0, 17, 17) (Nat.sub 1 0, Nat.sub 54 17, Nat.sub 24 17) mask_96_1_54_24 [(0, (-36)), (3, 2405), (4, 61262), (7, 35937), (8, (-1000000)), (9, 4669), (10, 63526), (11, 20939), (12, 96774), (13, 40464)] = true := by
  decide +kernel

private theorem anc_8 : checkCondCertFast2 (0, 21, 13) (Nat.sub 1 0, Nat.sub 54 21, Nat.sub 24 13) mask_96_1_54_24 [(0, (-155)), (3, 487), (4, 59417), (7, 35007), (8, (-1000000)), (9, 5622), (10, 67810), (11, 31271), (12, 112937), (13, 43294)] = true := by
  decide +kernel

private theorem anc_9 : checkCondCertFast2 (0, 23, 15) (Nat.sub 1 0, Nat.sub 54 23, Nat.sub 24 15) mask_96_1_54_24 [(3, 3756), (4, 59853), (7, 36199), (8, (-1000000)), (9, 4439), (10, 65272), (11, 29779), (12, 106457), (13, 44668)] = true := by
  decide +kernel

private theorem anc_10 : checkCondCertFast2 (0, 29, 13) (Nat.sub 1 0, Nat.sub 54 29, Nat.sub 24 13) mask_96_1_54_24 [(0, (-159)), (3, 4717), (4, 59581), (7, 36295), (8, (-1000000)), (9, 2700), (10, 64565), (11, 40491), (12, 110648), (13, 42762)] = true := by
  decide +kernel

private theorem anc_11 : checkCondCertFast2 (0, 33, 9) (Nat.sub 1 0, Nat.sub 54 33, Nat.sub 24 9) mask_96_1_54_24 [(0, (-7)), (3, 3794), (4, 57757), (7, 32884), (8, (-1000000)), (9, (-3794)), (10, 83895), (11, 45531), (12, 183811), (13, 68297)] = true := by
  decide +kernel

private theorem anc_12 : checkCondCertFast2 (0, 35, 11) (Nat.sub 1 0, Nat.sub 54 35, Nat.sub 24 11) mask_96_1_54_24 [(3, 3339), (4, 60329), (7, 36064), (8, (-1000000)), (9, 4675), (10, 65227), (11, 29386), (12, 105966), (13, 44078)] = true := by
  decide +kernel

private theorem anc_13 : checkCondCertFast2 (0, 39, 7) (Nat.sub 1 0, Nat.sub 54 39, Nat.sub 24 7) mask_96_1_54_24 [(0, (-50)), (3, 4902), (4, 55503), (7, 40797), (8, (-1000000)), (9, 4902), (10, 66888), (11, 38583), (12, 100569), (13, 44592)] = true := by
  decide +kernel

private theorem anc_14 : checkCondCertFast2 (0, 41, 9) (Nat.sub 1 0, Nat.sub 54 41, Nat.sub 24 9) mask_96_1_54_24 [(3, (-18657)), (4, 41045), (7, (-22388)), (8, (-701493)), (9, (-85821)), (10, 272388), (11, 194030), (12, 1000000), (13, 291045)] = true := by
  decide +kernel

private theorem anc_15 : checkCondCertFast2 (0, 45, 5) (Nat.sub 1 0, Nat.sub 54 45, Nat.sub 24 5) mask_96_1_54_24 [(3, 6410), (4, 57692), (7, 38462), (8, (-1000000)), (9, 6410), (10, 57692), (11, 25641), (12, 76923), (13, 38462)] = true := by
  decide +kernel

private theorem anc_16 : checkCondCertFast2 (0, 47, 7) (Nat.sub 1 0, Nat.sub 54 47, Nat.sub 24 7) mask_96_1_54_24 [(0, (-227)), (3, (-3213)), (4, (-86761)), (9, (-160668)), (10, 277635), (12, 1000000), (13, 307198)] = true := by
  decide +kernel

private theorem anc_17 : checkCondCertFast2 (0, 50, 2) (Nat.sub 1 0, Nat.sub 54 50, Nat.sub 24 2) mask_96_1_54_24 [(8, (-1000000)), (9, 83333), (10, 83333), (11, (-333333)), (12, 333333), (13, (-166667))] = true := by
  decide +kernel

private theorem anc_18 : checkCondCertFast2 (0, 50, 10) (Nat.sub 1 0, Nat.sub 54 50, Nat.sub 24 10) mask_96_1_54_24 [(0, (-4)), (7, 27778), (8, (-1000000)), (9, 27778), (10, 83333), (11, (-222222)), (12, 277778), (13, (-138889))] = true := by
  decide +kernel

private theorem anc_19 : checkCondCertFast2 (0, 52, 4) (Nat.sub 1 0, Nat.sub 54 52, Nat.sub 24 4) mask_96_1_54_24 [(8, (-1000000)), (9, 83333), (10, 83333), (11, (-333333)), (12, 333333), (13, (-166667))] = true := by
  decide +kernel

theorem layer0_ok : checkLayerFast2 1 54 24 mask_96_1_54_24 layer0_96_1_54_24 = true := by
  unfold layer0_96_1_54_24 checkLayerFast2
  dsimp only [List.all_cons, List.all_nil]
  rw [anc_0, anc_1, anc_2, anc_3, anc_4, anc_5, anc_6, anc_7, anc_8, anc_9, anc_10, anc_11, anc_12, anc_13, anc_14, anc_15, anc_16, anc_17, anc_18, anc_19]
  rfl

end Balanced242T96_1_54_24_L0
