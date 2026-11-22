/- Low-RAM 1-anchor-per-theorem kernel verification of layer 0 (10 anchors) for (96,2,47,27,8). -/
import Balanced242T96Data
import Balanced242FastCond

namespace Balanced242T96_2_47_27_L0
open Balanced242FastCond Balanced242T96Data

private theorem anc_0 : checkCondCertFast2 (0, 2, 18) (Nat.sub 2 0, Nat.sub 47 2, Nat.sub 27 18) mask_96_2_47_27 [(1, (-64)), (3, 13), (4, 1), (7, 2)] = true := by
  decide +kernel

private theorem anc_1 : checkCondCertFast2 (0, 3, 19) (Nat.sub 2 0, Nat.sub 47 3, Nat.sub 27 19) mask_96_2_47_27 [(0, (-160)), (3, 13), (4, 5), (7, 14), (8, 8), (9, 2), (10, 10), (11, 8), (12, 40), (13, 20)] = true := by
  decide +kernel

private theorem anc_2 : checkCondCertFast2 (0, 4, 20) (Nat.sub 2 0, Nat.sub 47 4, Nat.sub 27 20) mask_96_2_47_27 [(3, (-1000000)), (4, 333333), (7, 666667)] = true := by
  decide +kernel

private theorem anc_3 : checkCondCertFast2 (0, 5, 21) (Nat.sub 2 0, Nat.sub 47 5, Nat.sub 27 21) mask_96_2_47_27 [(0, (-666683)), (3, (-62500)), (4, 104167), (7, 625000), (10, 166667), (12, 1000000), (13, 500000)] = true := by
  decide +kernel

private theorem anc_4 : checkCondCertFast2 (0, 7, 23) (Nat.sub 2 0, Nat.sub 47 7, Nat.sub 27 23) mask_96_2_47_27 [(0, (-666683)), (3, (-62500)), (4, 104167), (7, 625000), (10, 166667), (12, 1000000), (13, 500000)] = true := by
  decide +kernel

private theorem anc_5 : checkCondCertFast2 (0, 44, 4) (Nat.sub 2 0, Nat.sub 47 44, Nat.sub 27 4) mask_96_2_47_27 [(4, (-4)), (7, 4), (8, 20), (9, (-7)), (10, 1), (11, 4), (12, 12), (13, 6)] = true := by
  decide +kernel

private theorem anc_6 : checkCondCertFast2 (0, 45, 5) (Nat.sub 2 0, Nat.sub 47 45, Nat.sub 27 5) mask_96_2_47_27 [(8, (-4)), (9, (-3)), (10, 1), (11, 8), (13, 2)] = true := by
  decide +kernel

private theorem anc_7 : checkCondCertFast2 (0, 46, 6) (Nat.sub 2 0, Nat.sub 47 46, Nat.sub 27 6) mask_96_2_47_27 [(1, (-281407)), (8, 125628), (10, 40201), (11, 500000), (12, 143216), (13, 241206)] = true := by
  decide +kernel

private theorem anc_8 : checkCondCertFast2 (1, 2, 20) (Nat.sub 2 1, Nat.sub 47 2, Nat.sub 27 20) mask_96_2_47_27 [(4, 83333), (5, (-500000)), (6, 333333), (7, (-250000)), (8, (-1000000))] = true := by
  decide +kernel

private theorem anc_9 : checkCondCertFast2 (1, 3, 21) (Nat.sub 2 1, Nat.sub 47 3, Nat.sub 27 21) mask_96_2_47_27 [(0, (-733)), (3, (-6410)), (4, 44872), (5, (-25641)), (6, 333333), (7, 166667), (8, (-1000000)), (9, 12821), (10, 64103), (11, 51282), (12, 256410), (13, 128205)] = true := by
  decide +kernel

theorem layer0_ok : checkLayerFast2 2 47 27 mask_96_2_47_27 layer0_96_2_47_27 = true := by
  unfold layer0_96_2_47_27 checkLayerFast2
  dsimp only [List.all_cons, List.all_nil]
  rw [anc_0, anc_1, anc_2, anc_3, anc_4, anc_5, anc_6, anc_7, anc_8, anc_9]
  rfl

end Balanced242T96_2_47_27_L0
