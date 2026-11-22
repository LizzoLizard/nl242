/- Kernel-checked splits, allowed-half bitmask, and post-peeling final Krawtchouk Farkas cert for (94,12,25,25,8). -/
import Balanced242T94Data

namespace Balanced242T94L12_base
open Balanced242Farkas Balanced242T94Data

theorem splits_eq : genSplits excl6MaskT94 eBoundsT94 94 12 25 25 = splits_94_12_25_25 := by
  decide +kernel

theorem mask_eq : buildAllowedMask 12 25 25 splits_94_12_25_25 = mask_94_12_25_25 := by
  decide +kernel

theorem final_ok : checkAffineCert 12 25 25 (peelSplits splits_94_12_25_25 layer0_94_12_25_25) final_94_12_25_25 = true := by
  decide +kernel

end Balanced242T94L12_base
