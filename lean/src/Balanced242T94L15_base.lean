/- Kernel-checked splits, allowed-half bitmask, and post-peeling final Krawtchouk Farkas cert for (94,15,24,22,8). -/
import Balanced242T94Data

namespace Balanced242T94L15_base
open Balanced242Farkas Balanced242T94Data

theorem splits_eq : genSplits excl6MaskT94 eBoundsT94 94 15 24 22 = splits_94_15_24_22 := by
  decide +kernel

theorem mask_eq : buildAllowedMask 15 24 22 splits_94_15_24_22 = mask_94_15_24_22 := by
  decide +kernel

theorem final_ok : checkAffineCert 15 24 22 (peelSplits splits_94_15_24_22 layer0_94_15_24_22) final_94_15_24_22 = true := by
  decide +kernel

end Balanced242T94L15_base
