/- Kernel-checked anchor-pair chunk 1 for (94,15,24,22,8). -/
import Balanced242T94Data
import Balanced242FastCond

namespace Balanced242T94L15_c1
open Balanced242FastCond Balanced242T94Data

theorem chunk_ok : checkLayerFast2 15 24 22 mask_94_15_24_22 layer0_94_15_24_22_c1 = true := by
  decide +kernel

end Balanced242T94L15_c1
