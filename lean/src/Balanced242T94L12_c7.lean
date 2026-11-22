/- Kernel-checked anchor-pair chunk 7 for (94,12,25,25,8). -/
import Balanced242T94Data
import Balanced242FastCond

namespace Balanced242T94L12_c7
open Balanced242FastCond Balanced242T94Data

theorem chunk_ok : checkLayerFast2 12 25 25 mask_94_12_25_25 layer0_94_12_25_25_c7 = true := by
  decide +kernel

end Balanced242T94L12_c7
