/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13Mask17

namespace Erdos539Geometry

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
theorem pg13_mask_batch_18 :
    ∀ i : Fin 128, PG13MaskCertificate (2304 + i.val) := by
  decide +kernel

end Erdos539Geometry
