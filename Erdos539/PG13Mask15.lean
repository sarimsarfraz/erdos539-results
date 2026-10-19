/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13Mask14

namespace Erdos539Geometry

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
theorem pg13_mask_batch_15 :
    ∀ i : Fin 128, PG13MaskCertificate (1920 + i.val) := by
  decide +kernel

end Erdos539Geometry
