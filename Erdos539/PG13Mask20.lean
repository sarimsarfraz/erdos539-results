/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13Mask19

namespace Erdos539Geometry

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
theorem pg13_mask_batch_20 :
    ∀ i : Fin 128, PG13MaskCertificate (2560 + i.val) := by
  decide +kernel

end Erdos539Geometry
