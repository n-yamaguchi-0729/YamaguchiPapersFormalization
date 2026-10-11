/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.AbelianModPower

/-!
# Compatibility names for abelianization modulo powers

The general construction lives in `ProCGroups.Abelian.AbelianModPower`.
These aliases preserve names exposed by the earlier paper-specific module.
-/

namespace Yamaguchi26AbfaithfulGalois

export ProCGroups.Abelian
  (abelianModPower abelianModPowerMap abelianModPowerMap_mk
    abelianModPowerLift abelianModPowerLift_mk abelianModPowerLift_surjective)

end Yamaguchi26AbfaithfulGalois
