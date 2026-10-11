/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26SolvableCoverings.Geometry.Boundary

/-!
# Definition 2.2: the boundary condition

For a horizontal effective Cartier divisor `D` on a connected locally Noetherian
scheme `X`, condition `(†)` consists of regularity along the support, a normal
crossings point of residue characteristic two on every component, and geometrically
integral generic fibers of every reduced boundary component after every connected
finite etale cover of `X`.

The definition quantifies over all connected finite etale covers, including those
which are not Galois. Connectedness, local Noetherianity, and horizontality are supplied
by the statements using the condition.

Source: `SolvableCoverings.tex`, `def:boundary-condition`.
-/

open AlgebraicGeometry

namespace Yamaguchi26SolvableCoverings

/-- Definition 2.2 (`def:boundary-condition`): 支持上の正則性、各成分の標数 `2`
の normal-crossings 点、および全連結有限 étale 被覆後の一般成分の幾何的整性。 -/
def BoundaryCondition {X : Scheme.{0}} (D : X.EffectiveCartierDivisor) : Prop :=
  D.IsAmbientRegularAlongSupport ∧
    D.HasNormalCrossingPointOfResidueCharacteristicOnEachComponent 2 ∧
      HasGeometricallyIntegralGenericComponentsAfterCovers D

end Yamaguchi26SolvableCoverings
