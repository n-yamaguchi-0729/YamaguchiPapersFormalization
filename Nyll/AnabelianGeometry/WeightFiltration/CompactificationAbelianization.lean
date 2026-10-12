/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationKernel

/-!
# The actual compactification map on abelianized fundamental groups

Restriction of finite étale covers defines the map. For a normal locally
Noetherian integral compactification, this map is surjective; its kernel is
the image of the kernel before abelianization. Identifying this kernel with
the boundary Tate module is a further geometric calculation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

variable {X U : Scheme} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j]
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ U)

/-- The map induced by the actual open immersion and actual fiber functor. -/
def compactificationAbelianizationMap :
    TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ*
      TopologicalAbelianization (Aut (FiniteEtale.fiber (ξ ≫ j))) :=
  TopologicalAbelianization.map (FiniteEtale.fundamentalGroupHom j ξ)

omit [IsIntegral X] [IsIntegral U] [IsOpenImmersion j] [IsSepClosed Ω] in
/-- The map on abelianizations retains the original fundamental-group map. -/
theorem compactificationAbelianizationMap_mk (g : Aut (FiniteEtale.fiber ξ)) :
    compactificationAbelianizationMap j ξ
      (TopologicalAbelianization.mk _ g) =
        TopologicalAbelianization.mk _ (FiniteEtale.fundamentalGroupHom j ξ g) := rfl

variable [IsNormalIntegral X] [IsLocallyNoetherian X]

/-- Every abelianized proper-curve class lifts to the open curve. -/
theorem compactificationAbelianizationMap_surjective :
    Function.Surjective (compactificationAbelianizationMap j ξ) :=
  TopologicalAbelianization.surjective_map_of_surjective
    (FiniteEtale.fundamentalGroupHom j ξ)
    (FiniteEtale.fundamentalGroupHom_surjective_of_isOpenImmersion j ξ)

/-- The boundary kernel after abelianization is exactly the image of the
actual compactification kernel, rather than an additional chosen subgroup. -/
theorem compactificationAbelianizationMap_ker :
    (compactificationAbelianizationMap j ξ).toMonoidHom.ker =
      (FiniteEtale.fundamentalGroupHom j ξ).toMonoidHom.ker.map
        (TopologicalAbelianization.mk (Aut (FiniteEtale.fiber ξ))) :=
  TopologicalAbelianization.ker_map_of_surjective
    (FiniteEtale.fundamentalGroupHom j ξ)
    (FiniteEtale.fundamentalGroupHom_surjective_of_isOpenImmersion j ξ)

end AnabelianGeometry.WeightFiltration
