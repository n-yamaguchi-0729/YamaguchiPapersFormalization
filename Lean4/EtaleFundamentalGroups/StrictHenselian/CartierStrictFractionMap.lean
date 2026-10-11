/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import EtaleFundamentalGroups.StrictHenselian.CartierGenericPoint
import EtaleFundamentalGroups.Inertia.CartierLocalFractionField


/-!
# The strict generic Cartier map through the actual fraction-field map
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- The actual strict generic Cartier morphism factors through the actual
local fraction field using the induced field map over a normal domain stalk. -/
theorem geometricStalkFractionFieldMap_comp_fractionStalkToSupportComplement
    {X : Scheme.{u}} (D : X.EffectiveCartierDivisor) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (φ : X.presheaf.stalk x →+* Ω) [IsLocalHom φ] :
    Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)) ≫
        D.2.fractionStalkToSupportComplement x =
      geometricStalkFractionFieldToComplement D x φ := by
  apply (cancel_mono D.1.supportComplement.ι).mp
  rw [Category.assoc, D.2.fractionStalkToSupportComplement_comp_ι,
    geometricStalkFractionFieldToComplement_comp_ι, ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact geometricStalkFractionFieldMap_algebraMap φ a

end EtaleFundamentalGroups.StrictHenselian
