/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.PointedQuotientTransport
import EtaleFundamentalGroups.Inertia.DivisorialStrictHenselian

/-!
# Transport of pointed local finite-cover quotients

The finite monodromy obtained from a scheme morphism is natural when the
composite geometric fiber is transported to another chosen base point.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- Restriction along a scheme morphism and transport of the pointed fiber
commute at the level of the resulting finite monodromy homomorphism. -/
theorem finiteEtaleGaloisCoverQuotientOfMorphism_transport
    {T U : Scheme.{u}} [ConnectedSpace U]
    {Omega Omega' : Type u}
    [Field Omega] [IsSepClosed Omega]
    [Field Omega'] [IsSepClosed Omega']
    (j : T ⟶ U) (xi : Spec (.of Omega) ⟶ T)
    (xi' : Spec (.of Omega') ⟶ U)
    (p : AlgebraicGeometry.FiniteEtale.fiber (xi ≫ j) ≅
      AlgebraicGeometry.FiniteEtale.fiber xi')
    (Y : AlgebraicGeometry.FiniteEtale U) (hY : IsGalois Y)
    (y : (AlgebraicGeometry.FiniteEtale.fiber xi').obj Y) :
    letI : IsGalois Y := hY
    Inertia.finiteEtaleGaloisCoverQuotientOfMorphism
        j xi Y hY (p.inv.app Y y) =
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi' Y hY y).comp
        (p.conjAut.toMonoidHom.comp
          (AlgebraicGeometry.FiniteEtale.fundamentalGroupHom j xi).toMonoidHom) := by
  let : IsGalois Y := hY
  change
    (finiteEtaleGaloisCoverQuotientMonoidHom
      (xi ≫ j) Y hY (p.inv.app Y y)).comp
        (AlgebraicGeometry.FiniteEtale.fundamentalGroupHom j xi).toMonoidHom = _
  exact galoisObjectQuotientMonoidHom_transport_comp
    (AlgebraicGeometry.FiniteEtale.fiber (xi ≫ j))
    (AlgebraicGeometry.FiniteEtale.fiber xi') p Y y
    (AlgebraicGeometry.FiniteEtale.fundamentalGroupHom j xi).toMonoidHom

end EtaleFundamentalGroups

end
