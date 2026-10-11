/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.LocalGeometry.HeightOne.ComponentFunctionField
import Nyll.SchemeTheory.LocalGeometry.HeightOne.Localization

/-!
# Geometric integrality under height-one localization

Localization at a containing prime does not change the residue field of a
branch, so geometric integrality transports canonically to the localized
branch used in a height-two chart.
-/

noncomputable section

open AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

/-- Geometric integrality of a prime residue field persists after extending
the prime to a localization at a containing prime. -/
theorem geometricallyIntegral_localizationAtPrimeMapResidueField
    {k A : Type u} [Field k] [CommRing A]
    (P q : Ideal A) [P.IsPrime] [q.IsPrime] (hqP : q ≤ P)
    [Algebra k q.ResidueField]
    (hgeo : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap k q.ResidueField)))) :
    let qV := q.map (algebraMap A (Localization.AtPrime P))
    letI : qV.IsPrime :=
      Ideal.isPrime_map_of_isLocalizationAtPrime P hqP
    let e := localizationAtPrimeMapResidueFieldRingEquiv A P q hqP
    letI : Algebra k qV.ResidueField :=
      (e.toRingHom.comp (algebraMap k q.ResidueField)).toAlgebra
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap k qV.ResidueField))) := by
  exact geometricallyIntegral_specMap_transport_ringEquiv'
    (localizationAtPrimeMapResidueFieldRingEquiv A P q hqP) hgeo

end EtaleFundamentalGroups

end
