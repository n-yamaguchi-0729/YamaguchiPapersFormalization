/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FiniteEtale.Away.AlgEquivTransport

/-!
# Transporting normalization boundary-away maps across field equivalences

When a map in a scalar tower of fields is bijective, it gives an algebra
equivalence of the ambient fields.  Mapping integral closures along that
equivalence transports the literal boundary-away etaleness statement.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uL uP

/-- A source-produced bijective field map transports the primitive
boundary-away map between the corresponding integral closures. -/
theorem integralClosure_boundaryAway_of_bijective_fieldTower_algebraMap
    {A : Type uA} {L : Type uL} {P : Type uP}
    [CommRing A] [Field L] [Field P]
    [Algebra A L] [Algebra A P]
    [Algebra L P] [IsScalarTower A L P]
    (hbij : Function.Bijective (algebraMap L P))
    (f : A)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A L)) f).Etale) :
    (Localization.awayMap
      (algebraMap A (integralClosure A P)) f).Etale := by
  let fieldEquiv : L ≃ₐ[A] P :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom A L P) hbij
  let normalizationEquiv : integralClosure A L ≃ₐ[A]
      integralClosure A P := fieldEquiv.mapIntegralClosure
  exact localization_awayMap_etale_of_algEquiv
    normalizationEquiv f hAway

end EtaleFundamentalGroups
