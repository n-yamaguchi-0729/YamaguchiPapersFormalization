/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.NormalizationRamification
import Nyll.EtaleFundamentalGroups.FiniteEtale.StalkFunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BaseRingEquiv
import Nyll.EtaleFundamentalGroups.Normalization.Localization.Basic

/-!
# Ramification above an etale affine normalization

A place whose valuation ring contains a Dedekind affine coordinate ring has an actual
centre in that affine chart. Localizing the normalization at this centre identifies its
base with the valuation ring, so etaleness on the chart implies ramification index one.
-/

noncomputable section

open AlgebraicCurve IsDedekindDomain EtaleFundamentalGroups

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u

/-- An etale affine normalization is unramified at every place centred on the chart.
The valuation-ring comparison is constructed from the centre, not assumed. -/
theorem ramificationIndex_eq_one_of_etale_affine_normalization
    {K R F E : Type u} [Field K] [CommRing R] [IsDedekindDomain R]
    [Field F] [Field E] [Algebra K F] [Algebra K E]
    [Algebra R F] [IsFractionRing R F] [Algebra F E]
    [Algebra R E] [IsScalarTower R F E] [IsScalarTower K F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (hEtale : Algebra.Etale R (integralClosure R E))
    (w : Place K E)
    (hcentre : ∀ r : R, algebraMap R F r ∈ (w.restrict F).toValuationSubring) :
    w.ramificationIndex F = 1 := by
  let v := w.restrict F
  let P := Place.centerHeightOneSpectrum R v hcentre
  let S := HeightOneSpectrum.valuationSubringAtPrime F P
  let valuationAlgebra : Algebra R v.toValuationSubring :=
    ((algebraMap R F).codRestrict v.toValuationSubring.toSubring hcentre).toAlgebra
  have valuationTower : IsScalarTower R v.toValuationSubring E :=
    IsScalarTower.of_algebraMap_eq fun r => by
      exact IsScalarTower.algebraMap_apply R F E r
  have hring : v.toValuationSubring.toSubring = S.toSubring :=
    congrArg ValuationSubring.toSubring (Place.toValuationSubring_eq_of_forall_mem v hcentre)
  let eS : S ≃ₐ[R] v.toValuationSubring :=
    AlgEquiv.ofRingEquiv (f := (RingEquiv.subringCongr hring).symm)
      fun _ => Subtype.ext rfl
  have valuationLocalization : IsLocalization P.asIdeal.primeCompl v.toValuationSubring :=
    IsLocalization.isLocalization_of_algEquiv P.asIdeal.primeCompl eS
  let e := IsLocalization.algEquiv P.asIdeal.primeCompl
    v.toValuationSubring (Localization.AtPrime P.asIdeal)
  let localAlgebra := localizationAtPrimeToExtensionAlgebra (K := F) (L := E) P.asIdeal
  have localTower : IsScalarTower R (Localization.AtPrime P.asIdeal) E :=
    localizationAtPrimeToExtension_isScalarTower (K := F) (L := E) P.asIdeal
  have hmap : (algebraMap (Localization.AtPrime P.asIdeal) E).comp e.toRingHom =
      algebraMap v.toValuationSubring E := by
    apply IsLocalization.ringHom_ext P.asIdeal.primeCompl
    ext r
    change algebraMap (Localization.AtPrime P.asIdeal) E
      (e (algebraMap R v.toValuationSubring r)) =
        algebraMap v.toValuationSubring E (algebraMap R v.toValuationSubring r)
    rw [e.commutes, ← IsScalarTower.algebraMap_apply R (Localization.AtPrime P.asIdeal) E,
      ← IsScalarTower.algebraMap_apply R v.toValuationSubring E]
  have localEtale : Algebra.Etale (Localization.AtPrime P.asIdeal)
      (integralClosure (Localization.AtPrime P.asIdeal) E) :=
    integralClosure_localizationAtPrime_etale_of_etale (K := F) hEtale P.asIdeal
  have valuationEtale : Algebra.Etale v.toValuationSubring
      (integralClosure v.toValuationSubring E) :=
    integralClosure_etale_of_baseRingEquiv e.toRingEquiv hmap localEtale
  exact ramificationIndex_eq_one_of_etale_integralClosure w valuationEtale

end AnabelianGeometry.GeometricFundamentalGroup
