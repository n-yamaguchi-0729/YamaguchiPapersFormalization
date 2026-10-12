/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.OverDVR
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Etale.Basic

/-!
# Unramified normalization and the ramification of places

The valuation ring of an extending place is the localization of the actual integral
closure at its centre. If that integral closure is etale over the base valuation ring,
the inclusion of valuation rings is unramified. Its image of a uniformizer generates
the maximal ideal, so the ramification index is one.
-/

noncomputable section

open AlgebraicCurve IsLocalRing IsDedekindDomain

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- An unramified, essentially finite type inclusion of valuation rings has
ramification index one, measured in the original field extension. -/
theorem ramificationIndex_eq_one_of_unramified_restrictInclusion
    {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsIntegral F E] (w : Place K E) :
    let _ := (w.restrictInclusion F).toAlgebra
    Algebra.EssFiniteType (w.restrict F).toValuationSubring w.toValuationSubring →
    Algebra.FormallyUnramified (w.restrict F).toValuationSubring w.toValuationSubring →
    w.ramificationIndex F = 1 := by
  intro valuationAlgebra finiteType unramified
  have localMap : IsLocalHom
      (algebraMap (w.restrict F).toValuationSubring w.toValuationSubring) :=
    show IsLocalHom (w.restrictInclusion F) from inferInstance
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible
    (w.restrict F).toValuationSubring
  have imageNeZero : w.restrictInclusion F t ≠ 0 := by
    intro h
    have hc := congrArg Subtype.val h
    rw [Place.coe_restrictInclusion] at hc
    exact ht.ne_zero (Subtype.ext ((map_eq_zero (algebraMap F E)).mp hc))
  have imageIdeal : Ideal.span {w.restrictInclusion F t} =
      maximalIdeal w.toValuationSubring := by
    have h := Algebra.FormallyUnramified.map_maximalIdeal
      (R := (w.restrict F).toValuationSubring) (S := w.toValuationSubring)
    rw [ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at h
    exact h
  have imageIrreducible : Irreducible (w.restrictInclusion F t) :=
    Ideal.irreducible_of_isMaximal_span_singleton imageNeZero
      (imageIdeal ▸ maximalIdeal.isMaximal w.toValuationSubring)
  have imageOrder := w.ord_coe_irreducible imageIrreducible
  rw [Place.coe_restrictInclusion, w.ord_restrict,
    (w.restrict F).ord_coe_irreducible ht, mul_one] at imageOrder
  exact_mod_cast imageOrder

/-- Etaleness of the actual integral closure over a base place forces every
extending place to have ramification index one. -/
theorem ramificationIndex_eq_one_of_etale_integralClosure
    {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (w : Place K E)
    (hEtale : Algebra.Etale (w.restrict F).toValuationSubring
      (Place.integralClosureAt E (w.restrict F))) :
    w.ramificationIndex F = 1 := by
  let v := w.restrict F
  let C := Place.integralClosureAt E v
  let P := Place.fiberCenter E v (w := w) rfl
  let S := HeightOneSpectrum.valuationSubringAtPrime E P
  let sourceAlgebra : Algebra v.toValuationSubring S :=
    ((algebraMap C S).comp (algebraMap v.toValuationSubring C)).toAlgebra
  have sourceTower : IsScalarTower v.toValuationSubring C S :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have finiteTypeCS : Algebra.EssFiniteType C S :=
    Algebra.EssFiniteType.of_isLocalization S P.asIdeal.primeCompl
  have unramifiedCS : Algebra.FormallyUnramified C S :=
    Algebra.FormallyUnramified.of_isLocalization P.asIdeal.primeCompl
  have etaleC : Algebra.Etale v.toValuationSubring C := hEtale
  have finiteTypeS : Algebra.EssFiniteType v.toValuationSubring S :=
    Algebra.EssFiniteType.comp v.toValuationSubring C S
  have unramifiedS : Algebra.FormallyUnramified v.toValuationSubring S :=
    Algebra.FormallyUnramified.comp v.toValuationSubring C S
  let valuationAlgebra := (w.restrictInclusion F).toAlgebra
  have hring : w.toValuationSubring.toSubring = S.toSubring :=
    congrArg ValuationSubring.toSubring
      (Place.toValuationSubring_eq_of_restrict_eq (w := w) (v := v) rfl)
  let e : w.toValuationSubring ≃ₐ[v.toValuationSubring] S :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr hring) fun _ => Subtype.ext rfl
  have finiteTypeW : Algebra.EssFiniteType v.toValuationSubring w.toValuationSubring :=
    Algebra.EssFiniteType.of_surjective e.symm.toAlgHom e.symm.surjective
  have unramifiedW : Algebra.FormallyUnramified v.toValuationSubring w.toValuationSubring :=
    Algebra.FormallyUnramified.of_equiv e.symm
  exact ramificationIndex_eq_one_of_unramified_restrictInclusion w finiteTypeW unramifiedW

end AnabelianGeometry.GeometricFundamentalGroup
