/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.LocalGeometry.HeightOne.RegularLocalDimensionTwoDVR
import EtaleFundamentalGroups.Normalization.Localization.IntegralClosureAtPrimeEquiv
import EtaleFundamentalGroups.Purity.Local.DimensionOne
import EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwo.IntegralClosure.Local

/-!
# Codimension-one unramifiedness and two-dimensional purity

For a normalization over a two-dimensional regular local domain, it is
enough to assume unramifiedness at the maximal ideals above every height-one
prime.  The corresponding localized normalization is finite torsion-free
over a DVR, hence finite etale.  Two-dimensional local purity then removes
the closed point.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

universe u v w

/-- The normalization in a finite separable extension of the fraction field
of a DVR is etale when it is unramified at every maximal ideal. -/
theorem integralClosure_etale_of_dvr_of_isUnramifiedAt_all_maximalIdeals
    {V : Type u} {K : Type v} {L : Type w}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra V L] [Algebra K L] [IsScalarTower V K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hunramified : ∀ (Q : Ideal (integralClosure V L)) [Q.IsMaximal],
      Algebra.IsUnramifiedAt V Q) :
    Algebra.Etale V (integralClosure V L) := by
  let : Module.IsTorsionFree V L :=
    Module.IsTorsionFree.trans_faithfulSMul V K L
  let : Module.Finite V (integralClosure V L) :=
    IsIntegralClosure.finite V K L (integralClosure V L)
  let : Module.IsTorsionFree V (integralClosure V L) :=
    IsIntegralClosure.isTorsionFree V (A := integralClosure V L) L
  exact
    EtaleFundamentalGroups.etale_of_dvr_of_finite_torsionFree_of_isUnramifiedAt_all_maximalIdeals
      hunramified

/-- A normalization over a two-dimensional regular local domain is etale if,
above every height-one prime, its localized normalization is unramified at
all maximal ideals. -/
theorem integralClosure_etale_of_isRegularLocalRing_dimension_two_of_unramifiedAt_height_one
    {A : Type u} {K : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞))
    (hunramified : ∀ (q : Ideal A) [q.IsPrime], q.height = 1 →
      letI := EtaleFundamentalGroups.localizationAtPrimeToExtensionAlgebra
        (K := K) (L := L) q
      ∀ (Q : Ideal (integralClosure (Localization.AtPrime q) L))
        [Q.IsMaximal],
        Algebra.IsUnramifiedAt (Localization.AtPrime q) Q) :
    Algebra.Etale A (integralClosure A L) := by
  apply integralClosure_etale_of_isRegularLocalRing_dimension_two
    (K := K) hdim
  intro q _ hq
  let V := Localization.AtPrime q
  let : Algebra V K :=
    EtaleFundamentalGroups.localizationAtPrimeToFractionFieldAlgebra
      (K := K) q
  let : IsFractionRing V K :=
    EtaleFundamentalGroups.localizationAtPrimeToFractionField_isFractionRing
      (K := K) q
  let : Algebra V L :=
    EtaleFundamentalGroups.localizationAtPrimeToExtensionAlgebra
      (K := K) (L := L) q
  let : IsScalarTower V K L :=
    EtaleFundamentalGroups.localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) q
  have : IsDiscreteValuationRing V :=
    (open _root_.EtaleFundamentalGroups in
      isDiscreteValuationRing_localizationAtPrime_of_isRegularLocalRing_dimension_two
        hdim q hq)
  have hlocal : Algebra.Etale V (integralClosure V L) :=
    integralClosure_etale_of_dvr_of_isUnramifiedAt_all_maximalIdeals
      (V := V) (K := K) (L := L)
      (hunramified q hq)
  exact
    EtaleFundamentalGroups.localization_integralClosure_etale_of_local_integralClosure_etale
      (K := K) (L := L) q hlocal

end EtaleFundamentalGroups.SpecialLocalPurity

end
