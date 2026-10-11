/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_eq_mul_and_eq_add_ord_of_presentations.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Models.Places
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_forall_eq_mul_of_presentations
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt
import Nyll.AlgebraicCurves.Models.Exists_closedPoint_range_stalk_eq
import Nyll.AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint
import Nyll.AlgebraicCurves.Places.Exists_place_range_stalk_eq
import Nyll.AlgebraicCurves.Models.Eq_of_range_stalk_eq
import Nyll.AlgebraicCurves.Geometry.Schemes.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Nyll.AlgebraicCurves.Models.IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Nyll.AlgebraicCurves.FunctionFields.EssFiniteType_functionField
import Nyll.AlgebraicCurves.FunctionFields.ConstantsAreBase_of_deg_eq_one
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.StichtenothGenusExists_of_isCurveOver

/-!
# Divisors of equivalent function-field presentations

The rational function relating two function-field presentations of a module on a
smooth proper curve also relates their representing divisors by its orders at the places.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_eq_mul_and_eq_add_ord_of_presentations
open
  _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp]
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq
attribute [-simp]
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec
  AlgebraicCurve.PoleDivisorPackage.mk.injEq

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace PresUniq
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry
open AlgebraicCurve TopologicalSpace WithZero

theorem exists_not_mem_placesOf {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec
    (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (U : X.Opens) (hU : IsAffineOpen
        U) [hUne : Nonempty U] :
    letI := (baseToFunctionField x).toAlgebra
    ∃ v₀ : Place K X.functionField, v₀ ∉ placesOf x U := by
  let := (baseToFunctionField x).toAlgebra
  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one x
  have hne : U ≠ ⊤ := by
    intro h
    apply hNA
    have hT : IsAffineOpen (⊤ : X.Opens) := h ▸ hU
    have : IsAffine (⊤ : X.Opens) := hT
    exact IsAffine.of_isIso X.topIso.inv
  obtain ⟨y, hy⟩ : ∃ y : X, y ∉ U := by
    by_contra hall
    exact hne (eq_top_iff.mpr fun z _ => by_contra fun hz => hall ⟨z, hz⟩)
  have hUne' : ((U : Set X)).Nonempty := let ⟨⟨z, hz⟩⟩ := hUne; ⟨z, hz⟩
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hUne')
  have hyη : y ≠ genericPoint X := fun h => hy (h ▸ hη)
  obtain ⟨v₀, hv₀⟩ := exists_place_range_stalk_eq x y (isClosed_singleton_of_ne_genericPoint x y
      hyη)
  refine ⟨v₀, ?_⟩
  rintro ⟨y', hy'U, -, hv₀'⟩
  have : y' = y := eq_of_range_stalk_eq x y' y (hv₀'.trans hv₀.symm)
  exact hy (this ▸ hy'U)

theorem exp_eq_mul_exp_of_forall_mem_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (S : Set (Place K F)) (D D' : Divisor K F) (g : F)
    (hiff : ∀ f : F, f ∈ lSpaceOn S D' ↔ ∃ f₀ ∈ lSpaceOn S D, f = g * f₀)
    (v : Place K F) (hv : v ∈ S)
    (hatt : ∃ f : F, f ∈ lSpaceOn S D ∧ v.adicValuation f = exp (D v))
    (hatt' : ∃ f : F, f ∈ lSpaceOn S D' ∧ v.adicValuation f = exp (D' v)) :
    exp (D' v) = v.adicValuation g * exp (D v) := by
  apply le_antisymm
  · obtain ⟨f', hf', hval'⟩ := hatt'
    obtain ⟨f₀, hf₀, rfl⟩ := (hiff f').mp hf'
    rw [← hval', Valuation.map_mul]
    exact mul_le_mul_right (hf₀ v hv) _
  · obtain ⟨f, hf, hval⟩ := hatt
    have hgf : g * f ∈ lSpaceOn S D' := (hiff (g * f)).mpr ⟨f, hf, rfl⟩
    have := hgf v hv
    rwa [Valuation.map_mul, hval] at this

end AlgebraicGeometry.Scheme.Modules.PresUniq

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
end AlgebraicGeometry.Scheme.Modules
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.Modules in
open AlgebraicGeometry.Scheme.Modules.PresUniq AlgebraicCurve in
theorem AlgebraicGeometry.Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations'
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (M : X.Modules)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set
            X.functionField))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set
            X.functionField))
    (hsec : ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ g : X.functionField, g ≠ 0 ∧
      (∀ (U : X.Opens) [Nonempty U] (m : Γ(M, U)), φ' U m = g * φ U m) ∧
      (∀ v : AlgebraicCurve.Place K X.functionField, D v = D' v + v.ord g) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D - D') := by
  let := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  have hcurve : IsCurveOver K X.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one x (RingEquiv.refl _) (fun _ => rfl)
  have : Algebra.EssFiniteType K X.functionField := essFiniteType_functionField x
  obtain ⟨g, hg, hmul⟩ :=
    Scheme.Modules.exists_forall_eq_mul_of_presentations M φ φ' hnat hnat' hsmul hsmul' hinj
        hinj' hsec
  have hord : ∀ v : Place K X.functionField, D v = D' v + v.ord g := by
    intro v
    obtain ⟨y, hy, hvy⟩ := exists_closedPoint_range_stalk_eq x v
    obtain ⟨U, hUaff, hyU, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (Opens.mem_top y)
    have : Nonempty U := ⟨⟨y, hyU⟩⟩
    have hvS : v ∈ placesOf x U := ⟨y, hyU, hy, hvy⟩
    obtain ⟨v₀, hv₀⟩ := exists_not_mem_placesOf x U hUaff
    have : Nonempty (Place K X.functionField) := ⟨v⟩
    have hC : ConstantsAreBase K X.functionField :=
      constantsAreBase_of_deg_eq_one v (IsCurveOver.deg_eq_one_of_isAlgClosed v)
    obtain ⟨-, hL0, γ, D₀, hγ⟩ := stichtenothGenusExists_of_isCurveOver hC
    have := hL0
    have hiff : ∀ f : X.functionField,
        f ∈ lSpaceOn (placesOf x U) D' ↔ ∃ f₀ ∈ lSpaceOn (placesOf x U) D, f = g * f₀ := by
      intro f
      have hD : ∀ f₀, f₀ ∈ lSpaceOn (placesOf x U) D ↔ f₀ ∈ Set.range (φ U) := fun f₀ => by
        rw [hrange U hUaff inferInstance]; rfl
      have hD' : f ∈ lSpaceOn (placesOf x U) D' ↔ f ∈ Set.range (φ' U) := by
        rw [hrange' U hUaff inferInstance]; rfl
      rw [hD']
      constructor
      · rintro ⟨m, rfl⟩
        exact ⟨φ U m, (hD _).mpr ⟨m, rfl⟩, hmul U m⟩
      · rintro ⟨f₀, hf₀, rfl⟩
        obtain ⟨m, rfl⟩ := (hD f₀).mp hf₀
        exact ⟨m, hmul U m⟩
    have key := exp_eq_mul_exp_of_forall_mem_iff (placesOf x U) D D' g hiff v hvS
      (exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt hγ (placesOf x U) hv₀ D v hvS)
      (exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt hγ (placesOf x U) hv₀ D' v hvS)
    rw [Place.adicValuation_eq_exp_neg_ord v hg, ← WithZero.exp_add] at key
    have := WithZero.exp_injective key
    omega
  refine ⟨g, hg, hmul, hord, g, hg, fun v => ?_⟩
  rw [Finsupp.sub_apply, hord v]
  ring

open AlgebraicGeometry.Scheme.Modules.PresUniq AlgebraicCurve in
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (M : X.Modules)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set
            X.functionField))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set
            X.functionField))
    (hsec : ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ g : X.functionField, g ≠ 0 ∧
      (∀ (U : X.Opens) [Nonempty U] (m : Γ(M, U)), φ' U m = g * φ U m) ∧
      (∀ v : AlgebraicCurve.Place K X.functionField, D v = D' v + v.ord g) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D - D') :=
  AlgebraicGeometry.Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations' x M D D' φ φ'
      hnat hnat' hsmul hsmul'
    hinj hinj' hrange hrange' hsec
end Scheme_Modules_exists_eq_mul_and_eq_add_ord_of_presentations
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

open
  _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp]
  AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp]
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec
  AlgebraicCurve.PoleDivisorPackage.mk.injEq
