/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Tactic.Ext
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOverBaseChange
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.abelianSchemePropertyBundle_fibreStr
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_geometricallyIntegral
import Nyll.AlgebraicCurves.Geometry.Curves.bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
import Nyll.AlgebraicCurves.Geometry.Schemes.comp_section_comp_eq_of_isClosedMap_of_surjective_app
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.SchemeTheory.ProjectiveSpace.Basic

/-!
# Pointed morphisms of abelian schemes preserve multiplication
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one
attribute [-instance] instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper
  AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase
  AlgebraicCurve.CurveModel.isFractionRing_overlap
  AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued
  AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued
  AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued
  AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing
  AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField
  AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU
  AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf
  AlgebraicCurve.CurveModel.isOpenImmersion_ιInf
  AlgebraicCurve.CurveModel.algebra_overlap_functionField
  AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin
  AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure
  AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime
  AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing
  AlgebraicCurve.CurveModel.isNoetherianRing_chartRing
  AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin
attribute [-instance] AlgebraicCurve.CurveModel.chartRing_finitePresentation
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicGeometry.SubalgebraStages.compactSpace_pullback
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback
  AlgebraicGeometry.SubalgebraStages.compactSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiCompact_snd
  AlgebraicGeometry.SubalgebraStages.isAffineHom_leg
  AlgebraicGeometry.SubalgebraStages.isAffineHom_trans
  AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map
  AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd
  AlgebraicGeometry.SubalgebraStages.isCofiltered_op
  IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec
  AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero
  AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add
  AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
  AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.ι₀_gluedToBase
  AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt
attribute [-simp] AlgebraicGeometry.SubalgebraStages.trans_fst
  AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd
  AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl
  AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom
  AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app
  AlgebraicGeometry.SubalgebraStages.specDiagram_map
  AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst
  AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply
  IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply
  IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian
open NeronModelInfra (SchemeHomOver)
open NeronModelInfra (fibreRestrictAlong)

universe u

noncomputable section

namespace H2bHomExt

variable {R : Type u} [CommRing R]
variable {A B : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}

theorem inv_natural (M : RelativeGroupLaw R g) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t
      = t')
    (x : SchemeHomOver t g) :
    schemeHomOverComp ψ hψ (M.inv t x) = M.inv t' (schemeHomOverComp ψ hψ x) := by
  let := M.pointGroup t'
  have h : M.mul t' (schemeHomOverComp ψ hψ (M.inv t x)) (schemeHomOverComp ψ hψ x) = M.one t' := by
    rw [← M.mul_natural t t' ψ hψ, M.inv_mul_cancel, M.one_natural]
  exact eq_inv_of_mul_eq_one_left h

theorem comp_nmComp {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t
      = t')
    (x : SchemeHomOver t f) (φ : SchemeHomOver f g) :
    schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp x φ) =
      NeronModelInfra.schemeHomOverComp (schemeHomOverComp ψ hψ x) φ :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem nmComp_one (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (φ : SchemeHomOver f g)
    (hφ : NeronModelInfra.schemeHomOverComp (L.one (𝟙 (Spec (CommRingCat.of R)))) φ =
      M.one (𝟙 (Spec (CommRingCat.of R))))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (L.one t) φ = M.one t := by
  rw [← L.one_natural (𝟙 _) t t (Category.comp_id t), ← comp_nmComp, hφ, M.one_natural]

/-- The structure morphism of the double fibre product. -/
abbrev tP (f : A ⟶ Spec (CommRingCat.of R)) : pullback f f ⟶ Spec (CommRingCat.of R) :=
  pullback.fst f f ≫ f

/-- The first projection regarded as a point over the product base. -/
def X₁ (f : A ⟶ Spec (CommRingCat.of R)) : SchemeHomOver (tP f) f := ⟨pullback.fst f f, rfl⟩

/-- The second projection regarded as a point over the product base. -/
def X₂ (f : A ⟶ Spec (CommRingCat.of R)) : SchemeHomOver (tP f) f := ⟨pullback.snd f f,
  pullback.condition.symm⟩

/--
The discrepancy between the image of the universal product and the product of the universal
images.
-/
def defect (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (φ : SchemeHomOver f g) :
    SchemeHomOver (tP f) g :=
  M.mul (tP f) (NeronModelInfra.schemeHomOverComp (L.mul (tP f) (X₁ f) (X₂ f)) φ)
    (M.inv (tP f) (M.mul (tP f) (NeronModelInfra.schemeHomOverComp (X₁ f) φ)
      (NeronModelInfra.schemeHomOverComp (X₂ f) φ)))

theorem comp_defect (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (φ : SchemeHomOver f g)
    {T : Scheme.{u}} (ψ : T ⟶ pullback f f) (t : T ⟶ Spec (CommRingCat.of R)) (hψ : ψ ≫ tP f = t) :
    schemeHomOverComp ψ hψ (defect L M φ) =
      M.mul t (NeronModelInfra.schemeHomOverComp
          (L.mul t (schemeHomOverComp ψ hψ (X₁ f)) (schemeHomOverComp ψ hψ (X₂ f))) φ)
        (M.inv t (M.mul t (NeronModelInfra.schemeHomOverComp (schemeHomOverComp ψ hψ (X₁ f)) φ)
          (NeronModelInfra.schemeHomOverComp (schemeHomOverComp ψ hψ (X₂ f)) φ))) := by
  unfold defect
  rw [M.mul_natural, inv_natural, M.mul_natural, comp_nmComp, comp_nmComp, comp_nmComp,
    L.mul_natural]

theorem comp_defect_eq_one (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (φ : SchemeHomOver
  f g)
    {T : Scheme.{u}} (ψ : T ⟶ pullback f f) (t : T ⟶ Spec (CommRingCat.of R)) (hψ : ψ ≫ tP f = t)
    (hhom : NeronModelInfra.schemeHomOverComp
          (L.mul t (schemeHomOverComp ψ hψ (X₁ f)) (schemeHomOverComp ψ hψ (X₂ f))) φ =
        M.mul t (NeronModelInfra.schemeHomOverComp (schemeHomOverComp ψ hψ (X₁ f)) φ)
          (NeronModelInfra.schemeHomOverComp (schemeHomOverComp ψ hψ (X₂ f)) φ)) :
    schemeHomOverComp ψ hψ (defect L M φ) = M.one t := by
  rw [comp_defect, hhom, M.mul_inv_cancel]

theorem one_coe (M : RelativeGroupLaw R g) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (M.one t).1 = t ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := congrArg Subtype.val (M.one_natural (𝟙 _) t t (Category.comp_id t))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  exact h.symm

theorem subsingleton_spec_field (K : Type u) [Field K] :
    Subsingleton ↥(Spec (CommRingCat.of K)) := by
  constructor
  intro p q
  apply PrimeSpectrum.ext
  have hp : p.asIdeal.IsPrime := (show PrimeSpectrum K from p).isPrime
  have hq : q.asIdeal.IsPrime := (show PrimeSpectrum K from q).isPrime
  rw [Ideal.eq_bot_of_prime p.asIdeal, Ideal.eq_bot_of_prime q.asIdeal]

theorem connectedSpace_of_bundle {K : Type u} [Field K] {X : Scheme.{u}}
    {q : X ⟶ Spec (CommRingCat.of K)} (hX : AbelianSchemePropertyBundle K q) : ConnectedSpace ↥X :=
      by
  have := subsingleton_spec_field K
  let p : ↥(Spec (CommRingCat.of K)) := IsLocalRing.closedPoint K
  have hc := hX.connectedFibres p
  have huniv : q.base ⁻¹' {p} = Set.univ := Set.eq_univ_of_forall fun a => Subsingleton.elim _ _
  rw [huniv] at hc
  exact connectedSpace_iff_univ.mpr hc

theorem nmComp_mul_of_fibre (hA : AbelianSchemePropertyBundle R f) (hB :
  AbelianSchemePropertyBundle R g)
    (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (φ : SchemeHomOver f g)
    (hφ : NeronModelInfra.schemeHomOverComp (L.one (𝟙 (Spec (CommRingCat.of R)))) φ =
      M.one (𝟙 (Spec (CommRingCat.of R))))
    (s : ↥(Spec (CommRingCat.of R))) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of (RelativeGroupLaw.baseResidueField s)))
    (x y : SchemeHomOver (t' ≫ RelativeGroupLaw.basePointInclusion s) f) :
    NeronModelInfra.schemeHomOverComp (L.mul _ x y) φ =
      M.mul _ (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) := by
  let ι := RelativeGroupLaw.basePointInclusion s
  have hAs : AbelianSchemePropertyBundle (RelativeGroupLaw.baseResidueField s)
      (RelativeGroupLaw.baseChangeStr ι f) := abelianSchemePropertyBundle_fibreStr hA s
  have hBs : AbelianSchemePropertyBundle (RelativeGroupLaw.baseResidueField s)
      (RelativeGroupLaw.baseChangeStr ι g) := abelianSchemePropertyBundle_fibreStr hB s
  have : IsProper (RelativeGroupLaw.baseChangeStr ι f) := hAs.proper
  have : Smooth (RelativeGroupLaw.baseChangeStr ι f) := hAs.smooth
  have : ConnectedSpace ↥(RelativeGroupLaw.baseChangeScheme ι f) := connectedSpace_of_bundle hAs
  let φs : SchemeHomOver (RelativeGroupLaw.baseChangeStr ι f) (RelativeGroupLaw.baseChangeStr ι g)
    :=
    fibreRestrictAlong ι g f φ
  have hφs : NeronModelInfra.schemeHomOverComp ((L.baseChange ι).one (𝟙 _)) φs = (M.baseChange
    ι).one (𝟙 _) := by
    apply (RelativeGroupLaw.baseChangePointEquiv ι (𝟙 _)).injective
    change RelativeGroupLaw.baseChangePointToBase ι _ = RelativeGroupLaw.baseChangePointToBase ι _
    rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
      RelativeGroupLaw.baseChangePointToBase_one,
      RelativeGroupLaw.baseChangePointToBase_one, nmComp_one L M φ hφ]
  have hfield :=
    RelativeGroupLaw.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
    (RelativeGroupLaw.baseResidueField s) (L.baseChange ι) (M.baseChange ι) hBs φs hφs t'
    (RelativeGroupLaw.baseChangePointOfBase ι x) (RelativeGroupLaw.baseChangePointOfBase ι y)
  have h := congrArg (RelativeGroupLaw.baseChangePointToBase ι) hfield
  rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
    RelativeGroupLaw.baseChangePointToBase_mul,
    RelativeGroupLaw.baseChangePointToBase_mul,
      RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
    RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
      RelativeGroupLaw.baseChangePointToBase_ofBase,
    RelativeGroupLaw.baseChangePointToBase_ofBase] at h
  exact h

theorem geometricallyReduced (hA : AbelianSchemePropertyBundle R f) : GeometricallyReduced f := by
  refine ⟨geometrically_iff_forall_fiberToSpecResidueField.mpr fun y => ?_⟩
  have := (abelianSchemePropertyBundle_fibreStr hA y).geometricallyIntegral
  exact GeometricallyReduced.geometrically_isReduced (f := RelativeGroupLaw.fibreStr f y)

theorem geometricallyConnected (hA : AbelianSchemePropertyBundle R f) : GeometricallyConnected f :=
  by
  refine ⟨geometrically_iff_forall_fiberToSpecResidueField.mpr fun y => ?_⟩
  have := (abelianSchemePropertyBundle_fibreStr hA y).geometricallyIntegral
  intro K _ z Z fst snd h
  have : IrreducibleSpace Z :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := RelativeGroupLaw.fibreStr f y) z
      fst snd h
  infer_instance

theorem main (hA : AbelianSchemePropertyBundle R f) (hB : AbelianSchemePropertyBundle R g)
    (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (φ : SchemeHomOver f g)
    (hφ : NeronModelInfra.schemeHomOverComp (L.one (𝟙 (Spec (CommRingCat.of R)))) φ =
      M.one (𝟙 (Spec (CommRingCat.of R)))) :
    defect L M φ = M.one (tP f) := by
  have heA : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  let ε : A ⟶ pullback f f := pullback.lift (𝟙 A) (f ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
    (by rw [Category.id_comp, Category.assoc, heA, Category.comp_id])
  have hεp : ε ≫ pullback.fst f f = 𝟙 A := pullback.lift_fst _ _ _
  have hεt : ε ≫ tP f = f := by
    change ε ≫ (pullback.fst f f ≫ f) = f
    rw [← Category.assoc, hεp, Category.id_comp]
  have hεX₁ : schemeHomOverComp ε hεt (X₁ f) = NeronModelInfra.schemeHomOverId f :=
    Subtype.ext hεp
  have hεX₂ : schemeHomOverComp ε hεt (X₂ f) = L.one f := by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe, one_coe L f]
    change ε ≫ pullback.snd f f = _
    exact pullback.lift_snd _ _ _
  have hεh : schemeHomOverComp ε hεt (defect L M φ) = M.one f := by
    apply comp_defect_eq_one
    rw [hεX₁, hεX₂, L.mul_one, nmComp_one L M φ hφ, M.mul_one]
  have hεh1 : ε ≫ (defect L M φ).1 = f ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    have h := congrArg Subtype.val hεh
    rw [GoodReductionJacobian.schemeHomOverComp_coe, one_coe M f] at h
    exact h
  have hval : ∀ z : ↥(pullback f f),
      (defect L M φ).1 z = (M.one (𝟙 (Spec (CommRingCat.of R)))).1 (tP f z) := by
    intro z
    let s : ↥(Spec (CommRingCat.of R)) := tP f z
    let zt : Spec ((pullback f f).residueField z) ⟶ pullback f f := (pullback f
      f).fromSpecResidueField z
    let t' : Spec ((pullback f f).residueField z) ⟶ Spec (CommRingCat.of
      (RelativeGroupLaw.baseResidueField s)) :=
      Spec.map ((tP f).residueFieldMap z)
    have hzt : zt ≫ tP f = t' ≫ RelativeGroupLaw.basePointInclusion s :=
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (tP f) z).symm
    have hone : schemeHomOverComp zt hzt (defect L M φ) = M.one _ :=
      comp_defect_eq_one L M φ zt _ hzt
        (nmComp_mul_of_fibre hA hB L M φ hφ s t' (schemeHomOverComp zt hzt (X₁ f))
          (schemeHomOverComp zt hzt (X₂ f)))
    have h1 := congrArg Subtype.val hone
    rw [GoodReductionJacobian.schemeHomOverComp_coe, one_coe M, ← hzt, Category.assoc] at h1
    have h2 := congrArg (fun q : Spec ((pullback f f).residueField z) ⟶ B =>
      q (IsLocalRing.closedPoint ((pullback f f).residueField z))) h1
    change (defect L M φ).1 (zt (IsLocalRing.closedPoint ((pullback f f).residueField z))) =
      (M.one (𝟙 (Spec (CommRingCat.of R)))).1
        (tP f (zt (IsLocalRing.closedPoint ((pullback f f).residueField z)))) at h2
    have hz : zt (IsLocalRing.closedPoint ((pullback f f).residueField z)) = z :=
      Scheme.fromSpecResidueField_apply z (IsLocalRing.closedPoint ((pullback f f).residueField z))
    exact (congrArg (fun a : ↥(pullback f f) => (defect L M φ).1 a) hz).symm.trans
      (h2.trans (congrArg (fun a : ↥(pullback f f) =>
        (M.one (𝟙 (Spec (CommRingCat.of R)))).1 (tP f a)) hz))
  have hconst : ∀ z : ↥(pullback f f), (defect L M φ).1 (ε (pullback.fst f f z)) = (defect L M φ).1
    z := by
    intro z
    rw [hval z, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hεh1]
    change (pullback.fst f f ≫ f ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1) z =
      (M.one (𝟙 (Spec (CommRingCat.of R)))).1 ((pullback.fst f f ≫ f) z)
    simp only [Scheme.Hom.comp_apply]
  have := hA.proper
  have := hA.smooth
  have := geometricallyReduced hA
  have := geometricallyConnected hA
  have hH0 : ∀ U : A.Opens, IsAffineOpen U → Function.Surjective ((pullback.fst f f).app U) := fun
    U _ =>
    (bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
      (pullback.fst f f) U).2
  have hrig := comp_section_comp_eq_of_isClosedMap_of_surjective_app (pullback.fst f f) ε hεp
    (pullback.fst f f).isClosedMap hH0 (defect L M φ).1 hconst
  apply Subtype.ext
  rw [← hrig, hεh1, one_coe M (tP f), Category.assoc]

end H2bHomExt

end

end AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs

namespace GoodReductionJacobian.AbelianSchemePropertyBundle

universe u

open _root_.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs in
open AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian in
open NeronModelInfra (SchemeHomOver) in
open NeronModelInfra (fibreRestrictAlong) in
open H2bHomExt in
theorem schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one
    {R : Type u} [CommRing R] {A B : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec
      (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (hB : AbelianSchemePropertyBundle R g)
    (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (φ : SchemeHomOver f g)
    (hφ : NeronModelInfra.schemeHomOverComp (L.one (𝟙 (Spec (CommRingCat.of R)))) φ = M.one (𝟙
      (Spec (CommRingCat.of R)))) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        M.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) :=
          by
  intro T t x y
  let ψ : T ⟶ pullback f f := pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  have hψ : ψ ≫ tP f = t := by
    change ψ ≫ (pullback.fst f f ≫ f) = t
    rw [← Category.assoc, pullback.lift_fst, x.2]
  have hX₁ : schemeHomOverComp ψ hψ (X₁ f) = x := Subtype.ext (pullback.lift_fst _ _ _)
  have hX₂ : schemeHomOverComp ψ hψ (X₂ f) = y := Subtype.ext (pullback.lift_snd _ _ _)
  have h := congrArg (schemeHomOverComp ψ hψ) (main hA hB L M φ hφ)
  rw [comp_defect, M.one_natural, hX₁, hX₂] at h
  let := M.pointGroup t
  exact mul_inv_eq_one.mp h
end GoodReductionJacobian.AbelianSchemePropertyBundle
end ProofImplementation

attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  GoodReductionJacobian.RelativeGroupLaw.nsmul_zero
  GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset
  GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.fibreRestrictAlong_coe_comp_snd
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq
  AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single
  AlgebraicCurve.Place.smul_toValuationSubring
attribute [-simp] AlgebraicCurve.Place.heightOneSpectrum_asIdeal
  AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one
  AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom
  AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
  AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.ι₀_gluedToBase
  AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt
  AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj
  AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map
  AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd
  AlgebraicGeometry.SubalgebraStages.specTrans_specHom
attribute [-simp] AlgebraicGeometry.SubalgebraStages.specCone_pt
  AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map
  AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst
  AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply
  IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply
  IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply
attribute [local instance] MvPolynomial.gradedAlgebra
