/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.PullbackComponentFunctionField
import Nyll.EtaleFundamentalGroups.GaloisCovers.SupportComplementFunctionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.FunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeNormalCrossingsComplementCover
import Nyll.SchemeTheory.FunctionFields.StalkFactorization
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Function-field compatibility for local etale charts

This file records the canonical maps from an ambient stalk through a
prime-localized etale chart and its boundary-away function field.  In
particular, the compatibility needed for finite-etale pullback components
is produced by the chart itself, rather than supplied as a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X Y : Scheme.{u}}

local instance (y : Y) (P : Spec (Y.presheaf.stalk y)) :
    P.asIdeal.IsPrime := P.isPrime

private theorem functionFieldMap_eq_of_eq
    {T R : Scheme.{u}} [IsIntegral T] [IsIntegral R]
    (a b : R ⟶ T) (hab : a = b)
    (ha : DenseRange a) (hb : DenseRange b) :
    a.functionFieldMap ha = b.functionFieldMap hb := by
  subst b
  rfl

/-- The canonical algebra structure from an ambient stalk to a
prime-localized stalk on an etale chart. -/
@[reducible]
noncomputable def etaleChartLocalizationAlgebra
    (f : Y ⟶ X) (y : Y) (P : Spec (Y.presheaf.stalk y)) :
    Algebra (X.presheaf.stalk (f y))
      (Localization.AtPrime P.asIdeal) :=
  (((algebraMap (Y.presheaf.stalk y)
    (Localization.AtPrime P.asIdeal)).comp (f.stalkMap y).hom)).toAlgebra

/-- Flatness of an etale chart makes the canonical ambient-stalk map into
a domain prime localization injective. -/
theorem etaleChartLocalization_algebraMap_injective
    [IsIntegral X] (f : Y ⟶ X) [Etale f] (y : Y)
    (P : Spec (Y.presheaf.stalk y))
    (_hVdomain : IsDomain (Localization.AtPrime P.asIdeal)) :
    Function.Injective
      ((algebraMap (Y.presheaf.stalk y)
        (Localization.AtPrime P.asIdeal)).comp
          (f.stalkMap y).hom) := by
  let A := X.presheaf.stalk (f y)
  let B := Y.presheaf.stalk y
  let V := Localization.AtPrime P.asIdeal
  let : IsDomain V := _hVdomain
  let : Algebra A V := etaleChartLocalizationAlgebra f y P
  let : Module.Flat A V := by
    rw [← RingHom.flat_algebraMap_iff]
    exact RingHom.Flat.comp (Flat.stalkMap f y)
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  change Function.Injective (algebraMap A V)
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hregular : IsRegular a := by
    exact isRegular_iff_ne_zero.mpr ha0
  have hsmul : IsSMulRegular V a :=
    Module.Flat.isSMulRegular_of_isRegular hregular
  have hone : (1 : V) = 0 := by
    apply hsmul
    change algebraMap A V a * 1 = algebraMap A V a * 0
    rw [ha]
    simp
  exact one_ne_zero hone

/-- After returning to the ambient scheme, the boundary-away chart map is
the spectrum map of the canonical composite out of the ambient stalk. -/
theorem boundaryAwayToSupportComplement_comp_ι_eq_specMap_fromSpecStalk
    (I : X.IdealSheafData) (f : Y ⟶ X) (y : Y)
    (P : Spec (Y.presheaf.stalk y)) {r : ℕ}
    (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hboundary :
      ((I.comap f).stalkIdeal y).map
          (algebraMap (Y.presheaf.stalk y)
            (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r}) :
    boundaryAwayToSupportComplement I f y P t hboundary ≫
        I.supportComplement.ι =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (Localization.AtPrime P.asIdeal)
          (Localization.Away (boundaryProduct t r))).comp
        ((algebraMap (Y.presheaf.stalk y)
          (Localization.AtPrime P.asIdeal)).comp
            (f.stalkMap y).hom))) ≫
        X.fromSpecStalk (f y) := by
  dsimp only [boundaryAwayToSupportComplement]
  rw [Category.assoc, comapSupportComplementTo_comp_ι]
  rw [← Category.assoc,
    localizationAwayToSupportComplement_comp_ι]
  rw [Scheme.localizationAtPrimeTo]
  rw [Category.assoc, Category.assoc]
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk f (x := y)]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  rfl

/-- The boundary-away map of an etale chart has dense image in the
ambient support complement. -/
theorem boundaryAwayToSupportComplement_denseRange
    [IsIntegral X]
    (I : X.IdealSheafData) (f : Y ⟶ X) [Etale f] (y : Y)
    (P : Spec (Y.presheaf.stalk y)) {r : ℕ}
    (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hf : boundaryProduct t r ≠ 0)
    (hboundary :
      ((I.comap f).stalkIdeal y).map
          (algebraMap (Y.presheaf.stalk y)
            (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r})
    (hVdomain : IsDomain (Localization.AtPrime P.asIdeal)) :
    DenseRange
      (boundaryAwayToSupportComplement I f y P t hboundary) := by
  let A := X.presheaf.stalk (f y)
  let B := Y.presheaf.stalk y
  let V := Localization.AtPrime P.asIdeal
  let b := boundaryProduct t r
  let S := Localization.Away b
  let : IsDomain V := hVdomain
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  let c := boundaryAwayToSupportComplement I f y P t hboundary
  let phi : A →+* S :=
    (algebraMap V S).comp
      ((algebraMap B V).comp (f.stalkMap y).hom)
  have hAV : Function.Injective
      ((algebraMap B V).comp (f.stalkMap y).hom) := by
    exact etaleChartLocalization_algebraMap_injective f y P hVdomain
  have hVS : Function.Injective (algebraMap V S) :=
    IsLocalization.injective (M := Submonoid.powers b) S
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
  have hphi : Function.Injective phi := hVS.comp hAV
  have hcanonical :
      c ≫ I.supportComplement.ι =
        Spec.map (CommRingCat.ofHom phi) ≫ X.fromSpecStalk (f y) := by
    exact boundaryAwayToSupportComplement_comp_ι_eq_specMap_fromSpecStalk
      I f y P t hboundary
  have hambient : DenseRange (c ≫ I.supportComplement.ι) := by
    rw [hcanonical]
    exact Scheme.Hom.denseRange_specMap_comp_fromSpecStalk_of_injective
      (f y) phi hphi
  let : IsDominant (c ≫ I.supportComplement.ι) := ⟨hambient⟩
  let : IsDominant c :=
    IsDominant.of_comp_of_isOpenImmersion c I.supportComplement.ι
  exact c.denseRange

/-- The two canonical maps from the ambient stalk to the boundary-away
function field agree: one passes through the support-complement function
field, and the other passes through the etale chart stalk and its two
localizations. -/
theorem boundaryAway_functionFieldMap_comp_ambientStalk
    [IsIntegral X] (I : X.IdealSheafData) [Nonempty I.supportComplement]
    (f : Y ⟶ X) [Etale f] (y : Y)
    (P : Spec (Y.presheaf.stalk y)) {r : ℕ}
    (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hf : boundaryProduct t r ≠ 0)
    (hboundary :
      ((I.comap f).stalkIdeal y).map
          (algebraMap (Y.presheaf.stalk y)
            (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r})
    [IsDomain (Localization.AtPrime P.asIdeal)]
    [IsDomain (Localization.Away (boundaryProduct t r))] :
    let c := boundaryAwayToSupportComplement I f y P t hboundary
    let hc : DenseRange c :=
      boundaryAwayToSupportComplement_denseRange
        I f y P t hf hboundary inferInstance
    (c.functionFieldMap hc).comp
        ((Scheme.Hom.functionFieldRingEquivOfIsOpenImmersion
          I.supportComplement.ι).toRingHom.comp
            (algebraMap (X.presheaf.stalk (f y)) X.functionField)) =
      (StructureSheaf.toStalk
        (CommRingCat.of (Localization.Away (boundaryProduct t r)))
        (genericPoint (Spec (.of (Localization.Away
          (boundaryProduct t r)))))).hom.comp
        ((algebraMap (Localization.AtPrime P.asIdeal)
          (Localization.Away (boundaryProduct t r))).comp
        ((algebraMap (Y.presheaf.stalk y)
          (Localization.AtPrime P.asIdeal)).comp
            (f.stalkMap y).hom)) := by
  dsimp only
  let A := X.presheaf.stalk (f y)
  let B := Y.presheaf.stalk y
  let V := Localization.AtPrime P.asIdeal
  let b := boundaryProduct t r
  let S := Localization.Away b
  let : Algebra S (Spec (.of S)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of S)
  let c := boundaryAwayToSupportComplement I f y P t hboundary
  let j := I.supportComplement.ι
  let phi : A →+* S :=
    (algebraMap V S).comp
      ((algebraMap B V).comp (f.stalkMap y).hom)
  have hAV : Function.Injective
      ((algebraMap B V).comp (f.stalkMap y).hom) := by
    exact etaleChartLocalization_algebraMap_injective
      f y P (inferInstance : IsDomain V)
  have hVS : Function.Injective (algebraMap V S) :=
    IsLocalization.injective (M := Submonoid.powers b) S
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
  have hphi : Function.Injective phi := hVS.comp hAV
  let g : Spec (.of S) ⟶ X :=
    Spec.map (CommRingCat.ofHom phi) ≫ X.fromSpecStalk (f y)
  let hg : DenseRange g :=
    Scheme.Hom.denseRange_specMap_comp_fromSpecStalk_of_injective
      (f y) phi hphi
  have hc : DenseRange c :=
    boundaryAwayToSupportComplement_denseRange
      I f y P t hf hboundary inferInstance
  have hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  have hcj : DenseRange (c ≫ j) := by
    change DenseRange (j.base ∘ c.base)
    exact hj.comp hc j.continuous
  have hcanonical : c ≫ j = g := by
    exact boundaryAwayToSupportComplement_comp_ι_eq_specMap_fromSpecStalk
      I f y P t hboundary
  have hfield : (c ≫ j).functionFieldMap hcj =
      g.functionFieldMap hg :=
    functionFieldMap_eq_of_eq (c ≫ j) g hcanonical hcj hg
  calc
    (c.functionFieldMap hc).comp
        ((j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).comp
          (algebraMap A X.functionField)) =
      ((c.functionFieldMap hc).comp (j.functionFieldMap hj)).comp
        (algebraMap A X.functionField) := by
          rw [RingHom.comp_assoc]
          rfl
    _ = ((c ≫ j).functionFieldMap hcj).comp
        (algebraMap A X.functionField) := by
          rw [Scheme.Hom.functionFieldMap_comp_of_denseRange j hj c hc]
    _ = (g.functionFieldMap hg).comp
        (algebraMap A X.functionField) := by rw [hfield]
    _ = (algebraMap S (Spec (.of S)).functionField).comp phi :=
      Scheme.Hom.functionFieldMap_comp_stalkFunctionField_of_injective
        (f y) phi hphi

end AlgebraicGeometry.Scheme.IdealSheafData

end
