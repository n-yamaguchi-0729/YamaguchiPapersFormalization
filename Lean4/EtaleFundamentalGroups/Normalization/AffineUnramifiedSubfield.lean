/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
import EtaleFundamentalGroups.Normalization.FieldSourceNormalization
import EtaleFundamentalGroups.Inertia.NormalizationSourceIso
import EtaleFundamentalGroups.Normalization.GenericFiber
import EtaleFundamentalGroups.Normalization.UnramifiedNormalBase
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.Galois.Infinite

/-!
# The original maximal unramified subextension over a normal domain

The field is defined as the supremum of the finite subfields of the supplied
ambient field whose literal integral closures over A are unramified. The
geometric criterion then proves that this is the field fixed by the actual
fundamental-group kernel, and that its elements form the literal union.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale
open scoped nonZeroDivisors

namespace EtaleFundamentalGroups

universe u v w

/-- The maximal subextension unramified over A, using finite subfields of
the original supplied ambient field and their actual integral closures. -/
def maximalUnramifiedSubfield
    (A : Type u) (K : Type v) (Ω : Type w) [CommRing A] [Field K] [Field Ω]
    [Algebra A K] [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] :
    IntermediateField K Ω :=
  ⨆ (E : IntermediateField K Ω) (_ : FiniteDimensional K E)
    (_ : Algebra.FormallyUnramified A (integralClosure A E) ∧
      Algebra.FiniteType A (integralClosure A E)), E

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

private local instance fractionSourcePreimmersion
    (A F : Type u) [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] :
    IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap A F))) :=
  IsPreimmersion.of_isLocalization A⁰

private local instance fractionSourceDominant
    (A F : Type u) [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A F))) := by
  rw [isDominant_iff]
  change DenseRange (PrimeSpectrum.comap (algebraMap A F))
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A F)]
  exact bot_le

variable (A F Ω : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field F] [Field Ω] [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [Algebra A Ω] [IsScalarTower A F Ω]
  [IsSepClosure F Ω] [IsSepClosed Ω]

/-- The normalization of a literal finite subfield is étale exactly when
the actual generic fundamental-group kernel fixes that subfield. -/
theorem integralClosure_etale_iff_fieldSourceKernel_le_fixingSubgroup
    (E : IntermediateField F Ω) [FiniteDimensional F E] :
    Algebra.Etale A (integralClosure A E) ↔
      (fieldSourceAbsoluteGaloisHom F Ω
        (Spec.map (CommRingCat.ofHom (algebraMap A F)))).toMonoidHom.ker ≤
          E.fixingSubgroup := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap A F))
  constructor
  · intro hEtale
    let : Algebra.Etale A (integralClosure A E) := hEtale
    let : Module.Finite A (integralClosure A E) := Algebra.IsIntegral.finite
    let g := Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A E)))
    have : IsFiniteEtale g :=
      IsFiniteEtale.SpecMap_iff.mpr (RingHom.finiteEtale_algebraMap_iff.mpr ⟨⟩)
    apply (fieldSourceKernel_le_fixingSubgroup_iff_exists_finiteEtale_genericFiber
      F Ω j E).mpr
    refine ⟨Spec (.of (integralClosure A E)), g, inferInstance, inferInstance,
      (isPullback_spec_integralClosure_generic A F E).isoPullback.symm, ?_⟩
    exact (isPullback_spec_integralClosure_generic A F E).isoPullback_inv_snd
  · intro hfix
    obtain ⟨Y, f, hf, he, e, hs⟩ :=
      (fieldSourceKernel_le_fixingSubgroup_iff_exists_finiteEtale_genericFiber
        F Ω j E).mp hfix
    let : IsFinite f := hf
    let : Etale f := he
    let p := e.inv ≫ pullback.fst f j
    have H : IsPullback p (Spec.map (CommRingCat.ofHom (algebraMap F E))) f j := by
      refine (IsPullback.of_hasPullback f j).of_iso
        e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      · simp only [Iso.refl_hom, Category.comp_id, p, Iso.hom_inv_id_assoc]
      · simpa only [Iso.refl_hom, Category.comp_id] using hs.symm
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    have hnorm := etale_fieldSourceNormalization_of_finiteEtale_genericFiber F E j f p H
    have hcomp : Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ j =
        Spec.map (CommRingCat.ofHom (algebraMap A E)) := by
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext
        (IsScalarTower.algebraMap_eq A F E).symm)
    let c := Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ j
    let n := Spec.map (CommRingCat.ofHom (algebraMap A E))
    have hi : (Iso.refl (Spec (.of E))).hom ≫ c = n :=
      (Category.id_comp c).trans hcomp
    let eNorm := Inertia.normalizationSourceIso n c (Iso.refl _) hi
    have hnorm' : Etale n.fromNormalization := by
      have : Etale c.fromNormalization := hnorm
      have hbase : eNorm.hom ≫ c.fromNormalization = n.fromNormalization :=
        Inertia.normalizationSourceIso_hom_fromNormalization n c (Iso.refl _) hi
      rw [← hbase]
      infer_instance
    let g := Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A E)))
    have hg : Etale g := by
      have : Etale (Spec.map (CommRingCat.ofHom (algebraMap A E))).fromNormalization :=
        hnorm'
      have hb : (specNormalizationIso A E).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap A E))).fromNormalization = g := by
        rw [← specNormalizationIso_hom_base A E]
        exact (specNormalizationIso A E).inv_hom_id_assoc g
      rw [← hb]
      infer_instance
    exact RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hg)

/-- Unramifiedness uses the literal integral closure, with no finiteness of
normalization assumed: finite type and formal unramifiedness imply étaleness. -/
theorem integralClosure_unramified_iff_fieldSourceKernel_le_fixingSubgroup
    (E : IntermediateField F Ω) [FiniteDimensional F E] :
    (Algebra.FormallyUnramified A (integralClosure A E) ∧
      Algebra.FiniteType A (integralClosure A E)) ↔
      (fieldSourceAbsoluteGaloisHom F Ω
        (Spec.map (CommRingCat.ofHom (algebraMap A F)))).toMonoidHom.ker ≤
          E.fixingSubgroup := by
  rw [← integralClosure_etale_iff_fieldSourceKernel_le_fixingSubgroup A F Ω E]
  constructor
  · rintro ⟨hUnramified, hFiniteType⟩
    let : Algebra.FormallyUnramified A (integralClosure A E) := hUnramified
    let : Algebra.FiniteType A (integralClosure A E) := hFiniteType
    have hAE : Function.Injective (algebraMap A E) := by
      rw [IsScalarTower.algebraMap_eq A F E]
      exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
    let : FaithfulSMul A (integralClosure A E) :=
      (faithfulSMul_iff_algebraMap_injective A (integralClosure A E)).mpr (by
        intro a b hab
        apply hAE
        exact congrArg (fun z : integralClosure A E => (z : E)) hab)
    exact etale_of_unramified_of_domain_of_faithful
  · intro hEtale
    let : Algebra.Etale A (integralClosure A E) := hEtale
    exact ⟨inferInstance, inferInstance⟩

/-- The fixed field of the actual generic kernel is the literal union of
finite subextensions unramified over A in the given ambient field. -/
theorem mem_fieldSourceKernelFixedField_iff_exists_unramified_finite_subfield
    (x : Ω) :
    x ∈ IntermediateField.fixedField
      (fieldSourceAbsoluteGaloisHom F Ω
        (Spec.map (CommRingCat.ofHom (algebraMap A F)))).toMonoidHom.ker ↔
      ∃ E : IntermediateField F Ω, FiniteDimensional F E ∧
        (Algebra.FormallyUnramified A (integralClosure A E) ∧
          Algebra.FiniteType A (integralClosure A E)) ∧ x ∈ E := by
  constructor
  · intro hx
    let E := IntermediateField.adjoin F ({x} : Set Ω)
    let : FiniteDimensional F E :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have hE : E ≤ IntermediateField.fixedField
        (fieldSourceAbsoluteGaloisHom F Ω
          (Spec.map (CommRingCat.ofHom (algebraMap A F)))).toMonoidHom.ker :=
      IntermediateField.adjoin_simple_le_iff.mpr hx
    have hfix := (IntermediateField.le_iff_le _ E).mp hE
    exact ⟨E, inferInstance,
      (integralClosure_unramified_iff_fieldSourceKernel_le_fixingSubgroup A F Ω E).mpr hfix,
      IntermediateField.subset_adjoin F {x} (Set.mem_singleton x)⟩
  · rintro ⟨E, hfinite, hunram, hx⟩
    let : FiniteDimensional F E := hfinite
    have hfix :=
      (integralClosure_unramified_iff_fieldSourceKernel_le_fixingSubgroup A F Ω E).mp hunram
    exact ((IntermediateField.le_iff_le _ E).mpr hfix) hx

/-- The independently defined maximal unramified subfield equals the fixed
field of the actual fundamental-group kernel. -/
theorem maximalUnramifiedSubfield_eq_fieldSourceKernelFixedField :
    maximalUnramifiedSubfield A F Ω = IntermediateField.fixedField
      (fieldSourceAbsoluteGaloisHom F Ω
        (Spec.map (CommRingCat.ofHom (algebraMap A F)))).toMonoidHom.ker := by
  apply le_antisymm
  · apply iSup_le
    intro E
    apply iSup_le
    intro hfinite
    apply iSup_le
    intro hunram x hx
    exact (mem_fieldSourceKernelFixedField_iff_exists_unramified_finite_subfield
      A F Ω x).mpr ⟨E, hfinite, hunram, hx⟩
  · intro x hx
    obtain ⟨E, hfinite, hunram, hxE⟩ :=
      (mem_fieldSourceKernelFixedField_iff_exists_unramified_finite_subfield
        A F Ω x).mp hx
    have hE : E ≤ maximalUnramifiedSubfield A F Ω :=
      le_iSup_of_le E (le_iSup_of_le hfinite (le_iSup_of_le hunram le_rfl))
    exact hE hxE

end EtaleFundamentalGroups
