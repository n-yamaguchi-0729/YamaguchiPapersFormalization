/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.GenericPointFixedSubfield
import EtaleFundamentalGroups.GeometricFiber.GenericPointGaloisQuotient
import EtaleFundamentalGroups.Normalization.FiniteEtaleGenericFiber
import EtaleFundamentalGroups.Normalization.GenericExtensionFiber
import EtaleFundamentalGroups.Normalization.UnramifiedNormalization

/-!
# Unramified subfields and the generic Galois kernel

The generic-fibre comparison identifies the finite subfields coming from
unramified normalization with the fields fixed by the generic Galois kernel.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups

universe u

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

/-- The generic Galois kernel fixes a finite subfield whose normalization
is étale. Integrality of normalization supplies the finite cover. -/
theorem genericKernel_le_fixingSubgroup_of_etale_normalization
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L]
    (h : Etale (X.genericExtensionMorphism L).fromNormalization) :
    (genericAbsoluteGaloisHom X).toMonoidHom.ker ≤ L.fixingSubgroup := by
  let f := X.genericExtensionMorphism L
  have hfinite : IsFinite f.fromNormalization :=
    ((unramified_normalization_iff_etale_iff_finiteEtale X L).2.mp h).1
  apply (genericKernel_le_fixingSubgroup_iff_exists_finiteEtale_genericFiber X L).mpr
  refine ⟨f.normalization, f.fromNormalization, hfinite, h,
    (genericExtensionNormalizationFiberIso X L).symm, ?_⟩
  exact (isPullback_genericExtensionNormalization X L).isoPullback_inv_snd

/-- A finite subfield has étale normalization exactly when it is fixed by
the kernel of the generic absolute Galois map. -/
theorem etale_normalization_iff_genericKernel_le_fixingSubgroup
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L] :
    Etale (X.genericExtensionMorphism L).fromNormalization ↔
      (genericAbsoluteGaloisHom X).toMonoidHom.ker ≤ L.fixingSubgroup := by
  refine ⟨genericKernel_le_fixingSubgroup_of_etale_normalization X L, ?_⟩
  intro h
  obtain ⟨Y, f, hf, he, e, hs⟩ :=
    (genericKernel_le_fixingSubgroup_iff_exists_finiteEtale_genericFiber X L).mp h
  let : IsFinite f := hf
  let : Etale f := he
  let p := e.inv ≫ pullback.fst f (X.fromSpecStalk (genericPoint X))
  have H : IsPullback p (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)))
      f (X.fromSpecStalk (genericPoint X)) := by
    refine (IsPullback.of_hasPullback f (X.fromSpecStalk (genericPoint X))).of_iso
      e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.refl_hom, Category.comp_id, p, Iso.hom_inv_id_assoc]
    · simpa only [Iso.refl_hom, Category.comp_id] using hs.symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  exact etale_genericExtensionNormalization_of_finiteEtale_genericFiber L f p H

/-- The field fixed by the generic kernel is the actual union of the
finite subextensions unramified in `X`. -/
theorem mem_genericKernelFixedField_iff_exists_unramified_finite_subfield
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (x : SeparableClosure X.functionField) :
    x ∈ genericKernelFixedField X ↔
      ∃ L : IntermediateField X.functionField (SeparableClosure X.functionField),
        FiniteDimensional X.functionField L ∧
        (FormallyUnramified (X.genericExtensionMorphism L).fromNormalization ∧
          LocallyOfFiniteType (X.genericExtensionMorphism L).fromNormalization) ∧ x ∈ L := by
  constructor
  · intro hx
    let L := IntermediateField.adjoin X.functionField ({x} : Set (SeparableClosure X.functionField))
    let : FiniteDimensional X.functionField L :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have hL : L ≤ genericKernelFixedField X :=
      IntermediateField.adjoin_simple_le_iff.mpr hx
    have hfix : (genericAbsoluteGaloisHom X).toMonoidHom.ker ≤ L.fixingSubgroup :=
      (IntermediateField.le_iff_le _ L).mp hL
    have he := (etale_normalization_iff_genericKernel_le_fixingSubgroup X L).mpr hfix
    exact ⟨L, inferInstance,
      (unramified_normalization_iff_etale_iff_finiteEtale X L).1.mpr he,
      IntermediateField.subset_adjoin X.functionField {x} (Set.mem_singleton x)⟩
  · rintro ⟨L, hfinite, hunram, hx⟩
    let : FiniteDimensional X.functionField L := hfinite
    have he := (unramified_normalization_iff_etale_iff_finiteEtale X L).1.mp hunram
    have hfix := (etale_normalization_iff_genericKernel_le_fixingSubgroup X L).mp he
    exact ((IntermediateField.le_iff_le _ L).mpr hfix) hx

/-- The maximal unramified extension, written as a supremum of the
original finite unramified subextensions, is the generic kernel's fixed field. -/
theorem genericKernelFixedField_eq_iSup_unramified
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X] :
    genericKernelFixedField X =
      ⨆ (L : IntermediateField X.functionField (SeparableClosure X.functionField))
        (_ : FiniteDimensional X.functionField L)
        (_ : FormallyUnramified (X.genericExtensionMorphism L).fromNormalization ∧
          LocallyOfFiniteType (X.genericExtensionMorphism L).fromNormalization), L := by
  apply le_antisymm
  · intro x hx
    obtain ⟨L, hfinite, hunram, hxL⟩ :=
      (mem_genericKernelFixedField_iff_exists_unramified_finite_subfield X x).mp hx
    have hL : L ≤
        ⨆ (M : IntermediateField X.functionField (SeparableClosure X.functionField))
          (_ : FiniteDimensional X.functionField M)
          (_ : FormallyUnramified (X.genericExtensionMorphism M).fromNormalization ∧
            LocallyOfFiniteType (X.genericExtensionMorphism M).fromNormalization), M :=
      le_iSup_of_le L (le_iSup_of_le hfinite (le_iSup_of_le hunram le_rfl))
    exact hL hxL
  · apply iSup_le
    intro L
    apply iSup_le
    intro hfinite
    apply iSup_le
    intro hunram x hx
    exact (mem_genericKernelFixedField_iff_exists_unramified_finite_subfield X x).mpr
      ⟨L, hfinite, hunram, hx⟩

end EtaleFundamentalGroups
