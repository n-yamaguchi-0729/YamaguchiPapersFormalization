/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NormalizationPointRigidity
import EtaleFundamentalGroups.Normalization.GenericExtensionFiber
import SchemeTheory.Morphisms.ResiduePointFixedness
import SchemeTheory.Normalization.FiniteSeparable
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.FieldTheory.Finiteness

/-!
# Global geometric-point rigidity for an unramified normalization

The normalization endomorphism is the actual extension of the original
field automorphism. If it fixes any field-valued point, unramified point
rigidity makes it the identity. The actual generic-fiber square makes the
map from Spec L into the normalization a monomorphism, so the original
field automorphism itself is the identity.

The final theorem uses canonical residue-point naturality to apply this
rigidity directly to the original fixed-point and trivial-residue-action
condition. It proves the global unramified-to-trivial-inertia implication
in Stacks Project, Tag 0BTF, for the original field automorphism itself.
Galoisness is unnecessary for this forward implication.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups

universe u

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

private theorem fieldAlgEquiv_eq_one_of_specMap_eq_id
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (h : Spec.map (CommRingCat.ofHom σ.toRingHom) = 𝟙 (Spec (.of L))) : σ = 1 := by
  have hring : CommRingCat.ofHom σ.toRingHom = 𝟙 (CommRingCat.of L) := by
    apply Spec.map_injective
    exact h.trans (Spec.map_id (CommRingCat.of L)).symm
  apply AlgEquiv.ext
  intro a
  exact congrArg (fun g : CommRingCat.of L ⟶ CommRingCat.of L => g.hom.toFun a) hring

/-- An original function-field automorphism preserves the actual generic
extension morphism, through its given scalar compatibility. -/
theorem genericExtensionMorphism_specMap_algEquiv
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (σ : L ≃ₐ[X.functionField] L) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ X.genericExtensionMorphism L =
      X.genericExtensionMorphism L := by
  have hcoeff : CommRingCat.ofHom (algebraMap X.functionField L) ≫
      CommRingCat.ofHom σ.toRingHom =
      CommRingCat.ofHom (algebraMap X.functionField L) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact σ.commutes r
  unfold Scheme.genericExtensionMorphism
  rw [← Category.assoc, ← Spec.map_comp, hcoeff]

/-- A field automorphism fixing an actual field-valued point of the
unramified normalization is the identity. Galoisness is unnecessary for
this individual-automorphism statement. -/
theorem genericNormalization_automorphism_eq_one_of_fixed_fieldPoint
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    (hunram : FormallyUnramified (X.genericExtensionMorphism L).fromNormalization ∧
      LocallyOfFiniteType (X.genericExtensionMorphism L).fromNormalization)
    (σ : L ≃ₐ[X.functionField] L) {Ω : Type u} [Field Ω]
    (z : Spec (.of Ω) ⟶ (X.genericExtensionMorphism L).normalization)
    (hz : z ≫ Inertia.normalizationEndomorphism (X.genericExtensionMorphism L)
        (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (genericExtensionMorphism_specMap_algEquiv X L σ) = z) : σ = 1 := by
  let f : Spec (.of L) ⟶ X := X.genericExtensionMorphism L
  have : FormallyUnramified f.fromNormalization := hunram.1
  have : LocallyOfFiniteType f.fromNormalization := hunram.2
  have hidentity : Inertia.normalizationEndomorphism f
      (Spec.map (CommRingCat.ofHom σ.toRingHom))
      (genericExtensionMorphism_specMap_algEquiv X L σ) = 𝟙 f.normalization :=
    Inertia.normalizationEndomorphism_eq_id_of_fixes_nonempty f
      (Spec.map (CommRingCat.ofHom σ.toRingHom))
      (genericExtensionMorphism_specMap_algEquiv X L σ) z hz
  have : Mono f.toNormalization :=
    (isPullback_genericExtensionNormalization X L).mono_fst_of_mono
  apply fieldAlgEquiv_eq_one_of_specMap_eq_id σ
  apply (cancel_mono f.toNormalization).mp
  calc
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ f.toNormalization =
        f.toNormalization ≫ Inertia.normalizationEndomorphism f
          (Spec.map (CommRingCat.ofHom σ.toRingHom))
          (genericExtensionMorphism_specMap_algEquiv X L σ) :=
      (Inertia.toNormalization_normalizationEndomorphism f
        (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (genericExtensionMorphism_specMap_algEquiv X L σ)).symm
    _ = f.toNormalization := by rw [hidentity, Category.comp_id]
    _ = 𝟙 (Spec (.of L)) ≫ f.toNormalization := (Category.id_comp f.toNormalization).symm

/-- The original point-and-residue inertia condition on an unramified
normalization forces the original field automorphism to be the identity.
This proves the forward implication to condition (9) of Tag 0BTF; it also
holds for finite extensions which are not Galois. -/
theorem genericNormalization_automorphism_eq_one_of_trivial_residue
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    (hunram : FormallyUnramified (X.genericExtensionMorphism L).fromNormalization ∧
      LocallyOfFiniteType (X.genericExtensionMorphism L).fromNormalization)
    (σ : L ≃ₐ[X.functionField] L) (y : (X.genericExtensionMorphism L).normalization)
    (hy : Inertia.normalizationEndomorphism (X.genericExtensionMorphism L)
      (Spec.map (CommRingCat.ofHom σ.toRingHom))
      (genericExtensionMorphism_specMap_algEquiv X L σ) y = y)
    (hres : (Inertia.normalizationEndomorphism (X.genericExtensionMorphism L)
        (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (genericExtensionMorphism_specMap_algEquiv X L σ)).residueFieldMap y =
      ((X.genericExtensionMorphism L).normalization.residueFieldCongr hy).hom) :
    σ = 1 := by
  let f : Spec (.of L) ⟶ X := X.genericExtensionMorphism L
  let e : f.normalization ⟶ f.normalization :=
    Inertia.normalizationEndomorphism f (Spec.map (CommRingCat.ofHom σ.toRingHom))
      (genericExtensionMorphism_specMap_algEquiv X L σ)
  have hfixed : f.normalization.fromSpecResidueField y ≫ e =
      f.normalization.fromSpecResidueField y :=
    Scheme.Hom.fixes_fromSpecResidueField_of_residueFieldMap_eq e y hy hres
  exact genericNormalization_automorphism_eq_one_of_fixed_fieldPoint X L hunram σ
    (Ω := f.normalization.residueField y) (f.normalization.fromSpecResidueField y) hfixed

end EtaleFundamentalGroups
