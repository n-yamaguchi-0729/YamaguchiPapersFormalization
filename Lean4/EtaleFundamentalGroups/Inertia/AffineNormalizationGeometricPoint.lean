/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AffineGeometricPoint
import SchemeTheory.Normalization.Affine
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Geometric-point inertia in an affine relative normalization

For an `R`-algebra `B`, an automorphism of `B` extends to the relative
normalization of `Spec B → Spec R` by `normalizationDesc`.  Under the canonical
identification with `Spec (integralClosure R B)`, this extension is exactly the
spectrum of the restricted algebra automorphism.  This compatibility is proved
from the integral-closure inclusion; it is not an additional hypothesis.

Consequently, the stabilizer of an actual geometric point of the normalization
is the ideal-inertia subgroup for the restricted action on the integral closure.
For a point obtained from the algebraic closure of the residue field of `P`,
the ideal is literally `P`.  No integrality, normality, finiteness, or Galois
assumption on `R` or `B` is required for this affine comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- Restrict algebra automorphisms to the actual integral closure. -/
def integralClosureAutHom :
    (B ≃ₐ[R] B) →* (integralClosure R B ≃ₐ[R] integralClosure R B) where
  toFun σ := σ.mapIntegralClosure
  map_one' := by
    apply AlgEquiv.ext
    intro b
    apply Subtype.ext
    rfl
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro b
    apply Subtype.ext
    rfl

/-- The restriction action of `Aut_R(B)` on the integral closure of `R` in `B`.
It is kept explicit, so it does not introduce a competing global instance. -/
abbrev integralClosureAutAction :
    MulSemiringAction (B ≃ₐ[R] B) (integralClosure R B) :=
  MulSemiringAction.compHom (integralClosure R B) (integralClosureAutHom R B)

/-- Extend an actual algebra automorphism by the universal property of relative
normalization, using the same `normalizationDesc` construction as for deck maps. -/
def affineNormalizationDeck (σ : B ≃ₐ[R] B) :
    (Spec.map (CommRingCat.ofHom (algebraMap R B))).normalization ⟶
      (Spec.map (CommRingCat.ofHom (algebraMap R B))).normalization :=
  (Spec.map (CommRingCat.ofHom (algebraMap R B))).normalizationDesc
    (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R B))).toNormalization)
    (Spec.map (CommRingCat.ofHom (algebraMap R B))).fromNormalization (by
      rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization,
        ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      exact (σ.commutes r).symm)

/-- The canonical affine normalization isomorphism intertwines the extension
by `normalizationDesc` with the literal restricted ring automorphism. -/
@[reassoc]
theorem affineNormalizationDeck_specNormalizationIso_hom
    (σ : B ≃ₐ[R] B) :
    affineNormalizationDeck R B σ ≫ (specNormalizationIso R B).hom =
      (specNormalizationIso R B).hom ≫
        Spec.map (CommRingCat.ofHom σ.toAlgHom.mapIntegralClosure.toRingHom) := by
  apply spec_toNormalization_hom_ext R B
  calc
    (Spec.map (CommRingCat.ofHom (algebraMap R B))).toNormalization ≫
        (affineNormalizationDeck R B σ ≫ (specNormalizationIso R B).hom) =
      (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R B))).toNormalization) ≫
          (specNormalizationIso R B).hom := by
      rw [← Category.assoc, affineNormalizationDeck,
        Scheme.Hom.toNormalization_normalizationDesc]
    _ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom) := by
      rw [Category.assoc, toNormalization_specNormalizationIso_hom]
    _ = Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom σ.toAlgHom.mapIntegralClosure.toRingHom) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
    _ = (Spec.map (CommRingCat.ofHom (algebraMap R B))).toNormalization ≫
        ((specNormalizationIso R B).hom ≫
          Spec.map (CommRingCat.ofHom σ.toAlgHom.mapIntegralClosure.toRingHom)) := by
      rw [← Category.assoc, toNormalization_specNormalizationIso_hom]

/-- An algebra automorphism belongs to ideal inertia exactly when its actual
normalization extension fixes the corresponding geometric point. -/
theorem mem_idealInertia_iff_fixes_affineNormalizationGeometricPoint
    {Ω : Type u} [Field Ω]
    (φ : integralClosure R B →+* Ω) (σ : B ≃ₐ[R] B) :
    letI : MulSemiringAction (B ≃ₐ[R] B) (integralClosure R B) :=
      integralClosureAutAction R B
    σ ∈ (RingHom.ker φ).inertia (B ≃ₐ[R] B) ↔
      (Spec.map (CommRingCat.ofHom φ) ≫ (specNormalizationIso R B).inv) ≫
          affineNormalizationDeck R B σ =
        Spec.map (CommRingCat.ofHom φ) ≫ (specNormalizationIso R B).inv := by
  let : MulSemiringAction (B ≃ₐ[R] B) (integralClosure R B) :=
    integralClosureAutAction R B
  have haction : MulSemiringAction.toRingHom (B ≃ₐ[R] B)
      (integralClosure R B) σ = σ.toAlgHom.mapIntegralClosure.toRingHom := by
    apply RingHom.ext
    intro b
    rfl
  have hfix :
      ((Spec.map (CommRingCat.ofHom φ) ≫ (specNormalizationIso R B).inv) ≫
          affineNormalizationDeck R B σ =
        Spec.map (CommRingCat.ofHom φ) ≫ (specNormalizationIso R B).inv) ↔
      Spec.map (CommRingCat.ofHom φ) ≫
          Spec.map (CommRingCat.ofHom σ.toAlgHom.mapIntegralClosure.toRingHom) =
        Spec.map (CommRingCat.ofHom φ) := by
    rw [← cancel_mono (specNormalizationIso R B).hom]
    simp only [Category.assoc, affineNormalizationDeck_specNormalizationIso_hom,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hmem := mem_idealInertia_iff_fixes_affineGeometricPoint
    (B ≃ₐ[R] B) φ σ
  rw [haction] at hmem
  exact hmem.trans hfix.symm

/-- The stabilizer uses equality of geometric-point morphisms into the relative
normalization, rather than equality of their underlying topological points. -/
def affineNormalizationGeometricPointStabilizer
    {Ω : Type u} [Field Ω] (φ : integralClosure R B →+* Ω) :
    Subgroup (B ≃ₐ[R] B) := by
  letI : MulSemiringAction (B ≃ₐ[R] B) (integralClosure R B) :=
    integralClosureAutAction R B
  refine
    { carrier := {σ | (Spec.map (CommRingCat.ofHom φ) ≫
          (specNormalizationIso R B).inv) ≫ affineNormalizationDeck R B σ =
        Spec.map (CommRingCat.ofHom φ) ≫ (specNormalizationIso R B).inv}
      one_mem' := ?_
      mul_mem' := ?_
      inv_mem' := ?_ }
  · intro σ τ hσ hτ
    exact (mem_idealInertia_iff_fixes_affineNormalizationGeometricPoint
      R B φ (σ * τ)).mp (Subgroup.mul_mem _
        ((mem_idealInertia_iff_fixes_affineNormalizationGeometricPoint R B φ σ).mpr hσ)
        ((mem_idealInertia_iff_fixes_affineNormalizationGeometricPoint R B φ τ).mpr hτ))
  · exact (mem_idealInertia_iff_fixes_affineNormalizationGeometricPoint
      R B φ 1).mp (Subgroup.one_mem _)
  · intro σ hσ
    exact (mem_idealInertia_iff_fixes_affineNormalizationGeometricPoint
      R B φ σ⁻¹).mp (Subgroup.inv_mem _
        ((mem_idealInertia_iff_fixes_affineNormalizationGeometricPoint R B φ σ).mpr hσ))

/-- The actual normalization geometric-point stabilizer is the ideal-inertia
subgroup for the integral-closure restriction action. -/
theorem affineNormalizationGeometricPointStabilizer_eq_idealInertia
    {Ω : Type u} [Field Ω] (φ : integralClosure R B →+* Ω) :
    letI : MulSemiringAction (B ≃ₐ[R] B) (integralClosure R B) :=
      integralClosureAutAction R B
    affineNormalizationGeometricPointStabilizer R B φ =
      (RingHom.ker φ).inertia (B ≃ₐ[R] B) := by
  let : MulSemiringAction (B ≃ₐ[R] B) (integralClosure R B) :=
    integralClosureAutAction R B
  ext σ
  exact (mem_idealInertia_iff_fixes_affineNormalizationGeometricPoint R B φ σ).symm

/-- For the canonical geometric point obtained from a prime's residue field,
the stabilizer ideal is the given prime itself. -/
theorem affineNormalizationResidueGeometricPointStabilizer_eq_idealInertia
    (P : Ideal (integralClosure R B)) [P.IsPrime] :
    letI : MulSemiringAction (B ≃ₐ[R] B) (integralClosure R B) :=
      integralClosureAutAction R B
    affineNormalizationGeometricPointStabilizer R B
        ((algebraMap P.ResidueField (AlgebraicClosure P.ResidueField)).comp
          (algebraMap (integralClosure R B) P.ResidueField)) =
      P.inertia (B ≃ₐ[R] B) := by
  let : MulSemiringAction (B ≃ₐ[R] B) (integralClosure R B) :=
    integralClosureAutAction R B
  rw [affineNormalizationGeometricPointStabilizer_eq_idealInertia,
    RingHom.ker_comp_of_injective (algebraMap (integralClosure R B) P.ResidueField)
      (algebraMap P.ResidueField (AlgebraicClosure P.ResidueField)).injective,
    Ideal.ker_algebraMap_residueField]

end EtaleFundamentalGroups.Inertia
