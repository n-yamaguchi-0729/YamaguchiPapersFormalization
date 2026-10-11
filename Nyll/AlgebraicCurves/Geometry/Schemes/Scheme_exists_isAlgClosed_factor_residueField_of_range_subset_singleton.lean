/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isAlgClosed_factor_residueField_of_range_subset_singleton.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Scheme exists is Alg Closed factor residue Field of range subset singleton
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_exists_isAlgClosed_factor_residueField_of_range_subset_singleton

universe u

open CategoryTheory AlgebraicGeometry

theorem
  _root_.AlgebraicGeometry.Scheme.exists_isAlgClosed_factor_residueField_of_range_subset_singleton
    {T : Scheme.{u}} (x : T)
    {k₁ : Type u} [Field k₁] (s₁ : Spec (CommRingCat.of k₁) ⟶ T) (hs₁ : Set.range ⇑s₁ ⊆ {x})
    {k₂ : Type u} [Field k₂] (s₂ : Spec (CommRingCat.of k₂) ⟶ T) (hs₂ : Set.range ⇑s₂ ⊆ {x}) :
    ∃ (ι₁ : T.residueField x ⟶ CommRingCat.of k₁) (ι₂ : T.residueField x ⟶ CommRingCat.of k₂)
      (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k₁ Ω) (_ : Algebra k₂ Ω),
      Spec.map ι₁ ≫ T.fromSpecResidueField x = s₁ ∧
      Spec.map ι₂ ≫ T.fromSpecResidueField x = s₂ ∧
      ι₁ ≫ CommRingCat.ofHom (algebraMap k₁ Ω) = ι₂ ≫ CommRingCat.ofHom (algebraMap k₂ Ω) ∧
      Spec.map (CommRingCat.ofHom (algebraMap k₁ Ω)) ≫ s₁ =
        Spec.map (CommRingCat.ofHom (algebraMap k₂ Ω)) ≫ s₂ := by
  classical
  obtain ⟨⟨x₁, ι₁⟩, rfl⟩ := (Scheme.SpecToEquivOfField k₁ T).symm.surjective s₁
  obtain ⟨⟨x₂, ι₂⟩, rfl⟩ := (Scheme.SpecToEquivOfField k₂ T).symm.surjective s₂
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at hs₁ hs₂ ⊢
  obtain rfl : x₁ = x := by
    have := hs₁ ⟨IsLocalRing.closedPoint k₁, rfl⟩
    change (T.fromSpecResidueField x₁) ((Spec.map ι₁) (IsLocalRing.closedPoint k₁)) = x at this
    simpa using this
  obtain rfl : x₂ = x₁ := by
    have := hs₂ ⟨IsLocalRing.closedPoint k₂, rfl⟩
    change (T.fromSpecResidueField x₂) ((Spec.map ι₂) (IsLocalRing.closedPoint k₂)) = x₁ at this
    simpa using this
  let _ : Algebra (T.residueField x₂) k₁ := ι₁.hom.toAlgebra
  let _ : Algebra (T.residueField x₂) k₂ := ι₂.hom.toAlgebra
  let S : Type u := TensorProduct (T.residueField x₂) k₁ k₂
  let _ : Nontrivial S := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  let _ : Field (S ⧸ m) := Ideal.Quotient.field m
  let Ω : Type u := AlgebraicClosure (S ⧸ m)
  let f₁ : k₁ →+* Ω := (algebraMap (S ⧸ m) Ω).comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeLeft (R := T.residueField x₂) (S := T.residueField x₂) (A := k₁)
      (B := k₂)).toRingHom)
  let f₂ : k₂ →+* Ω := (algebraMap (S ⧸ m) Ω).comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight (R := T.residueField x₂) (A := k₁) (B := k₂)).toRingHom)
  have hcomp : ι₁ ≫ CommRingCat.ofHom f₁ = ι₂ ≫ CommRingCat.ofHom f₂ := by
    ext r
    change f₁ (algebraMap (T.residueField x₂) k₁ r) = f₂ (algebraMap (T.residueField x₂) k₂ r)
    simp only [f₁, f₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
  refine ⟨ι₁, ι₂, Ω, inferInstance, inferInstance, f₁.toAlgebra, f₂.toAlgebra, rfl, rfl, hcomp, ?_⟩
  change Spec.map (CommRingCat.ofHom f₁) ≫ _ = Spec.map (CommRingCat.ofHom f₂) ≫ _
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hcomp]
end Scheme_exists_isAlgClosed_factor_residueField_of_range_subset_singleton
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
