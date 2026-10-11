/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# ext of forall comp eq of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.ext_of_forall_comp_eq_of_isAlgClosed

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.ext_of_forall_comp_eq_of_isAlgClosed
    {κ : Type u} [Field κ] [IsAlgClosed κ] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of κ)) (fY : Y ⟶ Spec (CommRingCat.of κ))
    [LocallyOfFiniteType fX] [IsReduced X] [IsSeparated fY]
    {f g : X ⟶ Y} (hf : f ≫ fY = fX) (hg : g ≫ fY = fX)
    (h : ∀ x : Spec (CommRingCat.of κ) ⟶ X, x ≫ fX = 𝟙 _ → x ≫ f = x ≫ g) :
    f = g := by
  classical
  let _ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace fX
  refine ext_of_fromSpecResidueField_eq f g fY (closedPoints X) ?_ ?_ (hf.trans hg.symm)
  · rw [Dense, ← Set.eq_univ_iff_forall]
    exact closure_closedPoints
  · intro x hx
    have hxcl : IsClosed ({x} : Set X) := hx
    let _ : LocallyOfFiniteType (X.fromSpecResidueField x) :=
      isClosed_singleton_iff_locallyOfFiniteType.1 hxcl
    let _ : LocallyOfFiniteType (X.fromSpecResidueField x ≫ fX) := inferInstance
    set φ : CommRingCat.of κ ⟶ CommRingCat.of (X.residueField x) := Spec.preimage
      (X.fromSpecResidueField x ≫ fX) with hφdef
    have hφ : Spec.map φ = X.fromSpecResidueField x ≫ fX := Spec.map_preimage _
    have hft : RingHom.FiniteType φ.hom := by
      have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
      exact HasRingHomProperty.Spec_iff.mp this
    let _ : Algebra κ (X.residueField x) := φ.hom.toAlgebra
    let _ : Algebra.FiniteType κ (X.residueField x) := hft
    let _ : Module.Finite κ (X.residueField x) := finite_of_finite_type_of_isJacobsonRing κ
      (X.residueField x)
    let _ : Algebra.IsIntegral κ (X.residueField x) := inferInstance
    have hbij : Function.Bijective (algebraMap κ (X.residueField x)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : κ ≃+* X.residueField x := RingEquiv.ofBijective (algebraMap κ (X.residueField x)) hbij
    let ψ : CommRingCat.of (X.residueField x) ⟶ CommRingCat.of κ := CommRingCat.ofHom
      e.symm.toRingHom
    have hψφ : φ ≫ ψ = 𝟙 _ := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      change e.symm (algebraMap κ (X.residueField x) a) = a
      exact e.symm_apply_apply a
    let _ : IsIso ψ := by
      refine ⟨⟨φ, ?_, hψφ⟩⟩
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      change algebraMap κ (X.residueField x) (e.symm b) = b
      exact e.apply_symm_apply b
    let x₀ : Spec (CommRingCat.of κ) ⟶ X := Spec.map ψ ≫ X.fromSpecResidueField x
    have hx₀ : x₀ ≫ fX = 𝟙 _ := by
      change (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ fX = 𝟙 _
      rw [Category.assoc, ← hφ, ← Spec.map_comp, hψφ, Spec.map_id]
    have hx₀' := h x₀ hx₀
    change (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ f = (Spec.map ψ ≫ X.fromSpecResidueField x) ≫
      g at hx₀'
    rw [Category.assoc, Category.assoc] at hx₀'
    exact (cancel_epi (Spec.map ψ)).1 hx₀'
end AlgebraicCurves.Geometry.Schemes.Proofs.ext_of_forall_comp_eq_of_isAlgClosed
end ProofImplementation
