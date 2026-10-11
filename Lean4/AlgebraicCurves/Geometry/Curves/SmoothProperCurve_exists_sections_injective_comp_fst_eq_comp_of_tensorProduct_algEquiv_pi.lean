/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Ring.Pi
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Scheme
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase

/-!
# Smooth Proper Curve exists sections injective comp fst eq comp of tensor Product alg Equiv
pi
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.TensorProduct
open _root_.NeronModelInfra


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Spec.map_comp Spec Spec.map Scheme Spec.map_injective
  SmoothProperCurve.specMap SmoothProperCurve.baseChange)

namespace SmoothProperCurve

export _root_.AlgebraicGeometry.SmoothProperCurve (specMap baseChange)

namespace SplitSections

open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.AlgebraicGeometry


variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R']
  {B : Type u} [CommRing B] [Algebra R B] {d : ℕ} (φ : R' ⊗[R] B ≃ₐ[R'] (Fin d → R'))

/-- The coordinate homomorphism obtained by splitting the base-changed algebra into a product. -/
noncomputable def coordHom (m : Fin d) : B →+* R' :=
  (Pi.evalRingHom (fun _ : Fin d => R') m).comp
    (φ.toRingEquiv.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R) (A := R') (B :=
      B)).toRingHom)

theorem coordHom_comp_algebraMap (m : Fin d) : (coordHom φ m).comp (algebraMap R B) = algebraMap R
  R' := by
  ext a
  simp only [coordHom, RingHom.coe_comp, Function.comp_apply]
  have h1 : (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := B)).toRingHom (algebraMap
    R B a) =
      algebraMap R' (R' ⊗[R] B) (algebraMap R R' a) := by
    change Algebra.TensorProduct.includeRight (R := R) (A := R') (B := B) (algebraMap R B a) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R R' (R' ⊗[R] B)]
  rw [h1]
  have h2 : φ.toRingEquiv.toRingHom (algebraMap R' (R' ⊗[R] B) (algebraMap R R' a)) =
      algebraMap R' (Fin d → R') (algebraMap R R' a) := φ.commutes _
  rw [h2, Pi.evalRingHom_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem coordHom_injective [Nontrivial R'] : Function.Injective (coordHom (R := R) φ) := by
  classical
  intro m m' h
  by_contra hne
  let F : Fin d → (R' ⊗[R] B →ₐ[R'] R') := fun n => (Pi.evalAlgHom R' (fun _ : Fin d => R') n).comp
    φ.toAlgHom
  have hF : F m = F m' := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext b
      exact congrArg (fun f : B →+* R' => f b) h
  have := congrArg (fun G : R' ⊗[R] B →ₐ[R'] R' => G (φ.symm (Pi.single m 1))) hF
  simp only [F, AlgHom.coe_comp, Function.comp_apply, Pi.evalAlgHom_apply] at this
  rw [AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, Pi.single_eq_same, Pi.single_apply,
    ite_eq_right (Ne.symm hne)] at this
  exact one_ne_zero this

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (z : Spec (CommRingCat.of B) ⟶ C)
  (hz : z ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B)))

/-- The section of the base-changed curve induced by a chosen factor of the split algebra. -/
noncomputable def splitSection (m : Fin d) : SchemeHomOver (𝟙 (Spec (CommRingCat.of R')))
  (baseChange R c R') :=
  ⟨pullback.lift (Spec.map (CommRingCat.ofHom (coordHom φ m)) ≫ z) (𝟙 _) (by
      rw [Category.assoc, hz, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        coordHom_comp_algebraMap]),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem splitSection_fst (m : Fin d) :
    (splitSection φ c z hz m).1 ≫ pullback.fst c (specMap R R') = Spec.map (CommRingCat.ofHom
      (coordHom φ m)) ≫ z :=
  pullback.lift_fst _ _ _

theorem exists_splitSection_fst_eq (m : Fin d) :
    ∃ y : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of B),
      (splitSection φ c z hz m).1 ≫ pullback.fst c (specMap R R') = y ≫ z :=
  ⟨_, splitSection_fst φ c z hz m⟩

theorem splitSection_injective [Nontrivial R'] [Mono z] : Function.Injective (splitSection φ c z
  hz) := by
  intro m m' h
  have h1 := congrArg (fun σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R') =>
    σ.1 ≫ pullback.fst c (specMap R R')) h
  simp only [splitSection_fst] at h1
  have h2 : Spec.map (CommRingCat.ofHom (coordHom φ m)) = Spec.map (CommRingCat.ofHom (coordHom φ
    m')) :=
    (cancel_mono z).mp h1
  have h3 : CommRingCat.ofHom (coordHom φ m) = CommRingCat.ofHom (coordHom φ m') :=
    Spec.map_injective h2
  exact coordHom_injective φ (by
    have := congrArg CommRingCat.Hom.hom h3
    simpa using this)

end AlgebraicGeometry.SmoothProperCurve.SplitSections

attribute [local simp] AlgebraicGeometry.SmoothProperCurve.SplitSections.splitSection_fst




end SmoothProperCurve_exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi
end AlgebraicCurves.Geometry.Curves.Proofs

namespace AlgebraicGeometry

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.SmoothProperCurve _root_.TensorProduct _root_.NeronModelInfra

open _root_.AlgebraicCurves.Geometry.Curves.Proofs in
open SmoothProperCurve_exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi in
attribute [local simp] AlgebraicGeometry.SmoothProperCurve.SplitSections.splitSection_fst

open _root_.AlgebraicCurves.Geometry.Curves.Proofs in
open SmoothProperCurve_exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi in
open AlgebraicGeometry.SmoothProperCurve.SplitSections in
theorem SmoothProperCurve.exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Nontrivial R']
    (B : Type u) [CommRing B] [Algebra R B] (d : ℕ) (φ : R' ⊗[R] B ≃ₐ[R'] (Fin d → R'))
    (z : Spec (CommRingCat.of B) ⟶ C) [Mono z] (hz : z ≫ c = Spec.map (CommRingCat.ofHom
      (algebraMap R B))) :
    ∃ σ : Fin d → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (SmoothProperCurve.baseChange R c
      R'),
      Function.Injective σ ∧
      ∀ m, ∃ y : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of B),
        (σ m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R R') = y ≫ z :=
  ⟨splitSection φ c z hz, splitSection_injective φ c z hz, exists_splitSection_fst_eq φ c z hz⟩
end AlgebraicGeometry
end ProofImplementation
