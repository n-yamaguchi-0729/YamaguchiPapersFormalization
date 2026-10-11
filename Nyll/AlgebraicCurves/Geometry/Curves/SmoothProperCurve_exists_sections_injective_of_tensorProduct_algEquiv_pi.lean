/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase

/-!
# Smooth Proper Curve exists sections injective of tensor Product alg Equiv pi
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi

universe u

open scoped TensorProduct
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace SmoothProperCurve
open _root_.AlgebraicGeometry.SmoothProperCurve
namespace SplitSectionsImpl
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.AlgebraicGeometry

section Ring

variable {R₀ R' B : Type u} [CommRing R₀] [CommRing R'] [CommRing B] [Algebra R₀ B] [Algebra R₀ R']
  {d : ℕ} (φ : (R' ⊗[R₀] B) ≃ₐ[R'] (Fin d → R'))

/-- Projection to a chosen factor of the split base-changed algebra. -/
noncomputable def proj (m : Fin d) : (R' ⊗[R₀] B) →ₐ[R'] R' :=
  (Pi.evalAlgHom R' (fun _ : Fin d => R') m).comp (φ : (R' ⊗[R₀] B) →ₐ[R'] (Fin d → R'))

theorem proj_apply (m : Fin d) (z : R' ⊗[R₀] B) : proj φ m z = φ z m := rfl

/-- The coordinate ring homomorphism obtained from the chosen factor of the split algebra. -/
noncomputable def coord (m : Fin d) : B →+* R' :=
  (proj φ m).toRingHom.comp (Algebra.TensorProduct.includeRight (R := R₀) (A := R') (B :=
    B)).toRingHom

theorem coord_apply (m : Fin d) (b : B) : coord φ m b = φ (1 ⊗ₜ[R₀] b) m := rfl

theorem proj_tmul (m : Fin d) (a : R') (b : B) : proj φ m (a ⊗ₜ[R₀] b) = a * coord φ m b := by
  rw [coord_apply, proj_apply]
  have h : a ⊗ₜ[R₀] b = algebraMap R' (R' ⊗[R₀] B) a * (1 ⊗ₜ[R₀] b) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  rw [h, map_mul, AlgEquiv.commutes, Pi.mul_apply, Pi.algebraMap_apply]
  rfl

theorem coord_algebraMap (m : Fin d) (x : R₀) : coord φ m (algebraMap R₀ B x) = algebraMap R₀ R' x
  := by
  rw [coord_apply, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have h : (algebraMap R₀ R' x) ⊗ₜ[R₀] (1 : B) = algebraMap R' (R' ⊗[R₀] B) (algebraMap R₀ R' x) :=
    by
    rw [Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [h, AlgEquiv.commutes, Pi.algebraMap_apply]
  rfl

theorem coord_comp_algebraMap (m : Fin d) : (coord φ m).comp (algebraMap R₀ B) = algebraMap R₀ R' :=
  RingHom.ext fun x => coord_algebraMap φ m x

theorem eq_of_apply_coord_eq {T : Type u} [CommRing T] [Nontrivial T] (t : R' →+* T) {i j : Fin d}
    (h : ∀ b : B, t (coord φ i b) = t (coord φ j b)) : i = j := by
  by_contra hij
  have key : ∀ z : R' ⊗[R₀] B, t (proj φ i z) = t (proj φ j z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b => rw [proj_tmul, proj_tmul, map_mul, map_mul, h b]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  have h1 := key (φ.symm (Pi.single i 1))
  rw [proj_apply, proj_apply, AlgEquiv.apply_symm_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm hij), map_one, map_zero] at h1
  exact one_ne_zero h1

end Ring

section Scheme

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  {R₀ : Type u} [CommRing R₀] [Algebra R R₀] {B : Type u} [CommRing B] [Algebra R₀ B]
  (ι : Spec (CommRingCat.of B) ⟶ pullback c (specMap R R₀))
  (hι : ι ≫ baseChange R c R₀ = specMap R₀ B)
  {R' : Type u} [CommRing R'] [Algebra R R'] [Algebra R₀ R'] [IsScalarTower R R₀ R']
  {d : ℕ} (φ : (R' ⊗[R₀] B) ≃ₐ[R'] (Fin d → R'))

/-- The morphism of spectra corresponding to the chosen coordinate homomorphism. -/
noncomputable abbrev specCoord (m : Fin d) : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (coord φ m))

theorem specCoord_comp_specMap (m : Fin d) : specCoord φ m ≫ specMap R₀ B = specMap R₀ R' := by
  change Spec.map (CommRingCat.ofHom (coord φ m)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) =
    Spec.map (CommRingCat.ofHom (algebraMap R₀ R'))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, coord_comp_algebraMap]

/-- The curve-valued point obtained from a factor of the split affine algebra. -/
noncomputable def secTop (m : Fin d) : Spec (CommRingCat.of R') ⟶ C :=
  specCoord φ m ≫ ι ≫ pullback.fst c (specMap R R₀)
include hι in
theorem secTop_comp (m : Fin d) : secTop c ι φ m ≫ c = specMap R R' := by
  have hι' : ι ≫ pullback.snd c (specMap R R₀) = specMap R₀ B := hι
  simp only [secTop, Category.assoc]
  rw [pullback.condition, ← Category.assoc ι, hι', ← Category.assoc, specCoord_comp_specMap φ m]
  change Spec.map (CommRingCat.ofHom (algebraMap R₀ R')) ≫ Spec.map (CommRingCat.ofHom (algebraMap
    R R₀)) =
    Spec.map (CommRingCat.ofHom (algebraMap R R'))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R R₀ R']

/-- The section of the base-changed curve determined by the chosen split factor. -/
noncomputable def sec (m : Fin d) : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c
  R') :=
  ⟨pullback.lift (secTop c ι φ m) (𝟙 _) (by rw [secTop_comp c ι hι φ m, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

theorem sec_fst (m : Fin d) : (sec c ι hι φ m).1 ≫ pullback.fst c (specMap R R') = secTop c ι φ m :=
  pullback.lift_fst _ _ _

theorem sec_injective [IsClosedImmersion ι] (k : Type u) [Field k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R')) :
    Function.Injective fun m => s ≫ (sec c ι hι φ m).1 := by
  intro i j h
  have hι' : ι ≫ pullback.snd c (specMap R R₀) = specMap R₀ B := hι
  have h1 : s ≫ secTop c ι φ i = s ≫ secTop c ι φ j := by
    have := congrArg (· ≫ pullback.fst c (specMap R R')) h
    simpa only [Category.assoc, sec_fst] using this
  have h2 : (s ≫ specCoord φ i) ≫ ι = (s ≫ specCoord φ j) ≫ ι := by
    apply pullback.hom_ext
    · simpa only [secTop, Category.assoc] using h1
    · simp only [Category.assoc, hι', specCoord_comp_specMap φ]
  have h3 : s ≫ specCoord φ i = s ≫ specCoord φ j := (cancel_mono ι).mp h2
  obtain ⟨θ, rfl⟩ : ∃ θ, Spec.map θ = s := ⟨Spec.preimage s, Spec.map_preimage s⟩
  rw [← Spec.map_comp, ← Spec.map_comp] at h3
  have h4 := Spec.map_injective h3
  have E : ∀ b : B, θ.hom (coord φ i b) = θ.hom (coord φ j b) := fun b => by
    have := congrArg (fun f : CommRingCat.of B ⟶ CommRingCat.of k => f.hom b) h4
    simpa using this
  exact eq_of_apply_coord_eq φ θ.hom E

end Scheme

end AlgebraicGeometry.SmoothProperCurve.SplitSectionsImpl

open AlgebraicGeometry.SmoothProperCurve.SplitSectionsImpl in
theorem
  _root_.AlgebraicGeometry.SmoothProperCurve.exists_sections_injective_of_tensorProduct_algEquiv_pi
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (R₀ : Type u) [CommRing R₀] [Algebra R R₀]
    (B : Type u) [CommRing B] [Algebra R₀ B]
    (ι : Spec (CommRingCat.of B) ⟶ pullback c (specMap R R₀)) [IsClosedImmersion ι]
    (hι : ι ≫ baseChange R c R₀ = specMap R₀ B)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R₀ R'] [IsScalarTower R R₀ R']
    (d : ℕ) (φ : (R' ⊗[R₀] B) ≃ₐ[R'] (Fin d → R')) :
    ∃ σ : Fin d → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R'),
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R')),
        Function.Injective fun i => s ≫ (σ i).1 :=
  ⟨fun m => sec c ι hι φ m, fun k _ s => sec_injective c ι hι φ k s⟩
end SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation
