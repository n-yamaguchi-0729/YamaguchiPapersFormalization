/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover

/-!
# Smooth Proper Curve exists is Closed Immersion level Set
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs.SmoothProperCurve_exists_isClosedImmersion_levelSet

universe u

open scoped TensorProduct
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.Algebra.TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace SmoothProperCurve
open _root_.AlgebraicGeometry.SmoothProperCurve
namespace LevelSetImpl
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (U₀ : C.Opens) (hU₀ : IsAffineOpen U₀)

theorem fromSpec_comp :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    hU₀.fromSpec ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R Γ(C, U₀))) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
  have h := IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top (Spec (CommRingCat.of R))) hU₀
    (le_top : U₀ ≤ c ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h]
  rfl

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The morphism from the base-changed affine chart into the base-changed curve. -/
noncomputable def chartMap :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    pullback (specMap R S) (specMap R Γ(C, U₀)) ⟶ pullback c (specMap R S) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
  pullback.lift (pullback.snd _ _ ≫ hU₀.fromSpec) (pullback.fst _ _)
    (by rw [Category.assoc, fromSpec_comp c U₀ hU₀, ← pullback.condition])

theorem chartMap_snd :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    chartMap c U₀ hU₀ S ≫ pullback.snd c (specMap R S) = pullback.fst _ _ :=
  pullback.lift_snd _ _ _

theorem chartMap_fst :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    chartMap c U₀ hU₀ S ≫ pullback.fst c (specMap R S) = pullback.snd _ _ ≫ hU₀.fromSpec :=
  pullback.lift_fst _ _ _

scoped instance mono_chartMap :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    Mono (chartMap c U₀ hU₀ S) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
  refine ⟨fun {T} x y h => ?_⟩
  apply pullback.hom_ext
  · have h1 := congrArg (· ≫ pullback.snd c (specMap R S)) h
    simpa only [Category.assoc, chartMap_snd] using h1
  · have h2 := congrArg (· ≫ pullback.fst c (specMap R S)) h
    simp only [Category.assoc, chartMap_fst] at h2
    rw [← Category.assoc, ← Category.assoc] at h2
    exact (cancel_mono hU₀.fromSpec).mp h2

end AlgebraicGeometry.SmoothProperCurve.LevelSetImpl

open AlgebraicGeometry.SmoothProperCurve.LevelSetImpl in
theorem _root_.AlgebraicGeometry.SmoothProperCurve.exists_isClosedImmersion_levelSet
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U₀ : C.Opens) (hU₀ : IsAffineOpen U₀) (f : Γ(C, U₀))
    (S : Type u) [CommRing S] [Algebra R S] (s : S)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
      Module.Finite S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))})) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    ∃ ι : Spec (CommRingCat.of (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C,
      U₀))})) ⟶ pullback c (specMap R S),
      IsClosedImmersion ι ∧ ι ≫ baseChange R c S = specMap S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S)
        ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
  set I : Ideal (S ⊗[R] Γ(C, U₀)) := Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))} with hI
  have : Module.Finite S (S ⊗[R] Γ(C, U₀) ⧸ I) := hfin
  let q : Spec (CommRingCat.of (S ⊗[R] Γ(C, U₀) ⧸ I)) ⟶ Spec (CommRingCat.of (S ⊗[R] Γ(C, U₀))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let e := (pullbackSpecIso R S Γ(C, U₀)).inv
  let ι := q ≫ e ≫ chartMap c U₀ hU₀ S
  have hιsnd : ι ≫ baseChange R c S = specMap S (S ⊗[R] Γ(C, U₀) ⧸ I) := by
    change (q ≫ e ≫ chartMap c U₀ hU₀ S) ≫ pullback.snd c (specMap R S) = _
    simp only [Category.assoc, chartMap_snd, q, e]
    rw [pullbackSpecIso_inv_fst', ← Spec.map_comp]
    rfl
  refine ⟨ι, ?_, hιsnd⟩
  have : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : Mono ι := by
    change Mono (q ≫ e ≫ chartMap c U₀ hU₀ S)
    infer_instance
  have : IsProper (ι ≫ baseChange R c S) := by
    rw [hιsnd]
    have : IsFinite (specMap S (S ⊗[R] Γ(C, U₀) ⧸ I)) := by
      rw [IsFinite.SpecMap_iff]
      change (algebraMap S (S ⊗[R] Γ(C, U₀) ⧸ I)).Finite
      exact RingHom.finite_algebraMap.mpr inferInstance
    infer_instance
  have : IsProper ι := IsProper.of_comp ι (baseChange R c S)
  exact IsClosedImmersion.iff_isProper_and_mono ι |>.mpr ⟨inferInstance, inferInstance⟩
end AlgebraicCurves.Geometry.Curves.Proofs.SmoothProperCurve_exists_isClosedImmersion_levelSet
end ProofImplementation
