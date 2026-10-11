/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_LocallyQuasiFinite_of_flat_of_locallyQuasiFinite_genericFiber.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.ClearExclamation
import Mathlib.Tactic.WLOG
import AlgebraicCurves.Foundations.Algebra.Algebra_QuasiFinite_of_flat_of_quasiFinite_genericFiber

/-!
# Locally Quasi Finite of flat of locally Quasi Finite generic Fiber
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace LocallyQuasiFinite_of_flat_of_locallyQuasiFinite_genericFiber

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.LocallyQuasiFinite.of_flat_of_locallyQuasiFinite_genericFiber
    {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.DimensionLEOne R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) [Flat f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    LocallyQuasiFinite f := by
  have : MorphismProperty.RespectsIso (@LocallyQuasiFinite.{u}) := by
    rw [HasRingHomProperty.eq_affineLocally (P := @LocallyQuasiFinite.{u})]
    exact affineLocally_respectsIso RingHom.QuasiFinite
      RingHom.QuasiFinite.propertyIsLocal.respectsIso
  suffices main : ∀ {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)), Flat f → LocallyOfFiniteType f →
      LocallyQuasiFinite (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) →
      LocallyQuasiFinite f by
    exact main f ‹_› ‹_› ‹_›
  clear! Y
  intro Y f hf hft hgen
  wlog hY : ∃ S, Y = Spec S generalizing Y
  · refine (HasRingHomProperty.iff_of_source_openCover (P := @LocallyQuasiFinite.{u})
      Y.affineCover).mpr
      fun i => HasRingHomProperty.appTop (P := @LocallyQuasiFinite.{u}) _
        (this _ inferInstance inferInstance ?_ ⟨_, rfl⟩)
    rw [← pullbackRightPullbackFstIso_inv_snd_snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) (Y.affineCover.f i)]
    infer_instance
  obtain ⟨S, rfl⟩ := hY
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [HasRingHomProperty.Spec_iff (P := @Flat)] at hf
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite.{u})]
  algebraize [φ.hom]
  have hgen' : LocallyQuasiFinite (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := hgen
  rw [← pullbackSpecIso_hom_snd R S K,
    MorphismProperty.cancel_left_of_respectsIso (P := @LocallyQuasiFinite.{u}),
    HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite.{u}), CommRingCat.hom_ofHom] at hgen'
  have h2 := (RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective
    (Algebra.TensorProduct.comm R S K).toRingEquiv.toRingHom
    (Algebra.TensorProduct.comm R S K).surjective)).comp hgen'
  have h3 : (Algebra.TensorProduct.comm R S K).toRingEquiv.toRingHom.comp
      ((Algebra.TensorProduct.includeRight (R := R) (A := S) (B := K) : K →ₐ[R] _) : K →+* _) =
      algebraMap K (TensorProduct R K S) :=
    RingHom.ext fun k => by simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h3, RingHom.quasiFinite_algebraMap] at h2
  change (algebraMap R S).QuasiFinite
  rw [RingHom.quasiFinite_algebraMap]
  exact Algebra.QuasiFinite.of_flat_of_quasiFinite_genericFiber (K := K) h2
end LocallyQuasiFinite_of_flat_of_locallyQuasiFinite_genericFiber
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
