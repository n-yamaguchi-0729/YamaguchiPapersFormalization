/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.ProjectiveSpace.Basic
import SchemeTheory.Modules.ProjectivePresentation

/-!
# Scheme Modules Finite By Sections of iso
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_FiniteBySections_of_iso

universe u

open CategoryTheory AlgebraicGeometry Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

namespace FBSIsoSketch

variable {X : Scheme.{u}} {M M' : X.Modules}

theorem map_app (φ : M ⟶ M') {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    M'.presheaf.map i.op (φ.app U s) = φ.app V (M.presheaf.map i.op s) := by
  have h := φ.mapPresheaf.naturality i.op
  have := congrArg (fun f => (ConcreteCategory.hom f) s) h
  simpa using this.symm

theorem app_bijective (e : M ≅ M') (U : X.Opens) : Function.Bijective (e.hom.app U) :=
  ConcreteCategory.bijective_of_isIso (e.hom.app U)

end FBSIsoSketch

open FBSIsoSketch in
theorem _root_.AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_iso
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M M' : X.Modules} (e : M ≅
      M')
    (hM : M.FiniteBySections f) : M'.FiniteBySections f := by
  obtain ⟨N, 𝔓, hfin⟩ := hM
  refine ⟨N,
    { σ := fun i => e.hom.app ⊤ (𝔓.σ i)
      toProj := 𝔓.toProj
      toProj_π := 𝔓.toProj_π
      frame := fun i V hV => ?_
      app_ratio_smul := fun i j => ?_ }, hfin⟩
  · have key : (fun g : Γ(X, V) => g • M'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (e.hom.app ⊤
      (𝔓.σ i)))
        = (e.hom.app V) ∘ (fun g : Γ(X, V) => g • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (𝔓.σ
          i)) := by
      funext g
      simp only [Function.comp_apply, map_app, Scheme.Modules.Hom.app_smul]
    rw [key]
    exact (app_bijective e V).comp (𝔓.frame i V hV)
  · rw [map_app, map_app, ← Scheme.Modules.Hom.app_smul, 𝔓.app_ratio_smul i j]
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_FiniteBySections_of_iso
end ProofImplementation
