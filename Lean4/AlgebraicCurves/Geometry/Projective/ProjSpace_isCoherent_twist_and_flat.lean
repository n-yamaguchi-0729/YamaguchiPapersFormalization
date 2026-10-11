/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Flat.Localization
import AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafSectionsLinearRes
import AlgebraicCurves.Geometry.Projective.ProjSpace_isQuasicoherent_twist
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent

/-!
# Proj Space is Coherent twist and flat
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isCoherent_twist_and_flat
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mTwistCohFlat

open AlgebraicGeometry.ProjSpace AlgebraicGeometry.OModulePresheaf

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ)
  (U : X.affineOpens)

/-- Functions whose basic opens are contained in one of the pullback charts. -/
def smallFuns : Set Γ(X, U.1) := {f | ∃ j : Fin (N + 1), X.basicOpen f ≤ pullbackChart φ j}

theorem span_smallFuns [IsAffineHom φ] : Ideal.span (smallFuns φ U) = ⊤ := by
  rw [← U.2.self_le_iSup_basicOpen_iff]
  intro x hx
  have hcov : (⨆ j : ULift.{u} (Fin (N + 1)), (ProjSpace.stdCoverPullback φ).U j) = ⊤ :=
    (ProjSpace.stdCoverPullback φ).iSup_eq_top
  have hx' : x ∈ (⨆ j : ULift.{u} (Fin (N + 1)), (ProjSpace.stdCoverPullback φ).U j) := by
    rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  obtain ⟨f, hfle, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hj⟩ hx
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, ⟨j.down, ?_⟩⟩, hxf⟩
  exact hfle

section Local

variable (f : Γ(X, U.1))

noncomputable scoped instance moduleU : Module Γ(X, U.1) ((twist π φ m).obj (X.basicOpen f)) :=
  (twist π φ m).moduleRestrict (X.basicOpen_le f)

scoped instance isScalarTower_U : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen f) ((twist π φ m).obj
  (X.basicOpen f)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

scoped instance isLocalization_U : IsLocalization.Away f Γ(X, X.basicOpen f) :=
  U.2.isLocalization_basicOpen f

theorem isLocalizedModule_res [IsSeparated π] [IsAffineHom φ] :
    IsLocalizedModule.Away f ((twist π φ m).resₗ (X.basicOpen_le f) :
      (twist π φ m).obj U.1 →ₗ[Γ(X, U.1)] (twist π φ m).obj (X.basicOpen f)) :=
  isLocalizedModule_res_of_isQuasicoherent (twist π φ m) (ProjSpace.isQuasicoherent_twist π φ m) U f

variable {f}

theorem finite_local {j : Fin (N + 1)} (hf : X.basicOpen f ≤ pullbackChart φ j) :
    Module.Finite Γ(X, X.basicOpen f) ((twist π φ m).obj (X.basicOpen f)) := by
  obtain ⟨e, -, -⟩ := ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart π φ m hf
  exact Module.Finite.equiv (e.symm : Γ(X, X.basicOpen f) ≃ₗ[Γ(X, X.basicOpen f)] twistObj π φ m
    (X.basicOpen f))

theorem flat_local {j : Fin (N + 1)} (hf : X.basicOpen f ≤ pullbackChart φ j) :
    Module.Flat Γ(X, U.1) ((twist π φ m).obj (X.basicOpen f)) := by
  obtain ⟨e, -, -⟩ := ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart π φ m hf
  have : Module.Flat Γ(X, U.1) Γ(X, X.basicOpen f) := IsLocalization.flat _ (Submonoid.powers f)
  have : Module.Flat Γ(X, X.basicOpen f) ((twist π φ m).obj (X.basicOpen f)) :=
    Module.Flat.of_linearEquiv (e : twistObj π φ m (X.basicOpen f) ≃ₗ[Γ(X, X.basicOpen f)] Γ(X,
      X.basicOpen f))
  exact Module.Flat.trans Γ(X, U.1) Γ(X, X.basicOpen f) _

end Local

theorem finite [IsSeparated π] [IsAffineHom φ] : Module.Finite Γ(X, U.1) ((twist π φ m).obj U.1) :=
  by
  have := fun g : smallFuns φ U => isLocalizedModule_res π φ m U g.1
  refine Module.Finite.of_localizationSpan' (smallFuns φ U) (span_smallFuns φ U)
    (Mₚ := fun g : smallFuns φ U => (twist π φ m).obj (X.basicOpen g.1))
    (Rₚ := fun g : smallFuns φ U => Γ(X, X.basicOpen g.1))
    (fun g => (twist π φ m).resₗ (X.basicOpen_le g.1)) fun g => ?_
  obtain ⟨j, hj⟩ := g.2
  exact finite_local π φ m U hj

theorem flat [IsSeparated π] [IsAffineHom φ] : Module.Flat Γ(X, U.1) ((twist π φ m).obj U.1) := by
  have := fun g : smallFuns φ U => isLocalizedModule_res π φ m U g.1
  refine Module.flat_of_isLocalized_span Γ(X, U.1) ((twist π φ m).obj U.1) (smallFuns φ U)
    (span_smallFuns φ U)
    (fun g : smallFuns φ U => (twist π φ m).obj (X.basicOpen g.1))
    (fun g => (twist π φ m).resₗ (X.basicOpen_le g.1)) fun g => ?_
  obtain ⟨j, hj⟩ := g.2
  exact flat_local π φ m U hj


theorem main [IsSeparated π] [IsAffineHom φ] : (twist π φ m).IsCoherent ∧ ∀ U : X.affineOpens,
  Module.Flat Γ(X, U.1) ((twist π φ m).obj U.1) :=
  ⟨fun U => finite π φ m U, fun U => flat π φ m U⟩

end P2mTwistCohFlat

attribute [local instance] P2mTwistCohFlat.moduleU
attribute [local instance] P2mTwistCohFlat.isScalarTower_U
attribute [local instance] P2mTwistCohFlat.isLocalization_U


theorem _root_.AlgebraicGeometry.ProjSpace.isCoherent_twist_and_flat
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (π : X ⟶ Spec (.of A)) [IsSeparated π]
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ] (m : ℕ) :
    (ProjSpace.twist π φ m).IsCoherent ∧
      ∀ U : X.affineOpens, Module.Flat Γ(X, U.1) ((ProjSpace.twist π φ m).obj U.1) :=
  P2mTwistCohFlat.main π φ m
end AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isCoherent_twist_and_flat
end ProofImplementation
