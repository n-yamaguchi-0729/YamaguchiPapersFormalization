/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.ProjectiveSpace.Basic
import SchemeTheory.Modules.ProjectivePresentation
import SchemeTheory.Modules.PullbackFrame

/-!
# Scheme Modules Proj Presentation exists proj Presentation pullback sigma eq to Proj eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry


attribute [local instance] MvPolynomial.gradedAlgebra

universe u

open Opposite TopologicalSpace

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Modules.pullback Scheme.Hom Spec Scheme Proj
  Scheme.Hom.comp_app Scheme.Modules.pullbackPushforwardAdjunction Proj.basicOpen Scheme.Modules
  Scheme.Hom.comp_preimage Proj.awayToSection ProjSpace.ratio)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Modules.Hom.app_smul Modules.pullback Hom Γ Modules.Hom
  Hom.comp_app basicOpen Modules.pullbackPushforwardAdjunction Modules Opens Hom.comp_preimage)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (Hom.app_smul pullback presheaf Hom.comp_app Hom
  mapPresheaf_app pullbackPushforwardAdjunction ProjPresentation
  bijective_smul_unit_app_of_bijective_smul)


open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry


namespace PresPre

variable {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (.of R)} (p : X' ⟶ X)
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

lemma preimage_chart (i : Fin (N + 1)) :
    (p ≫ 𝔓.toProj) ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i) =
      p ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) :=
  Scheme.Hom.comp_preimage _ _ _

/-- The presenting sections pulled back through the adjunction unit. -/
noncomputable abbrev σ' (i : Fin (N + 1)) : Γ((Modules.pullback p).obj M, ⊤) :=
  ((pullbackPushforwardAdjunction p).unit.app M).app ⊤ (𝔓.σ i)
omit 𝔓 in
lemma presheaf_map_congr {Z : Scheme.{u}} (G : TopCat.Presheaf Ab Z) {U V : Z.Opens}
    (k₁ k₂ : op U ⟶ op V) (z : G.obj (op U)) : G.map k₁ z = G.map k₂ z := by
  rw [show k₁ = k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

/-- The pullback of a module section through the adjunction unit. -/
noncomputable def eta (U : X.Opens) (m : Γ(M, U)) : Γ((Modules.pullback p).obj M, p ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction p).unit.app M).app U m
omit 𝔓 f in
lemma eta_smul (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) :
    eta p (M := M) U (r • m) = p.app U r • eta p (M := M) U m :=
  Modules.Hom.app_smul _ r m
omit 𝔓 f in
lemma eta_resTop (U : X.Opens) (m : Γ(M, ⊤)) :
    eta p (M := M) U (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op m) =
      ((Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : p ⁻¹ᵁ U ≤ ⊤)).op (eta p (M := M)
        ⊤ m) := by
  have hnat := ((pullbackPushforwardAdjunction p).unit.app M).mapPresheaf.naturality
    (homOfLE (le_top : U ≤ ⊤)).op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hx
  refine hx.trans ?_
  exact presheaf_map_congr ((Modules.pullback p).obj M).presheaf _ _ _

lemma ratio_pulled (i j : Fin (N + 1)) :
    (p.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i))
        (𝔓.toProj.app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
          (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j)))) •
      ((Modules.pullback p).obj M).presheaf.map
        (homOfLE (le_top : p ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) ≤ ⊤)).op (σ' p
          𝔓 i) =
      ((Modules.pullback p).obj M).presheaf.map
        (homOfLE (le_top : p ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) ≤ ⊤)).op (σ' p
          𝔓 j) := by
  have h := congrArg (eta p (M := M) (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)))
    (𝔓.app_ratio_smul i j)
  have h2 := (eta_smul p _ _ _).symm.trans h
  rw [eta_resTop, eta_resTop] at h2
  exact h2

lemma comp_app_ratio (i j : Fin (N + 1)) :
    (p ≫ 𝔓.toProj).app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
        (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j)) =
      p.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i))
        (𝔓.toProj.app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
          (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j))) := by
  have h := ConcreteCategory.congr_hom (Scheme.Hom.comp_app p 𝔓.toProj (Proj.basicOpen 𝒜R
    (MvPolynomial.X i)))
    (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j))
  exact h

/--
The projective presentation obtained by pulling back the module and precomposing its projective
map.
-/
noncomputable def precomp : ((Modules.pullback p).obj M).ProjPresentation (p ≫ f) N where
  σ := σ' p 𝔓
  toProj := p ≫ 𝔓.toProj
  toProj_π := by rw [Category.assoc, 𝔓.toProj_π]
  frame := fun i V hV =>
    bijective_smul_unit_app_of_bijective_smul p M (𝔓.σ i)
      (V := 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) (𝔓.frame i) V
      (hV.trans (preimage_chart p 𝔓 i).le)
  app_ratio_smul := fun i j => by
    have key := ratio_pulled p 𝔓 i j
    have hc := comp_app_ratio p 𝔓 i j
    rw [hc]
    exact key

lemma precomp_σ (i : Fin (N + 1)) :
    (precomp p 𝔓).σ i = ((pullbackPushforwardAdjunction p).unit.app M).app ⊤ (𝔓.σ i) := rfl

lemma precomp_toProj : (precomp p 𝔓).toProj = p ≫ 𝔓.toProj := rfl

end PresPre

end AlgebraicGeometry.Scheme.Modules

end Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
end AlgebraicCurves.Geometry.Sheaves.Proofs

namespace AlgebraicGeometry

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq in
open AlgebraicGeometry.Scheme.Modules.PresPre in
theorem Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq
    {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (.of R)} (p : X' ⟶ X)
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) :
    ∃ 𝔓' : ((Scheme.Modules.pullback p).obj M).ProjPresentation (p ≫ f) N,
      (∀ i, 𝔓'.σ i = (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) (𝔓.σ i))
        ∧
      𝔓'.toProj = p ≫ 𝔓.toProj :=
  ⟨precomp p 𝔓, fun _ => rfl, rfl⟩
end AlgebraicGeometry
end ProofImplementation
