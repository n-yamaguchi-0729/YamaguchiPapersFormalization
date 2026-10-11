/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Compatible sections of a fibre product of module sheaves

Sections of a pullback are identified with pairs whose images in the common target agree.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_fibreProduct_sections_bijective

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace FibreProductSections
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Evaluate a presheaf of abelian groups on `U` and forget the group structure. -/
noncomputable def evalForget (U : X.Opens) : TopCat.Presheaf Ab X ⥤ Type u :=
  (CategoryTheory.evaluation _ _).obj (op U) ⋙ CategoryTheory.forget Ab

noncomputable scoped instance (U : X.Opens) : PreservesLimitsOfShape WalkingCospan (evalForget (X :=
  X) U) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    ((CategoryTheory.evaluation (TopologicalSpace.Opens X)ᵒᵖ Ab.{u}).obj (op U) ⋙
        CategoryTheory.forget Ab.{u}))

/-- Take the underlying set of sections of a module sheaf over `U`. -/
noncomputable def sectionsFunctorAt (U : X.Opens) : X.Modules ⥤ Type u :=
  toPresheaf X ⋙ evalForget U

noncomputable scoped instance (U : X.Opens) :
    PreservesLimitsOfShape WalkingCospan (sectionsFunctorAt (X := X) U) := by
  unfold sectionsFunctorAt; infer_instance

theorem sectionsFunctorAt_map {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    (sectionsFunctorAt U).map φ x = φ.app U x := rfl

end AlgebraicGeometry.Scheme.Modules.FibreProductSections

open CategoryTheory.Limits _root_.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules
    AlgebraicGeometry.Scheme.Modules.FibreProductSections in
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_fibreProduct_sections_bijective
    {X : Scheme.{u}} {N₀ N₁ N₀₁ : X.Modules} (a : N₀ ⟶ N₀₁) (b : N₁ ⟶ N₀₁) :
    ∃ (L : X.Modules) (π₀ : L ⟶ N₀) (π₁ : L ⟶ N₁), π₀ ≫ a = π₁ ≫ b ∧
      (∀ U : X.Opens, Function.Injective fun s : Γ(L, U) => (π₀.app U s, π₁.app U s)) ∧
      (∀ (U : X.Opens) (s₀ : Γ(N₀, U)) (s₁ : Γ(N₁, U)), a.app U s₀ = b.app U s₁ →
        ∃ s : Γ(L, U), π₀.app U s = s₀ ∧ π₁.app U s = s₁) := by
  have key : ∀ U : X.Opens, ∃ e : (Γ(Limits.pullback a b, U) : Type u) ≃
      Types.PullbackObj ((sectionsFunctorAt U).map a) ((sectionsFunctorAt U).map b),
      ∀ s, (e s).1.1 = (pullback.fst a b).app U s ∧ (e s).1.2 = (pullback.snd a b).app U s := by
    intro U
    have hc := isLimitPullbackConeMapOfIsLimit (sectionsFunctorAt U) pullback.condition
      (pullbackIsPullback a b)
    exact ⟨PullbackCone.IsLimit.equivPullbackObj hc, fun s =>
      ⟨PullbackCone.IsLimit.equivPullbackObj_apply_fst hc s,
       PullbackCone.IsLimit.equivPullbackObj_apply_snd hc s⟩⟩
  refine ⟨Limits.pullback a b, pullback.fst a b, pullback.snd a b, pullback.condition, ?_, ?_⟩
  · intro U s t hst
    obtain ⟨e, he⟩ := key U
    apply e.injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rw [(he s).1, (he t).1]; exact congrArg Prod.fst hst
    · rw [(he s).2, (he t).2]; exact congrArg Prod.snd hst
  · intro U s₀ s₁ h
    obtain ⟨e, he⟩ := key U
    refine ⟨e.symm ⟨(s₀, s₁), h⟩, ?_, ?_⟩
    · have := (he (e.symm ⟨(s₀, s₁), h⟩)).1
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    · have := (he (e.symm ⟨(s₀, s₁), h⟩)).2
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_fibreProduct_sections_bijective
end ProofImplementation
