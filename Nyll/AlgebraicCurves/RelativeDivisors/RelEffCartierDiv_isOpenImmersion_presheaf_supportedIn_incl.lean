/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn

/-!
The inclusion of divisors supported in an open is an open immersion of presheaves.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (U : 𝒞.Opens)


theorem isOpenImmersion_presheaf_supportedIn_incl_aux :
    IsOpenImmersion.presheaf (RelEffCartierDiv.supportedIn f r U).ι := by
  apply MorphismProperty.relative.of_exists
  intro T g
  set x : (RelEffCartierDiv.functor f r).obj (op T) := yonedaEquiv g with hx
  have hg : ∀ {T' : Scheme.{u}ᵒᵖ} (φ : unop T' ⟶ T),
      g.app T' φ = (RelEffCartierDiv.functor f r).map φ.op x := by
    intro T' φ
    rw [hx, yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  let W : T.Opens := x.2.supportedInLocus U
  have hxW : (RelEffCartierDiv.functor f r).map W.ι.op x ∈
      (RelEffCartierDiv.supportedIn f r U).obj (op (W : Scheme.{u})) := by
    rw [mem_supportedIn_iff, functor_map_snd]
    exact (supportedIn_pullbackAlong_iff _ _ _ _).mpr
      (by simp only [Quiver.Hom.unop_op, Scheme.Opens.range_ι]; exact subset_rfl)
  let y : (RelEffCartierDiv.supportedIn f r U).toFunctor.obj (op (W : Scheme.{u})) := ⟨_, hxW⟩
  refine ⟨W, yonedaEquiv.symm y, W.ι, ?_, inferInstance⟩
  apply IsPullback.of_forall_isPullback_app
  intro T'
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · refine ConcreteCategory.hom_ext _ _ fun ψ => ?_
    simp only [ConcreteCategory.comp_apply, yonedaEquiv_symm_app_apply, yoneda_map_app, hg]
    change (RelEffCartierDiv.functor f r).map ψ.op ((RelEffCartierDiv.functor f r).map W.ι.op x) = _
    rw [← Functor.map_comp_apply, ← op_comp]
    rfl
  · rintro ψ₁ ψ₂ ⟨-, h⟩
    simp only [yoneda_map_app] at h
    exact (cancel_mono W.ι).mp h
  · intro y₂ φ h
    change unop T' ⟶ T at φ
    change y₂.1 = g.app T' φ at h
    rw [hg] at h
    have hφ : (x.2.pullbackAlong φ rfl).SupportedIn U := by
      have := y₂.2
      rw [h, mem_supportedIn_iff, functor_map_snd] at this
      exact this
    rw [supportedIn_pullbackAlong_iff] at hφ
    have hW : Set.range φ ⊆ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
    refine ⟨IsOpenImmersion.lift W.ι φ hW, ?_, ?_⟩
    · apply Subtype.ext
      change (RelEffCartierDiv.functor f r).map (IsOpenImmersion.lift W.ι φ hW).op
        ((RelEffCartierDiv.functor f r).map W.ι.op x) = y₂.1
      rw [h, ← Functor.map_comp_apply, ← op_comp, IsOpenImmersion.lift_fac]
    · exact IsOpenImmersion.lift_fac W.ι φ hW

end AlgebraicGeometry.RelEffCartierDiv

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_presheaf_supportedIn_incl {𝒞 S
    : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (U : 𝒞.Opens) :
    IsOpenImmersion.presheaf (RelEffCartierDiv.supportedIn f r U).ι :=
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_presheaf_supportedIn_incl_aux f r U
end RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl
end AlgebraicCurves.RelativeDivisors.Proofs
end ProofImplementation
