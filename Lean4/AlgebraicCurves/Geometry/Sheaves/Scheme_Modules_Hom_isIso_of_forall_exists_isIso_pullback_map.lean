/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top

/-!
# Detecting isomorphisms by local pullback

A module morphism is an isomorphism when its pullback is an isomorphism
on an open neighborhood of each point.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map

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
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

lemma restrictFunctor_map_app' {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (W : (U : Scheme.{u}).Opens) :
    ((restrictFunctor U.ι).map φ).app W = φ.app (U.ι ''ᵁ W) := rfl

lemma isIso_app_of_isIso_pullback_ι_map {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (hU : IsIso ((Scheme.Modules.pullback U.ι).map φ)) (W : X.Opens) (hWU : W ≤ U) :
    IsIso (φ.app W) := by
  have h1 : IsIso ((restrictFunctor U.ι).map φ) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback U.ι) φ).2 hU
  have h2 := Hom.isIso_iff_isIso_app.1 h1 (U.ι ⁻¹ᵁ W)
  rw [restrictFunctor_map_app'] at h2
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.2 hWU]
  rw [← e]
  exact h2

theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map {M N :
  X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map φ)) :
    IsIso φ := by
  choose U hxU hU using h
  refine Hom.isIso_of_isIso_app_of_iSup_eq_top φ U ?_ (fun x V hV => ?_)
  · exact top_le_iff.mp fun x _ => Opens.mem_iSup.2 ⟨x, hxU x⟩
  · exact isIso_app_of_isIso_pullback_ι_map φ (U x) (hU x) V hV


end AlgebraicGeometry.Scheme.Modules
end Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
