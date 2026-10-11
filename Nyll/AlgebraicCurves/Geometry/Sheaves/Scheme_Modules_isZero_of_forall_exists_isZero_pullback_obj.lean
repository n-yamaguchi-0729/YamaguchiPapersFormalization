/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic.Choose

/-!
# Vanishing of modules detected by pullback

Detects a zero module from vanishing pullbacks on a family covering all points.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj

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

lemma sections_eq_zero_of_isZero_pullback_ι {M : X.Modules} (U : X.Opens)
    (hU : IsZero ((Scheme.Modules.pullback U.ι).obj M)) (W : X.Opens) (hWU : W ≤ U)
    (s : Γ(M, W)) : s = 0 := by
  have h1 : IsZero ((restrictFunctor U.ι).obj M) :=
    hU.of_iso ((restrictFunctorIsoPullback U.ι).app M)
  have h2 : (𝟙 ((restrictFunctor U.ι).obj M) :) = 0 := h1.eq_of_src _ _
  have h4 : ∀ t : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)), t = 0 := fun t => by
    have h3 := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ (U.ι ⁻¹ᵁ W) : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ
      W)) → _) t) h2
    simp only [_root_.AlgebraicGeometry.Scheme.Modules.Hom.id_app,
      _root_.AlgebraicGeometry.Scheme.Modules.Hom.zero_app] at h3
    exact h3
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.2 hWU]
  let i : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ⟶ W := homOfLE e.le
  let j : W ⟶ U.ι ''ᵁ (U.ι ⁻¹ᵁ W) := homOfLE e.ge
  have hij : j ≫ i = 𝟙 W := Subsingleton.elim _ _
  calc s = M.presheaf.map (𝟙 (op W)) s := by simp
    _ = M.presheaf.map (j ≫ i).op s := by rw [hij]; rfl
    _ = M.presheaf.map j.op (M.presheaf.map i.op s) := by
      rw [op_comp, M.presheaf.map_comp]; rfl
    _ = 0 := by rw [h4 (M.presheaf.map i.op s), map_zero]

theorem _root_.AlgebraicGeometry.Scheme.Modules.isZero_of_forall_exists_isZero_pullback_obj (M :
  X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsZero ((Scheme.Modules.pullback U.ι).obj M)) :
    IsZero M := by
  choose U hxU hU using h
  have hsec : ∀ (W : X.Opens) (s : Γ(M, W)), s = 0 := by
    intro W s
    let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
    let V : W → X.Opens := fun x => W ⊓ U x.1
    refine F.eq_of_locally_eq' V W (fun x => homOfLE inf_le_left)
      (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hx, hxU x⟩) s 0 fun x => ?_
    rw [map_zero]
    exact sections_eq_zero_of_isZero_pullback_ι (U x.1) (hU x.1) (W ⊓ U x.1) inf_le_right _
  rw [IsZero.iff_id_eq_zero]
  ext W s
  simpa using hsec W s


end AlgebraicGeometry.Scheme.Modules
end Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
