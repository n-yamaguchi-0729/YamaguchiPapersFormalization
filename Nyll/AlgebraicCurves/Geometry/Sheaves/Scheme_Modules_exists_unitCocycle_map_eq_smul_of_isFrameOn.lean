/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Choose
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesGlueOfCocycle

/-!
# Scheme Modules exists unit Cocycle map eq smul of is Frame On
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn


open _root_.CategoryTheory
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


universe u

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme Scheme.Modules Scheme.Modules.map_smul
  Scheme.Modules.IsFrameOn Scheme.Modules.UnitCocycle)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Γ Modules Opens Modules.map_smul restrict Modules.IsFrameOn
  Modules.UnitCocycle)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (presheaf restrict map_smul IsFrameOn UnitCocycle)

namespace RatioCocycle

open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry



open _root_.AlgebraicGeometry.Scheme.Modules.GlueOfCocycle


variable {X : Scheme.{u}} {M : X.Modules}

theorem map_smul' {A B : X.Opens} (h : B ≤ A) (r : Γ(X, A)) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE h).op (r • m) = X.presheaf.map (homOfLE h).op r • M.presheaf.map
      (homOfLE h).op m :=
  Scheme.Modules.map_smul M _ r m

theorem map_map {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE hCB).op (M.presheaf.map (homOfLE hBA).op m) = M.presheaf.map (homOfLE
      (hCB.trans hBA)).op m := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl

end AlgebraicGeometry.Scheme.Modules.RatioCocycle

open AlgebraicGeometry.Scheme.Modules.RatioCocycle AlgebraicGeometry.Scheme.Modules.GlueOfCocycle in
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_unitCocycle_map_eq_smul_of_isFrameOn
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
    {M : X.Modules} (e : ∀ i, Γ(M, U i)) (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (U i)) :
    ∃ c : Scheme.Modules.UnitCocycle U, ∀ i j,
      M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
        c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i) := by
  classical
  have hcoef : ∀ i j, ∃! u : Γ(X, U i ⊓ U j),
      u • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i) =
        M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) :=
    fun i j => (he i).existsUnique inf_le_left inf_le_left _
  choose u hu huniq using hcoef
  have hcoefW : ∀ (i : ι) {W : X.Opens} (hW : W ≤ U i) (a b : Γ(X, W)),
      a • M.presheaf.map (homOfLE hW).op (e i) = b • M.presheaf.map (homOfLE hW).op (e i) → a = b :=
    fun i W hW a b h => ((he i) hW hW).1 h
  refine ⟨⟨u, fun i => ?_, fun i j k => ?_⟩, fun i j => (hu i j).symm⟩
  · apply hcoefW i inf_le_left
    rw [hu i i, one_smul]
  · let T : X.Opens := U i ⊓ U j ⊓ U k
    have hTi : T ≤ U i := inf_le_left.trans inf_le_left
    have hTij : T ≤ U i ⊓ U j := le_inf hTi (inf_le_left.trans inf_le_right)
    have hTjk : T ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hTik : T ≤ U i ⊓ U k := le_inf hTi inf_le_right
    apply hcoefW i hTi
    have hij := congrArg (M.presheaf.map (homOfLE hTij).op) (hu i j)
    have hjk := congrArg (M.presheaf.map (homOfLE hTjk).op) (hu j k)
    have hik := congrArg (M.presheaf.map (homOfLE hTik).op) (hu i k)
    rw [map_smul', map_map, map_map] at hij hjk hik
    change (rO hTij (u i j) * rO hTjk (u j k)) • _ = rO hTik (u i k) • _
    rw [mul_comm, mul_smul]
    erw [hij, hjk, hik]
end Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
