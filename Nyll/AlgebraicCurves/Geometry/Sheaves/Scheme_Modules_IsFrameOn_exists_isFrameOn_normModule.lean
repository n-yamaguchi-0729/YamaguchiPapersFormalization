/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_normModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_exists_isFrameOn_dual
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_exists_basis_smul_pushforward
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isFrameOn_sheafificationAdjunction_unit_iotaMulti
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_tensorSections

/-!
# Scheme Modules Is Frame On exists is Frame On norm Module
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.NormFrameExistence

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isFrameOn_normModule
    {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ) {L : X.Modules} {V : Y.Opens}
    (e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V))
    (he : ∀ (W : Y.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin d) Γ(Y, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).presheaf.map (homOfLE
          hW).op (e i))
    {s : Γ(L, π ⁻¹ᵁ V)} (hs : Scheme.Modules.IsFrameOn s (π ⁻¹ᵁ V)) :
    ∃ q : Γ(Scheme.Modules.dual (Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_
      X.Modules))), V),
      Scheme.Modules.IsFrameOn q V ∧
      Scheme.Modules.ihomEval (Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_
        X.Modules)))
          (𝟙_ Y.Modules) V
        (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj
              (𝟙_ X.Modules)).val)).app
          (op V)
          (show ((Scheme.Modules.presheafExteriorPower Y d).obj
              ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).val).obj (op V) from
                exteriorPower.ιMulti (M := Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules),
                V)) Γ(Y, V) d e))
        q = Scheme.Modules.unitSection V ∧
      Scheme.Modules.IsFrameOn (M := Scheme.Modules.normModule π d L)
        (Scheme.Modules.tensorSections
          (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
              ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj
                L).val)).app (op V)
            (show ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward
              π).obj L).val).obj (op V)
              from exteriorPower.ιMulti (M := Γ((Scheme.Modules.pushforward π).obj L, V)) Γ(Y, V) d
                (fun i => (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ
                  V) from e i) • s))))
          q)
        V := by
  have hE := Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
    (M := (Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)) e he
  obtain ⟨q, hq, hq1⟩ := hE.exists_isFrameOn_dual (le_refl V)
  have hES := Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
    (M := (Scheme.Modules.pushforward π).obj L)
    (fun i => (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e i)
      • s))
    (Scheme.Modules.IsFrameOn.exists_basis_smul_pushforward π e he hs)
  refine ⟨q, hq, ?_, ?_⟩
  · have hid : ∀ (M : Y.Modules) (x : Γ(M, V)), M.presheaf.map (homOfLE (le_refl V)).op x = x :=
      fun M x => by
      rw [show (homOfLE (le_refl V)).op = 𝟙 _ from Subsingleton.elim _ _,
        CategoryTheory.Functor.map_id]; rfl
    exact (congrArg
      (fun x : Γ(Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)), V) =>
        Scheme.Modules.ihomEval
          (Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)))
          (𝟙_ Y.Modules) V x q)
      (hid _ _)).symm.trans hq1
  · exact hES.tensorSections hq
end AlgebraicCurves.Geometry.Sheaves.Proofs.NormFrameExistence
end ProofImplementation
