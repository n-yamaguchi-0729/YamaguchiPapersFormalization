/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_dual_eq_of_ihomEval_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import SchemeTheory.Modules.Monoidal
import SchemeTheory.Modules.TensorSections
import AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections
import AlgebraicCurves.Geometry.Sheaves.ModulesDet
import AlgebraicCurves.Geometry.Sheaves.ModulesNormModule

/-!
# Scheme Modules Is Frame On dual eq of ihom Eval eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_dual_eq_of_ihomEval_eq

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite


lemma presheaf_map_map_aux {X : Scheme.{u}} (M : X.Modules) {A B C : X.Opens} (f : B ⟶ A) (g : C ⟶
  B) (k : C ⟶ A)
    (x : Γ(M, A)) : M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (g ≫ f) k]

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.dual_eq_of_ihomEval_eq
    {X : Scheme.{u}} {P : X.Modules} {U V : X.Opens} {p : Γ(P, U)}
    (hp : Scheme.Modules.IsFrameOn p V) (hVU : V ≤ U) {q q' : Γ(Scheme.Modules.dual P, V)}
    (h : Scheme.Modules.ihomEval P (𝟙_ X.Modules) V (P.presheaf.map (homOfLE hVU).op p) q =
      Scheme.Modules.ihomEval P (𝟙_ X.Modules) V (P.presheaf.map (homOfLE hVU).op p) q') :
    q = q' := by
  apply Scheme.Modules.ihom_sections_ext
  intro W i m
  obtain ⟨c, hc⟩ := (hp (i.le.trans hVU) i.le).2 m
  change c • P.presheaf.map (homOfLE (i.le.trans hVU)).op p = m at hc
  have hres : P.presheaf.map (homOfLE (i.le.trans hVU)).op p = P.presheaf.map i.op (P.presheaf.map
    (homOfLE hVU).op p) :=
    (presheaf_map_map_aux P _ _ _ p).symm
  rw [← hc, hres, Scheme.Modules.ihomEval_smul_left, Scheme.Modules.ihomEval_smul_left,
    ← Scheme.Modules.map_ihomEval, ← Scheme.Modules.map_ihomEval, h]
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_dual_eq_of_ihomEval_eq
end ProofImplementation
