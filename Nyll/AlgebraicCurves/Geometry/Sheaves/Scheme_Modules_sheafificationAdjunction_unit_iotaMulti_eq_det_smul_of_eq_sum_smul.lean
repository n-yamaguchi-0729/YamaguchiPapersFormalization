/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exteriorPower_map_app_unit_iotaMulti_eq_det_smul
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule

/-!
# Scheme Modules sheafification Adjunction unit iota Multi eq det smul of eq sum smul
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.SheafifiedDeterminant

universe u

open CategoryTheory AlgebraicGeometry Opposite

end AlgebraicCurves.Geometry.Sheaves.Proofs.SheafifiedDeterminant

section
universe u
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs.SheafifiedDeterminant
namespace AlgebraicGeometry

theorem Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul
    {X : Scheme.{u}} {M : X.Modules} {V : X.Opens} {d : ℕ} (f f' : Fin d → Γ(M, V))
    (a : Matrix (Fin d) (Fin d) Γ(X, V)) (h : ∀ j, f' j = ∑ i, a i j • f i) :
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X d).obj M.val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower X d).obj M.val).obj (op V) from
        exteriorPower.ιMulti (M := Γ(M, V)) Γ(X, V) d f') :
      Γ(Scheme.Modules.det d M, V)) =
    a.det • (show Γ(Scheme.Modules.det d M, V) from
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X d).obj M.val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower X d).obj M.val).obj (op V) from
        exteriorPower.ιMulti (M := Γ(M, V)) Γ(X, V) d f))) := by
  have key := Scheme.Modules.exteriorPower_map_app_unit_iotaMulti_eq_det_smul (𝟙 M) (U := V) f' f a
    (fun j => by rw [h j]; rfl)
  rw [CategoryTheory.Functor.map_id] at key
  exact key
end AlgebraicGeometry
end
end ProofImplementation
