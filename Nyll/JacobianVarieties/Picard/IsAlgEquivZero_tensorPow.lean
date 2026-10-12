/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_tensorPow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.TensorPowers
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow

/-!
Tensor powers of an algebraically trivial invertible module remain algebraically trivial.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_tensorPow

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard


namespace AezTensorPow


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard


private theorem unit {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) :
    IsAlgEquivZero a (𝟙_ A.Modules) := by
  refine ⟨Spec (CommRingCat.of k), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec k,
    SheafOfModules.unit (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf,
    Scheme.Modules.isInvertible_unit _, ⟨𝟙 _, Category.comp_id _⟩, ⟨𝟙 _, Category.comp_id _⟩,
    ⟨Scheme.Modules.pullbackUnitIso _⟩, ⟨?_⟩⟩
  exact Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm



theorem main {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    {L : A.Modules}
    (hL : IsAlgEquivZero a L) (n : ℕ) : IsAlgEquivZero a (L.tensorPow n) := by
  induction n with
  | zero => exact unit a
  | succ n ih =>
    rw [Scheme.Modules.tensorPow_succ]
    exact ih.tensor hL

end AezTensorPow

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory in
open AlgebraicGeometry AlgebraicGeometry.RelPicard in
theorem _root_.AlgebraicGeometry.RelPicard.IsAlgEquivZero.tensorPow
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)} {L : A.Modules}
    (hL : IsAlgEquivZero a L) (n : ℕ) : IsAlgEquivZero a (L.tensorPow n) :=
  AezTensorPow.main hL n
end JacobianVarieties.Picard.Proofs.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_tensorPow
end ProofImplementation
