/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.EndDegree
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Relative Group Law surjective and end Degree eq finrank of is Finite of flat
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mKerRank

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem endDegree_eq_finrank_unit (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] :
    L.endDegree β =
      β.1.finrank ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 (IsLocalRing.closedPoint K)) := by
  have : IsFinite (L.endKerStr β) := inferInstance
  rw [RelativeGroupLaw.endDegree_of_isFinite]
  exact Scheme.Hom.finrank_pullback_snd β.1 _ _

theorem finrank_eq_finrank [LocallyOfFiniteType f] (β : SchemeHomOver f f) [IsFinite β.1] [Flat β.1]
    [PreconnectedSpace A] (x y : A) : β.1.finrank x = β.1.finrank y := by
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian A :=
    _root_.AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  have : LocallyOfFinitePresentation β.1 := inferInstance
  have h := Scheme.Hom.isLocallyConstant_finrank β.1
  exact h.apply_eq_of_preconnectedSpace x y

theorem endDegree_eq_finrank [LocallyOfFiniteType f] (L : RelativeGroupLaw K f) (β : SchemeHomOver
  f f)
    [IsFinite β.1] [Flat β.1] [PreconnectedSpace A] (x : A) : L.endDegree β = β.1.finrank x := by
  rw [endDegree_eq_finrank_unit L β]
  exact finrank_eq_finrank β _ x

theorem one_le_finrank [LocallyOfFiniteType f] (β : SchemeHomOver f f) [IsFinite β.1] [Flat β.1]
    [PreconnectedSpace A] (x : A) : 1 ≤ β.1.finrank x := by
  rw [finrank_eq_finrank β x (β.1 x)]
  exact Scheme.Hom.one_le_finrank_map β.1 x

theorem surjective [LocallyOfFiniteType f] (β : SchemeHomOver f f) [IsFinite β.1] [Flat β.1]
    [PreconnectedSpace A] : Function.Surjective β.1 := by
  have h : Surjective β.1 := (Scheme.Hom.one_le_finrank_iff_surjective β.1).mp fun x =>
    one_le_finrank β x
  exact h.surj

theorem main [LocallyOfFiniteType f] (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] [PreconnectedSpace A] :
    Function.Surjective β.1 ∧ 0 < L.endDegree β ∧ ∀ x : A, L.endDegree β = β.1.finrank x := by
  refine ⟨surjective β, ?_, endDegree_eq_finrank L β⟩
  rw [endDegree_eq_finrank_unit L β]
  exact one_le_finrank β _

end P2mKerRank

end
end RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs

namespace GoodReductionJacobian.RelativeGroupLaw

noncomputable section

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.NeronModelInfra _root_.GoodReductionJacobian

open _root_.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs in
open RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat in
theorem surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType
      f]
    [PreconnectedSpace A] (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] :
    Function.Surjective β.1 ∧ 0 < L.endDegree β ∧
      ∀ x : A, L.endDegree β = Scheme.Hom.finrank β.1 x :=
  P2mKerRank.main L β

end
end GoodReductionJacobian.RelativeGroupLaw
end ProofImplementation
