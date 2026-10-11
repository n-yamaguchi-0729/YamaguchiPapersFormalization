/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.EndDegree
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_finrank_comp_of_finrank_eq_const
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Relative Group Law end Degree scheme Hom Over Comp of is Finite of flat
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mDegMul

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem endDegree_eq_finrank_unit (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] :
    L.endDegree β =
      β.1.finrank ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 (IsLocalRing.closedPoint K)) := by
  have : IsFinite (L.endKerStr β) := inferInstance
  rw [RelativeGroupLaw.endDegree_of_isFinite]
  exact Scheme.Hom.finrank_pullback_snd β.1 _ _

theorem finrank_eq_finrank [LocallyOfFiniteType f] (β : SchemeHomOver f f) [IsFinite β.1]
    [Flat β.1] [PreconnectedSpace A] (x y : A) : β.1.finrank x = β.1.finrank y := by
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian A :=
    _root_.AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  have : LocallyOfFinitePresentation β.1 := inferInstance
  exact (Scheme.Hom.isLocallyConstant_finrank β.1).apply_eq_of_preconnectedSpace x y

theorem endDegree_eq_finrank [LocallyOfFiniteType f] (L : RelativeGroupLaw K f)
    (β : SchemeHomOver f f) [IsFinite β.1] [Flat β.1] [PreconnectedSpace A] (x : A) :
    L.endDegree β = β.1.finrank x := by
  rw [endDegree_eq_finrank_unit L β]
  exact finrank_eq_finrank β _ x

theorem main [LocallyOfFiniteType f] [PreconnectedSpace A] (L : RelativeGroupLaw K f)
    (β γ : SchemeHomOver f f) [IsFinite β.1] [Flat β.1] [IsFinite γ.1] [Flat γ.1] :
    L.endDegree (NeronModelInfra.schemeHomOverComp β γ) = L.endDegree β * L.endDegree γ := by
  have hfin : IsFinite (NeronModelInfra.schemeHomOverComp β γ).1 :=
    inferInstanceAs (IsFinite (β.1 ≫ γ.1))
  have hfl : Flat (NeronModelInfra.schemeHomOverComp β γ).1 :=
    inferInstanceAs (Flat (β.1 ≫ γ.1))
  let x : A := (L.one (𝟙 (Spec (CommRingCat.of K)))).1 (IsLocalRing.closedPoint K)
  rw [endDegree_eq_finrank L (NeronModelInfra.schemeHomOverComp β γ) x,
    endDegree_eq_finrank L γ x]
  have h := Scheme.Hom.finrank_comp_of_finrank_eq_const β.1 γ.1 (L.endDegree β)
    (fun y => (endDegree_eq_finrank L β y).symm) x
  exact h

end P2mDegMul

theorem
  _root_.GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_of_isFinite_of_flat
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType
      f]
    [PreconnectedSpace A] (L : RelativeGroupLaw K f) (β γ : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] [IsFinite γ.1] [Flat γ.1] :
    L.endDegree (NeronModelInfra.schemeHomOverComp β γ) = L.endDegree β * L.endDegree γ :=
  P2mDegMul.main L β γ

end
end RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
