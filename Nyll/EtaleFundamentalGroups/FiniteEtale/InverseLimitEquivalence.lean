/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitFullness
import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitFaithfulness
import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitStageCoherence
import Nyll.SchemeTheory.FiniteEtale.InverseLimitModel

/-!
# Finite étale categories commute with inverse limits

The concrete colimit category is the localization of actual finite-étale
models at their cartesian arrows.  Its stage inclusions, canonical
pullback-transition isomorphisms, unit/composition equations, and
functor-category universal property are constructed in the stage modules.

Here the actual object-gluing theorem supplies essential surjectivity.
Together with the proved Hom and equality descent, this makes the original
base-change functor a localization and gives an actual equivalence with
finite étale covers of the limiting scheme.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale.InverseLimitModel

universe u

variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable (F : Iᵒᵖ ⥤ Scheme.{u}) (s : Cone F) (hs : IsLimit s)
variable [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (F.map h)]
variable [∀ i : Iᵒᵖ, CompactSpace (F.obj i)]
variable [∀ i : Iᵒᵖ, QuasiSeparatedSpace (F.obj i)]

include hs

/-- The actual base-change functor realizes finite-étale covers of the
limit as the localization of actual models at cartesian transitions. -/
theorem baseChange_isLocalization :
    (baseChange F s).IsLocalization (cartesian F) := by
  have hfull : (localizedBaseChange F s).Full := localizedBaseChange_full F s hs
  have hfaithful : (localizedBaseChange F s).Faithful := localizedBaseChange_faithful F s hs
  have hessSurj : (localizedBaseChange F s).EssSurj := by
    constructor
    intro X
    obtain ⟨i, N, he⟩ := exists_inverse_limit_model F s hs X
    exact ⟨(cartesian F).Q.obj ((stageInclusion F i).obj N), he⟩
  have hequivalence : (localizedBaseChange F s).IsEquivalence :=
    { faithful := hfaithful, full := hfull, essSurj := hessSurj }
  exact Functor.IsLocalization.of_equivalence_target
    (cartesian F).Q (cartesian F) (baseChange F s)
    (localizedBaseChange F s).asEquivalence (eqToIso (q_comp_localizedBaseChange F s))

/-- The categorical assertion of Stacks 58.14.1, with the directed
2-colimit represented by its actual cartesian model localization. -/
@[stacks 0BTV "The equivalence of finite-etale categories for a directed qcqs inverse limit."]
def inverseLimitEquivalence : (cartesian F).Localization ≌ FiniteEtale s.pt := by
  have : (baseChange F s).IsLocalization (cartesian F) := baseChange_isLocalization F s hs
  exact Localization.equivalenceFromModel (baseChange F s) (cartesian F)

/-- The equivalence recovers the original pullback of each actual stage
model, through the specified model-localization functor. -/
def inverseLimitEquivalence_pullbackComparison :
    (cartesian F).Q ⋙ (inverseLimitEquivalence F s hs).functor ≅ baseChange F s := by
  have : (baseChange F s).IsLocalization (cartesian F) := baseChange_isLocalization F s hs
  exact Localization.qCompEquivalenceFromModelFunctorIso (baseChange F s) (cartesian F)

end AlgebraicGeometry.FiniteEtale.InverseLimitModel
