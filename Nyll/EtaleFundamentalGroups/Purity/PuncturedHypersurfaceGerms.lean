/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedHypersurfaceNeighborhoodDiagram
import Nyll.EtaleFundamentalGroups.Purity.PuncturedHypersurfaceNeighborhoodExistence
import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitModels
import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitEventualFaithfulness
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.FiniteEtale.DensePullback
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.NatIso
import Mathlib.Order.OrderDual

/-!
# Faithfulness on germs along a punctured hypersurface

The category of germs is the concrete localization of finite etale models
on open neighbourhoods at their cartesian transition arrows. Restriction
is the actual base-change functor from this localization to the punctured
hypersurface, using the constructed cone over the diagram of open neighbourhoods.

For a Noetherian local ring and an element of its maximal ideal, equality
of restricted morphisms is detected on a smaller neighbourhood. The
calculus of fractions therefore makes the restriction functor faithful.
This is the final categorical assertion of
[Stacks Project, Lemma 58.22.1](https://stacks.math.columbia.edu/tag/0BLN).
The geometric faithful neighbourhood is constructed from the original
ring hypotheses; no eventual-equality or faithfulness hypothesis remains
in the final theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteEtale.PuncturedHypersurface

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

variable (R : Type u) [CommRing R] [IsLocalRing R] (f : R)

/-- Faithfulness over the actual hypersurface pullback is preserved by its
constructed identification with the fixed punctured hypersurface. -/
theorem projection_pullback_faithful (W : Neighborhood R f)
    (hW : (pullback (Limits.pullback.fst W.val.ι (hypersurfaceMap R f))).Faithful) :
    (pullback (projection R f W)).Faithful := by
  have : (pullback (Limits.pullback.fst W.val.ι (hypersurfaceMap R f))).Faithful := hW
  have : (pullback (neighborhoodPullbackIso R f W).hom).Faithful :=
    pullback_faithful_of_isDominant (neighborhoodPullbackIso R f W).hom
  let e : pullback (projection R f W) ≅
      pullback (Limits.pullback.fst W.val.ι (hypersurfaceMap R f)) ⋙
        pullback (neighborhoodPullbackIso R f W).hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      (neighborhoodPullbackIso R f W).hom
      (Limits.pullback.fst W.val.ι (hypersurfaceMap R f))
      (projection R f W) rfl
  exact Functor.Faithful.of_iso e.symm

variable [IsNoetherianRing R] (hf : f ∈ IsLocalRing.maximalIdeal R)

include hf

/-- Equality of restrictions is detected on a genuine smaller neighbourhood.
The new stage is the intersection with the constructed faithful open. -/
theorem exists_stage_map_eq
    (i : (OrderDual (Neighborhood R f))ᵒᵖ)
    {A B : FiniteEtale ((diagram R f).obj i)} (a b : A ⟶ B)
    (hab : (pullback ((cone R f).π.app i)).map a =
      (pullback ((cone R f).π.app i)).map b) :
    ∃ (j : (OrderDual (Neighborhood R f))ᵒᵖ) (h : j ⟶ i),
      (pullback ((diagram R f).map h)).map a =
        (pullback ((diagram R f).map h)).map b := by
  obtain ⟨U, hUpuncture, hUzero, hUfaithful⟩ :=
    exists_punctured_hypersurface_neighborhood_faithful R f hf
  let V : Neighborhood R f :=
    ⟨i.unop.val ⊓ U, inf_le_right.trans hUpuncture,
      fun p hp hfp ↦ ⟨i.unop.property.2 p hp hfp, hUzero p hp hfp⟩⟩
  let j : (OrderDual (Neighborhood R f))ᵒᵖ := op (OrderDual.toDual V)
  let h : j ⟶ i :=
    (homOfLE (show i.unop ≤ OrderDual.toDual V from by
      change i.unop.val ⊓ U ≤ i.unop.val
      exact inf_le_left)).op
  have hV : (pullback ((cone R f).π.app j)).Faithful :=
    projection_pullback_faithful R f V (hUfaithful V.val inf_le_right V.property.2)
  let e : pullback ((cone R f).π.app i) ≅
      pullback ((diagram R f).map h) ⋙ pullback ((cone R f).π.app j) :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      ((cone R f).π.app j) ((diagram R f).map h)
      ((cone R f).π.app i) ((cone R f).w h).symm
  refine ⟨j, h, ?_⟩
  apply (pullback ((cone R f).π.app j)).map_injective
  change (pullback ((diagram R f).map h) ⋙ pullback ((cone R f).π.app j)).map a =
    (pullback ((diagram R f).map h) ⋙ pullback ((cone R f).π.app j)).map b
  rw [← NatIso.naturality_1 e a, ← NatIso.naturality_1 e b, hab]

/-- The actual restriction from the cartesian model localization of all open
neighbourhoods to the punctured hypersurface is faithful. This is the
neighbourhood-colimit assertion of Stacks 58.22.1, with the original local
Noetherian hypotheses and an element of the maximal ideal. -/
theorem restriction_faithful :
    (InverseLimitModel.localizedBaseChange (diagram R f) (cone R f)).Faithful :=
  InverseLimitModel.localizedBaseChange_faithful_of_stage_equality
    (diagram R f) (cone R f)
    (exists_stage_map_eq R f hf)

end AlgebraicGeometry.FiniteEtale.PuncturedHypersurface
