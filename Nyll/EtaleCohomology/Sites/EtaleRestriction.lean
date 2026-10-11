/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.BaseChange
import Nyll.EtaleCohomology.Sites.SetSheafFunctors
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Over

/-!
# Restriction along an étale morphism

Composition with an étale morphism defines a continuous functor of small
étale sites. Its adjunction with scheme base change identifies actual inverse
image of set-valued sheaves with restriction of their underlying presheaves.
This makes local representers on an étale trivializing cover available for
effective descent, with their ordinary functorial sections.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {U X : Scheme.{u}} (f : U ⟶ X) [hf : Etale f]

/-- Postcomposition with an étale morphism on the small sites. -/
def etalePostcompose : U.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map (P := show MorphismProperty Scheme.{u} from @Etale) ⊤
    (show Etale f from inferInstance)

/-- Postcomposition and scheme base change are adjoint. -/
def etalePostcomposeBaseChangeAdjunction : etalePostcompose f ⊣ etaleBaseChange f :=
  MorphismProperty.Over.mapPullbackAdj
    (show MorphismProperty Scheme.{u} from @Etale) ⊤ f inferInstance trivial

/-- Postcomposition does not change the covering property of a family. -/
lemma etalePostcompose_coverPreserving :
    CoverPreserving U.smallEtaleTopology X.smallEtaleTopology (etalePostcompose f) where
  cover_preserve {V} {S} hS := by
    let : (Scheme.Etale.forget U).LocallyCoverDense (Scheme.etaleTopology.over U) :=
      inferInstanceAs ((MorphismProperty.Over.forget
        (show MorphismProperty Scheme.{u} from @Etale) ⊤ U).LocallyCoverDense _)
    let : (Scheme.Etale.forget X).LocallyCoverDense (Scheme.etaleTopology.over X) :=
      inferInstanceAs ((MorphismProperty.Over.forget
        (show MorphismProperty Scheme.{u} from @Etale) ⊤ X).LocallyCoverDense _)
    change S ∈ (Scheme.Etale.forget U).restrictedTopology
      (Scheme.etaleTopology.over U) V at hS
    change S.functorPushforward (etalePostcompose f) ∈
      (Scheme.Etale.forget X).restrictedTopology
        (Scheme.etaleTopology.over X) ((etalePostcompose f).obj V)
    rw [CategoryTheory.Functor.mem_restrictedTopology_iff] at hS ⊢
    rw [← Sieve.functorPushforward_comp]
    change S.functorPushforward
        (Scheme.Etale.forget U ⋙ CategoryTheory.Over.map f) ∈
      (Scheme.etaleTopology.over X) _
    rw [Sieve.functorPushforward_comp]
    exact (GrothendieckTopology.over_map_coverPreserving Scheme.etaleTopology f).cover_preserve hS

instance : PreservesLimitsOfShape WalkingCospan (etalePostcompose f) := by
  let H := Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X
  have : PreservesLimitsOfShape WalkingCospan (etalePostcompose f ⋙ H) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (Scheme.Etale.forget U ⋙ CategoryTheory.Over.forget U))
  exact preservesLimitsOfShape_of_reflects_of_preserves (etalePostcompose f) H

instance : (etalePostcompose f).IsContinuous U.smallEtaleTopology X.smallEtaleTopology := by
  let : Functor.PreservesOneHypercovers.{u + 1} (etalePostcompose f)
      U.smallEtaleTopology X.smallEtaleTopology :=
    Functor.PreservesOneHypercovers.of_coverPreserving (etalePostcompose_coverPreserving f)
  exact Functor.isContinuous_of_preservesOneHypercovers (etalePostcompose f)
    U.smallEtaleTopology X.smallEtaleTopology

variable (A : Type v) [Category.{w} A]

/-- Restriction of sheaves by precomposition with the étale postcomposition functor. -/
def etaleRestriction : Sheaf X.smallEtaleTopology A ⥤ Sheaf U.smallEtaleTopology A :=
  (etalePostcompose f).sheafPushforwardContinuous A
    U.smallEtaleTopology X.smallEtaleTopology

/-- Restriction along an étale morphism is left adjoint to direct image. -/
def etaleRestrictionPushforwardAdjunction :
    etaleRestriction f A ⊣ (etaleBaseChange f).sheafPushforwardContinuous A
      X.smallEtaleTopology U.smallEtaleTopology :=
  (etalePostcomposeBaseChangeAdjunction f).sheafPushforwardContinuous
    U.smallEtaleTopology X.smallEtaleTopology

/-- The constructed inverse image is naturally isomorphic to ordinary restriction. -/
def etaleSetPullbackRestrictionIso : etaleSetPullback f ≅ etaleRestriction f (Type u) :=
  (etaleSetPullbackPushforwardAdjunction f).leftAdjointUniq
    (etaleRestrictionPushforwardAdjunction f (Type u))

end EtaleCohomology
