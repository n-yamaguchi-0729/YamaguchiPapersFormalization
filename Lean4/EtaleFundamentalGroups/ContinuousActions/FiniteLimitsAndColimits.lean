/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Limits.FintypeCat
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.Topology.Category.FinTopCat

import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Finite limits and colimits of finite continuous actions

Finite limits and finite colimits of continuous actions on finite discrete
spaces are again continuous.  Consequently the inherited forgetful functor
from finite continuous actions to finite sets preserves both.

This is the categorical exactness foundation used for Stacks Project,
Tag `0BMV`.
-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.ContAction

variable {G : Type v} [Monoid G] [TopologicalSpace G]

omit [TopologicalSpace G] in
private lemma hom_apply_rho {X Y : Action FintypeCat.{u} G}
    (f : X ⟶ Y) (g : G) (x : X.V) :
    ConcreteCategory.hom f.hom (ConcreteCategory.hom (X.ρ g) x) =
      ConcreteCategory.hom (Y.ρ g) (ConcreteCategory.hom f.hom x) := by
  simpa only [FintypeCat.comp_apply] using
    ConcreteCategory.congr_hom (f.comm g) x

private lemma isContinuous_of_finite_limit
    {J : Type} [SmallCategory J] [FinCategory J]
    (F : J ⥤ Action FintypeCat.{u} G) (c : Cone F) (hc : IsLimit c)
    (hF : ∀ j, Action.IsContinuous (F.obj j)) :
    Action.IsContinuous c.pt := by
  rw [Action.isContinuous_def]
  change Continuous (fun p : G × c.pt.V ↦ ConcreteCategory.hom (c.pt.ρ p.1) p.2)
  rw [continuous_prod_of_discrete_right]
  intro x
  rw [continuous_discrete_rng]
  intro y
  have hpreimage :
      (fun g : G ↦ ConcreteCategory.hom (c.pt.ρ g) x) ⁻¹' ({y} : Set _) =
        ⋂ j : J, (fun g : G ↦ ConcreteCategory.hom ((F.obj j).ρ g)
          (ConcreteCategory.hom (c.π.app j).hom x)) ⁻¹'
            ({ConcreteCategory.hom (c.π.app j).hom y} : Set _) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
    constructor
    · intro h j
      have hcomm := hom_apply_rho (X := c.pt) (c.π.app j) g x
      exact hcomm.symm.trans
        (congrArg (fun z ↦ ConcreteCategory.hom (c.π.app j).hom z) h)
    · intro h
      apply Concrete.isLimit_ext (F ⋙ Action.forget FintypeCat G)
        (isLimitOfPreserves (Action.forget FintypeCat G) hc)
      intro j
      change ConcreteCategory.hom (c.π.app j).hom
          (ConcreteCategory.hom (c.pt.ρ g) x) =
        ConcreteCategory.hom (c.π.app j).hom y
      exact (hom_apply_rho (X := c.pt) (c.π.app j) g x).trans (h j)
  rw [hpreimage]
  apply isOpen_iInter_of_finite
  intro j
  have hcontinuous :
      Continuous (fun p : G × (F.obj j).V ↦
        ConcreteCategory.hom ((F.obj j).ρ p.1) p.2) :=
    (Action.isContinuous_def (F.obj j)).mp (hF j)
  exact (isOpen_discrete _).preimage
    (hcontinuous.comp (continuous_id.prodMk continuous_const))

private lemma isContinuous_of_finite_colimit
    {J : Type} [SmallCategory J] [FinCategory J]
    (F : J ⥤ Action FintypeCat.{u} G) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, Action.IsContinuous (F.obj j)) :
    Action.IsContinuous c.pt := by
  rw [Action.isContinuous_def]
  change Continuous (fun p : G × c.pt.V ↦ ConcreteCategory.hom (c.pt.ρ p.1) p.2)
  rw [continuous_prod_of_discrete_right]
  intro x
  obtain ⟨j, y, hy⟩ := FintypeCat.jointly_surjective
    (F ⋙ Action.forget FintypeCat G)
    ((Action.forget FintypeCat G).mapCocone c)
    (isColimitOfPreserves (Action.forget FintypeCat G) hc) x
  have hcontinuous :
      Continuous (fun p : G × (F.obj j).V ↦
        ConcreteCategory.hom ((F.obj j).ρ p.1) p.2) :=
    (Action.isContinuous_def (F.obj j)).mp (hF j)
  have horbit :
      Continuous (fun g : G ↦ ConcreteCategory.hom ((F.obj j).ρ g) y) :=
    hcontinuous.comp (continuous_id.prodMk continuous_const)
  have hleg :
      Continuous (fun z : (F.obj j).V ↦ ConcreteCategory.hom (c.ι.app j).hom z) :=
    continuous_of_discreteTopology
  rw [← hy]
  exact (hleg.comp horbit).congr fun g ↦
    hom_apply_rho (Y := c.pt) (c.ι.app j) g y

/-- Continuity of an action on a finite discrete space is closed under limits
indexed by finite categories. -/
instance isClosedUnderLimitsOfShape_isContinuous
    {J : Type} [SmallCategory J] [FinCategory J] :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (Action.IsContinuous (V := FintypeCat.{u}) (G := G)) J where
  limitsOfShape_le _ h := by
    obtain ⟨h⟩ := h
    exact isContinuous_of_finite_limit h.diag h.toLimitPresentation.cone
      h.isLimit h.prop_diag_obj

/-- Continuity of an action on a finite discrete space is closed under colimits
indexed by finite categories. -/
instance isClosedUnderColimitsOfShape_isContinuous
    {J : Type} [SmallCategory J] [FinCategory J] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (Action.IsContinuous (V := FintypeCat.{u}) (G := G)) J where
  colimitsOfShape_le _ h := by
    obtain ⟨h⟩ := h
    exact isContinuous_of_finite_colimit h.diag h.toColimitPresentation.cocone
      h.isColimit h.prop_diag_obj

/-- Finite continuous actions of a topological monoid have finite limits. -/
noncomputable instance hasFiniteLimits :
    HasFiniteLimits (ContAction FintypeCat.{u} G) where
  out _ _ _ := inferInstance

/-- Finite continuous actions of a topological monoid have finite colimits. -/
noncomputable instance hasFiniteColimits :
    HasFiniteColimits (ContAction FintypeCat.{u} G) where
  out _ _ _ := inferInstance

/-- The inherited forgetful functor from finite continuous actions to finite
sets preserves finite limits. -/
noncomputable instance forgetPreservesFiniteLimits :
    PreservesFiniteLimits
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat) where
  preservesFiniteLimits _ _ _ := by
    change PreservesLimitsOfShape _
      (ObjectProperty.ι
          (Action.IsContinuous (V := FintypeCat.{u}) (G := G)) ⋙
        Action.forget FintypeCat G)
    infer_instance

/-- The inherited forgetful functor from finite continuous actions to finite
sets preserves finite colimits. -/
noncomputable instance forgetPreservesFiniteColimits :
    PreservesFiniteColimits
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat) where
  preservesFiniteColimits _ _ _ := by
    change PreservesColimitsOfShape _
      (ObjectProperty.ι
          (Action.IsContinuous (V := FintypeCat.{u}) (G := G)) ⋙
        Action.forget FintypeCat G)
    infer_instance

/-- Restriction of finite continuous actions preserves finite limits. -/
noncomputable instance resPreservesFiniteLimits
    {H : Type w} [Monoid H] [TopologicalSpace H]
    (f : G →ₜ* H) :
    PreservesFiniteLimits (ContAction.res FintypeCat.{u} f) := by
  have : PreservesFiniteLimits
      (ContAction.res FintypeCat.{u} f ⋙
        ObjectProperty.ι
          (Action.IsContinuous (V := FintypeCat.{u}) (G := G))) := by
    change PreservesFiniteLimits
      (ObjectProperty.ι
          (Action.IsContinuous (V := FintypeCat.{u}) (G := H)) ⋙
        Action.res FintypeCat.{u} f.toMonoidHom)
    constructor
    intro J _ _
    apply Action.preservesLimitsOfShape_of_preserves
    change PreservesLimitsOfShape J
      (forget₂ (ContAction FintypeCat.{u} H) FintypeCat)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves
    (ContAction.res FintypeCat.{u} f)
    (ObjectProperty.ι
      (Action.IsContinuous (V := FintypeCat.{u}) (G := G)))

/-- Restriction of finite continuous actions preserves finite colimits. -/
noncomputable instance resPreservesFiniteColimits
    {H : Type w} [Monoid H] [TopologicalSpace H]
    (f : G →ₜ* H) :
    PreservesFiniteColimits (ContAction.res FintypeCat.{u} f) := by
  have : PreservesFiniteColimits
      (ContAction.res FintypeCat.{u} f ⋙
        ObjectProperty.ι
          (Action.IsContinuous (V := FintypeCat.{u}) (G := G))) := by
    change PreservesFiniteColimits
      (ObjectProperty.ι
          (Action.IsContinuous (V := FintypeCat.{u}) (G := H)) ⋙
        Action.res FintypeCat.{u} f.toMonoidHom)
    constructor
    intro J _ _
    apply Action.preservesColimitsOfShape_of_preserves
    change PreservesColimitsOfShape J
      (forget₂ (ContAction FintypeCat.{u} H) FintypeCat)
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves
    (ContAction.res FintypeCat.{u} f)
    (ObjectProperty.ι
      (Action.IsContinuous (V := FintypeCat.{u}) (G := G)))

end CategoryTheory.ContAction
