/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCategories.AutomorphismInverseLimit
import EtaleFundamentalGroups.GeometricFiber.PointedComposition
import SchemeTheory.FiniteEtale.BaseChange.PullbackIdentity
import SchemeTheory.FiniteEtale.InverseLimitHom
import Mathlib.CategoryTheory.Category.Preorder

/-!
# The actual finite étale pullback diagram of an inverse system

The functors and cone maps are the canonical scheme pullbacks.  Their unit and
composition coherence is proved from the projection-based pullback coherence
theorems, including all equalities of the original diagram's scheme maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

private theorem pullbackCone_identity
    {X Y : Scheme.{u}} (p : X ⟶ Y) (f : Y ⟶ Y)
    (hf : f = 𝟙 Y) (hp : p = p ≫ f) :
    MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) p f p hp ≪≫
      Functor.isoWhiskerRight
        (eqToIso (congrArg pullback hf) ≪≫ pullbackIdIso Y) (pullback p) ≪≫
      Functor.leftUnitor (pullback p) = Iso.refl (pullback p) := by
  subst f
  simpa only [eqToIso_refl, Iso.refl_trans] using pullbackComp_id_coherence p

private theorem pullbackCone_composition
    {L X Y Z : Scheme.{u}} (p : L ⟶ X) (q : L ⟶ Y) (r : L ⟶ Z)
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : Z ⟶ X)
    (hp : p = q ≫ f) (hq : q = r ≫ g) (hh : h = g ≫ f)
    (hpr : p = r ≫ h) :
    MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) r h p hpr ≪≫
      Functor.isoWhiskerRight
        (MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) g f h hh) (pullback r) ≪≫
      Functor.associator (pullback f) (pullback g) (pullback r) =
    MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) q f p hp ≪≫
      Functor.isoWhiskerLeft (pullback f)
        (MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) r g q hq) := by
  subst p
  subst q
  subst h
  apply Iso.ext
  apply NatTrans.ext
  funext A
  let A₀ : FiniteEtale L := (pullback ((r ≫ g) ≫ f)).obj A
  let A₁ : FiniteEtale L := (pullback r).obj ((pullback (g ≫ f)).obj A)
  let A₂ : FiniteEtale L := (pullback r).obj ((pullback g).obj ((pullback f).obj A))
  let A₃ : FiniteEtale L := (pullback (r ≫ g)).obj ((pullback f).obj A)
  let a : A₀ ⟶ A₁ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) r (g ≫ f) ((r ≫ g) ≫ f)
    (Category.assoc r g f)).hom.app A
  let b : A₁ ⟶ A₂ := (pullback r).map ((MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) g f).hom.app A)
  let c : A₀ ⟶ A₃ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) (r ≫ g) f).hom.app A
  let d : A₃ ⟶ A₂ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) r g).hom.app ((pullback f).obj A)
  have hc : a ≫ b = c ≫ (d ≫ 𝟙 A₂) :=
    congrArg (fun z ↦ z.hom.app A)
      (pullbackComp_assoc_of_eq r g f ((r ≫ g) ≫ f) (Category.assoc r g f))
  change a ≫ (b ≫ 𝟙 A₂) = c ≫ d
  rw [Category.comp_id] at hc ⊢
  exact hc

namespace InverseLimitDiagram

variable {I : Type u} [Preorder I]
variable (D : Iᵒᵖ ⥤ Scheme.{u}) (s : Cone D)

/-- The original scheme transition associated to a comparison of indices. -/
def transitionMap {i j : I} (hij : i ≤ j) :
    D.obj (Opposite.op j) ⟶ D.obj (Opposite.op i) :=
  D.map (homOfLE hij).op

/-- Identity transitions use the identity scheme map. -/
theorem transitionMap_id (i : I) :
    transitionMap D (le_rfl : i ≤ i) = 𝟙 (D.obj (Opposite.op i)) := by
  exact D.map_id (Opposite.op i)

/-- The transition maps are the maps of the given functor, with its composition law. -/
theorem transitionMap_comp {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    transitionMap D (hij.trans hjk) = transitionMap D hjk ≫ transitionMap D hij := by
  exact D.map_comp (homOfLE hjk).op (homOfLE hij).op

/-- The category of finite étale covers at the original stage. -/
abbrev stage (i : I) := FiniteEtale (D.obj (Opposite.op i))

/-- The actual pullback functor from a stage to the cone point. -/
def toLimit (i : I) : stage D i ⥤ FiniteEtale s.pt :=
  pullback (s.π.app (Opposite.op i))

/-- The actual refinement functor between stage categories. -/
def transition {i j : I} (hij : i ≤ j) : stage D i ⥤ stage D j :=
  pullback (transitionMap D hij)

/-- The cone comparison is precisely the existing scheme pullback comparison. -/
def comparison {i j : I} (hij : i ≤ j) :
    toLimit D s i ≅ transition D hij ⋙ toLimit D s j :=
  inverseLimitPullbackComparison D s (homOfLE hij).op

/-- The actual unit comparison, including the original functor's map-id equality. -/
def unitIso (i : I) : transition D (le_rfl : i ≤ i) ≅ 𝟭 (stage D i) :=
  eqToIso (congrArg pullback (transitionMap_id D i)) ≪≫
    pullbackIdIso (D.obj (Opposite.op i))

/-- The actual composition comparison, including the original map-comp equality. -/
def compositionIso {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    transition D (hij.trans hjk) ≅ transition D hij ⋙ transition D hjk :=
  MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤)
    (transitionMap D hjk) (transitionMap D hij)
    (transitionMap D (hij.trans hjk)) (transitionMap_comp D hij hjk)

/-- Unit coherence of the supplied functor diagram is a theorem of actual pullbacks. -/
theorem comparison_identity (i : I) :
    comparison D s (le_rfl : i ≤ i) ≪≫
      Functor.isoWhiskerRight (unitIso D i) (toLimit D s i) ≪≫
      Functor.leftUnitor (toLimit D s i) = Iso.refl (toLimit D s i) := by
  exact pullbackCone_identity (s.π.app (Opposite.op i))
    (transitionMap D (le_rfl : i ≤ i)) (transitionMap_id D i)
    (s.w (homOfLE (le_rfl : i ≤ i)).op).symm

/-- Composition coherence of the supplied cone is proved, not assumed. -/
theorem comparison_composition {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    comparison D s (hij.trans hjk) ≪≫
      Functor.isoWhiskerRight (compositionIso D hij hjk) (toLimit D s k) ≪≫
      Functor.associator (transition D hij) (transition D hjk) (toLimit D s k) =
    comparison D s hij ≪≫ Functor.isoWhiskerLeft (transition D hij) (comparison D s hjk) := by
  exact pullbackCone_composition
    (s.π.app (Opposite.op i)) (s.π.app (Opposite.op j)) (s.π.app (Opposite.op k))
    (transitionMap D hij) (transitionMap D hjk) (transitionMap D (hij.trans hjk))
    (s.w (homOfLE hij).op).symm (s.w (homOfLE hjk).op).symm
    (transitionMap_comp D hij hjk) (s.w (homOfLE (hij.trans hjk)).op).symm

variable {Ω : Type u} [Field Ω] (point : Spec (.of Ω) ⟶ s.pt)

/-- The generic automorphism system instantiated with the actual scheme pullbacks. -/
abbrev pullbackAutSystem : ProCGroups.InverseSystems.InverseSystem (I := I) :=
  autInverseSystem (stage D) (toLimit D s) (transition D) (comparison D s)
    (fiber point) (unitIso D) (compositionIso D)
    (comparison_identity D s) (comparison_composition D s)

/-- The actual comparison into the stage-pullback automorphism system. -/
def pullbackAutComparison : π₁ᵉᵗ(point) →ₜ* (pullbackAutSystem D s point).inverseLimit :=
  autInverseLimitComparison (stage D) (toLimit D s) (transition D) (comparison D s)
    (fiber point) (unitIso D) (compositionIso D)
    (comparison_identity D s) (comparison_composition D s)

end InverseLimitDiagram

end AlgebraicGeometry.FiniteEtale
