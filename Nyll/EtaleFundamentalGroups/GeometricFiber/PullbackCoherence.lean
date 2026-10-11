/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition

/-!
# Coherence of the canonical finite étale pullback comparisons

The comparison isomorphisms are determined by the projections of the actual
pullbacks.  Their associativity supplies strict composition of pointed
fundamental-group maps, rather than composition only up to conjugation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

variable {W X Y Z : Scheme.{u}}

private theorem pullback_map_fst
    (f : X ⟶ Y) {A B : FiniteEtale Y} (q : A ⟶ B) :
    ((pullback f).map q).left ≫ Limits.pullback.fst B.hom f =
      Limits.pullback.fst A.hom f ≫ q.left :=
  Limits.pullback.lift_fst _ _ _

private theorem pullback_map_snd
    (f : X ⟶ Y) {A B : FiniteEtale Y} (q : A ⟶ B) :
    ((pullback f).map q).left ≫ Limits.pullback.snd B.hom f =
      Limits.pullback.snd A.hom f :=
  Limits.pullback.lift_snd _ _ _

/-- The two canonical comparisons from a triple composite to its iterated
pullback agree.  The equation is proved on scheme morphisms by the two
pullback projections. -/
theorem pullbackComp_assoc
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) f (g ≫ h) ≪≫
      Functor.isoWhiskerRight
        (MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) g h) (pullback f) =
    MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤)
        (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h).symm ≪≫
      Functor.isoWhiskerLeft (pullback h)
        (MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) f g) ≪≫
      (Functor.associator (pullback h) (pullback g) (pullback f)).symm := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext A
  let A₀ : Scheme := A.left
  let p : A₀ ⟶ Z := A.hom
  let A₁ : Scheme := Limits.pullback p h
  let p₁ : A₁ ⟶ Y := Limits.pullback.snd p h
  let A₂ : Scheme := Limits.pullback p₁ g
  let p₂ : A₂ ⟶ X := Limits.pullback.snd p₁ g
  let A₃ : Scheme := Limits.pullback p₂ f
  let L : Scheme := Limits.pullback p (g ≫ h)
  let l : L ⟶ X := Limits.pullback.snd p (g ≫ h)
  let M : Scheme := Limits.pullback l f
  let N : Scheme := Limits.pullback p₁ (f ≫ g)
  let T : Scheme := Limits.pullback p (f ≫ g ≫ h)
  let q : A₂ ⟶ L := ((MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) g h).inv.app A).left
  let u : A₃ ⟶ M := ((pullback f).map ((MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) g h).inv.app A)).left
  let v : M ⟶ T := ((MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) f (g ≫ h)).inv.app A).left
  let z : A₃ ⟶ N := ((MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) f g).inv.app ((pullback h).obj A)).left
  let w : N ⟶ T := ((MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤)
    (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h).symm).inv.app A).left
  let a₀ : A₃ ⟶ A₂ := Limits.pullback.fst p₂ f
  let a₁ : A₂ ⟶ A₁ := Limits.pullback.fst p₁ g
  let a₂ : A₁ ⟶ A₀ := Limits.pullback.fst p h
  let b₀ : M ⟶ L := Limits.pullback.fst l f
  let b₁ : L ⟶ A₀ := Limits.pullback.fst p (g ≫ h)
  let c₀ : N ⟶ A₁ := Limits.pullback.fst p₁ (f ≫ g)
  let r : T ⟶ A₀ := Limits.pullback.fst p (f ≫ g ≫ h)
  let s : T ⟶ W := Limits.pullback.snd p (f ≫ g ≫ h)
  let sM : M ⟶ W := Limits.pullback.snd l f
  let sN : N ⟶ W := Limits.pullback.snd p₁ (f ≫ g)
  let sA : A₃ ⟶ W := Limits.pullback.snd p₂ f
  have hu : u ≫ b₀ = a₀ ≫ q := pullback_map_fst f
    ((MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) g h).inv.app A)
  have hv : v ≫ r = b₀ ≫ b₁ :=
    pullbackComp_inv_app_left_fst f (g ≫ h) (f ≫ g ≫ h) rfl A
  have hq : q ≫ b₁ = a₁ ≫ a₂ :=
    pullbackComp_inv_app_left_fst g h (g ≫ h) rfl A
  have hz : z ≫ c₀ = a₀ ≫ a₁ :=
    pullbackComp_inv_app_left_fst f g (f ≫ g) rfl ((pullback h).obj A)
  have hw : w ≫ r = c₀ ≫ a₂ :=
    pullbackComp_inv_app_left_fst (f ≫ g) h (f ≫ g ≫ h)
      (Category.assoc f g h).symm A
  have huS : u ≫ sM = sA := pullback_map_snd f
    ((MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) g h).inv.app A)
  have hvS : v ≫ s = sM :=
    pullbackComp_inv_app_left_snd f (g ≫ h) (f ≫ g ≫ h) rfl A
  have hzS : z ≫ sN = sA :=
    pullbackComp_inv_app_left_snd f g (f ≫ g) rfl ((pullback h).obj A)
  have hwS : w ≫ s = sN :=
    pullbackComp_inv_app_left_snd (f ≫ g) h (f ≫ g ≫ h)
      (Category.assoc f g h).symm A
  apply MorphismProperty.Over.Hom.ext
  change u ≫ v = (𝟙 A₃ ≫ z) ≫ w
  rw [Category.id_comp]
  apply Limits.pullback.hom_ext
  · change (u ≫ v) ≫ r = (z ≫ w) ≫ r
    calc
      (u ≫ v) ≫ r = u ≫ (v ≫ r) := Category.assoc u v r
      _ = u ≫ (b₀ ≫ b₁) := congrArg (fun t : M ⟶ A₀ ↦ u ≫ t) hv
      _ = (u ≫ b₀) ≫ b₁ := (Category.assoc u b₀ b₁).symm
      _ = (a₀ ≫ q) ≫ b₁ := congrArg (fun t : A₃ ⟶ L ↦ t ≫ b₁) hu
      _ = a₀ ≫ (q ≫ b₁) := Category.assoc a₀ q b₁
      _ = a₀ ≫ (a₁ ≫ a₂) := congrArg (fun t : A₂ ⟶ A₀ ↦ a₀ ≫ t) hq
      _ = (a₀ ≫ a₁) ≫ a₂ := (Category.assoc a₀ a₁ a₂).symm
      _ = (z ≫ c₀) ≫ a₂ := congrArg (fun t : A₃ ⟶ A₁ ↦ t ≫ a₂) hz.symm
      _ = z ≫ (c₀ ≫ a₂) := Category.assoc z c₀ a₂
      _ = z ≫ (w ≫ r) := congrArg (fun t : N ⟶ A₀ ↦ z ≫ t) hw.symm
      _ = (z ≫ w) ≫ r := (Category.assoc z w r).symm
  · change (u ≫ v) ≫ s = (z ≫ w) ≫ s
    calc
      (u ≫ v) ≫ s = u ≫ (v ≫ s) := Category.assoc u v s
      _ = u ≫ sM := congrArg (fun t : M ⟶ W ↦ u ≫ t) hvS
      _ = sA := huS
      _ = z ≫ sN := hzS.symm
      _ = z ≫ (w ≫ s) := congrArg (fun t : N ⟶ W ↦ z ≫ t) hwS.symm
      _ = (z ≫ w) ≫ s := (Category.assoc z w s).symm

end AlgebraicGeometry.FiniteEtale
