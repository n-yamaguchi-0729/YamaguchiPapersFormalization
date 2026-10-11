/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.IdealQuotientMayerVietorisPowers

/-!
# Derived-Ext Mayer--Vietoris sequences along powers

The contravariant six-term derived-Ext sequence of a short exact complex is
functorial in morphisms of short complexes.  Applying that naturality to the
power-compatible ideal-quotient Mayer--Vietoris complexes produces the exact
sequence diagram that precedes an AB5 filtered-colimit argument.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe w v u

section ContravariantSequence

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The map on derived Ext induced contravariantly by a morphism in the first
argument. -/
def derivedExtContravariantMap {X X' : C} (f : X ⟶ X') (Y : C) (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Abelian.Ext.{w} X' Y n) ⟶
      AddCommGrpCat.of (CategoryTheory.Abelian.Ext.{w} X Y n) :=
  AddCommGrpCat.ofHom
    ((CategoryTheory.Abelian.Ext.mk₀ f).precomp Y (zero_add n))

/-- Contravariant derived-Ext sends an identity to an identity. -/
@[simp]
theorem derivedExtContravariantMap_id (X Y : C) (n : ℕ) :
    derivedExtContravariantMap (𝟙 X) Y n = 𝟙 _ := by
  ext x
  dsimp [derivedExtContravariantMap]
  exact CategoryTheory.Abelian.Ext.mk₀_id_comp x

/-- Composition law for the contravariant maps on derived Ext. -/
@[reassoc]
theorem derivedExtContravariantMap_comp
    {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (Y : C) (n : ℕ) :
    derivedExtContravariantMap g Y n ≫
        derivedExtContravariantMap f Y n =
      derivedExtContravariantMap (f ≫ g) Y n := by
  ext x
  dsimp [derivedExtContravariantMap]
  change
    (CategoryTheory.Abelian.Ext.mk₀ f).comp
        ((CategoryTheory.Abelian.Ext.mk₀ g).comp x (zero_add n))
        (zero_add n) =
      (CategoryTheory.Abelian.Ext.mk₀ (f ≫ g)).comp x (zero_add n)
  rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc]

/-- Contravariant derived-Ext maps carry a commutative square in the first
argument to a commutative square of Ext groups. -/
theorem derivedExtContravariantMap_square
    {X₁ X₂ X₁' X₂' : C}
    (a : X₁ ⟶ X₂) (b : X₁' ⟶ X₂')
    (f₁ : X₁ ⟶ X₁') (f₂ : X₂ ⟶ X₂')
    (hsq : f₁ ≫ b = a ≫ f₂) (Y : C) (n : ℕ) :
    AddCommGrpCat.ofHom
          ((CategoryTheory.Abelian.Ext.mk₀ b).precomp Y (zero_add n)) ≫
        derivedExtContravariantMap f₁ Y n =
      derivedExtContravariantMap f₂ Y n ≫
        AddCommGrpCat.ofHom
          ((CategoryTheory.Abelian.Ext.mk₀ a).precomp Y (zero_add n)) := by
  ext x
  dsimp [derivedExtContravariantMap]
  change
    (CategoryTheory.Abelian.Ext.mk₀ f₁).comp
        ((CategoryTheory.Abelian.Ext.mk₀ b).comp x (zero_add n))
        (zero_add n) =
      (CategoryTheory.Abelian.Ext.mk₀ a).comp
        ((CategoryTheory.Abelian.Ext.mk₀ f₂).comp x (zero_add n))
        (zero_add n)
  rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc,
    CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc]
  rw [hsq]

/-- The connecting morphism in the contravariant derived-Ext sequence is
natural in morphisms of short exact complexes. -/
theorem derivedExtConnectingMap_naturality
    {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)
    (Y : C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    AddCommGrpCat.ofHom (h₂.extClass.precomp Y h) ≫
        derivedExtContravariantMap f.τ₃ Y n₁ =
      derivedExtContravariantMap f.τ₁ Y n₀ ≫
        AddCommGrpCat.ofHom (h₁.extClass.precomp Y h) := by
  ext x
  dsimp [derivedExtContravariantMap]
  change
    (CategoryTheory.Abelian.Ext.mk₀ f.τ₃).comp
        (h₂.extClass.comp x h) (zero_add n₁) =
      h₁.extClass.comp
        ((CategoryTheory.Abelian.Ext.mk₀ f.τ₁).comp x (zero_add n₀)) h
  calc
    _ = ((CategoryTheory.Abelian.Ext.mk₀ f.τ₃).comp h₂.extClass
          (zero_add 1)).comp x h := by
        symm
        apply CategoryTheory.Abelian.Ext.comp_assoc
        omega
    _ = (h₁.extClass.comp (CategoryTheory.Abelian.Ext.mk₀ f.τ₁)
          (add_zero 1)).comp x h := by
        rw [h₁.extClass_naturality h₂ f]
    _ = _ := by
        apply CategoryTheory.Abelian.Ext.comp_assoc
        omega

/-- A morphism of short exact complexes induces, contravariantly, a morphism
between their six-term derived-Ext sequences. -/
def derivedExtContravariantSequenceMap
    {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)
    (Y : C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    CategoryTheory.Abelian.Ext.contravariantSequence h₂ Y n₀ n₁ h ⟶
      CategoryTheory.Abelian.Ext.contravariantSequence h₁ Y n₀ n₁ h :=
  ComposableArrows.homMk₅
    (derivedExtContravariantMap f.τ₃ Y n₀)
    (derivedExtContravariantMap f.τ₂ Y n₀)
    (derivedExtContravariantMap f.τ₁ Y n₀)
    (derivedExtContravariantMap f.τ₃ Y n₁)
    (derivedExtContravariantMap f.τ₂ Y n₁)
    (derivedExtContravariantMap f.τ₁ Y n₁)
    (derivedExtContravariantMap_square S₁.g S₂.g f.τ₂ f.τ₃
      f.comm₂₃ Y n₀)
    (derivedExtContravariantMap_square S₁.f S₂.f f.τ₁ f.τ₂
      f.comm₁₂ Y n₀)
    (derivedExtConnectingMap_naturality h₁ h₂ f Y n₀ n₁ h)
    (derivedExtContravariantMap_square S₁.g S₂.g f.τ₂ f.τ₃
      f.comm₂₃ Y n₁)
    (derivedExtContravariantMap_square S₁.f S₂.f f.τ₁ f.τ₂
      f.comm₁₂ Y n₁)

/-- The contravariant map of six-term sequences induced by an identity is
the identity. -/
@[simp]
theorem derivedExtContravariantSequenceMap_id
    {S : ShortComplex C} (hS : S.ShortExact)
    (Y : C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    derivedExtContravariantSequenceMap hS hS (𝟙 S) Y n₀ n₁ h = 𝟙 _ := by
  apply ComposableArrows.hom_ext₅
  · change derivedExtContravariantMap (𝟙 S.X₃) Y n₀ = 𝟙 _
    exact derivedExtContravariantMap_id S.X₃ Y n₀
  · change derivedExtContravariantMap (𝟙 S.X₂) Y n₀ = 𝟙 _
    exact derivedExtContravariantMap_id S.X₂ Y n₀
  · change derivedExtContravariantMap (𝟙 S.X₁) Y n₀ = 𝟙 _
    exact derivedExtContravariantMap_id S.X₁ Y n₀
  · change derivedExtContravariantMap (𝟙 S.X₃) Y n₁ = 𝟙 _
    exact derivedExtContravariantMap_id S.X₃ Y n₁
  · change derivedExtContravariantMap (𝟙 S.X₂) Y n₁ = 𝟙 _
    exact derivedExtContravariantMap_id S.X₂ Y n₁
  · change derivedExtContravariantMap (𝟙 S.X₁) Y n₁ = 𝟙 _
    exact derivedExtContravariantMap_id S.X₁ Y n₁

/-- Composition law for the contravariant maps of six-term sequences. -/
@[reassoc]
theorem derivedExtContravariantSequenceMap_comp
    {S₁ S₂ S₃ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (h₃ : S₃.ShortExact)
    (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃)
    (Y : C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    derivedExtContravariantSequenceMap h₂ h₃ g Y n₀ n₁ h ≫
        derivedExtContravariantSequenceMap h₁ h₂ f Y n₀ n₁ h =
      derivedExtContravariantSequenceMap h₁ h₃ (f ≫ g) Y n₀ n₁ h := by
  apply ComposableArrows.hom_ext₅
  · change derivedExtContravariantMap g.τ₃ Y n₀ ≫
      derivedExtContravariantMap f.τ₃ Y n₀ =
        derivedExtContravariantMap (f.τ₃ ≫ g.τ₃) Y n₀
    exact derivedExtContravariantMap_comp f.τ₃ g.τ₃ Y n₀
  · change derivedExtContravariantMap g.τ₂ Y n₀ ≫
      derivedExtContravariantMap f.τ₂ Y n₀ =
        derivedExtContravariantMap (f.τ₂ ≫ g.τ₂) Y n₀
    exact derivedExtContravariantMap_comp f.τ₂ g.τ₂ Y n₀
  · change derivedExtContravariantMap g.τ₁ Y n₀ ≫
      derivedExtContravariantMap f.τ₁ Y n₀ =
        derivedExtContravariantMap (f.τ₁ ≫ g.τ₁) Y n₀
    exact derivedExtContravariantMap_comp f.τ₁ g.τ₁ Y n₀
  · change derivedExtContravariantMap g.τ₃ Y n₁ ≫
      derivedExtContravariantMap f.τ₃ Y n₁ =
        derivedExtContravariantMap (f.τ₃ ≫ g.τ₃) Y n₁
    exact derivedExtContravariantMap_comp f.τ₃ g.τ₃ Y n₁
  · change derivedExtContravariantMap g.τ₂ Y n₁ ≫
      derivedExtContravariantMap f.τ₂ Y n₁ =
        derivedExtContravariantMap (f.τ₂ ≫ g.τ₂) Y n₁
    exact derivedExtContravariantMap_comp f.τ₂ g.τ₂ Y n₁
  · change derivedExtContravariantMap g.τ₁ Y n₁ ≫
      derivedExtContravariantMap f.τ₁ Y n₁ =
        derivedExtContravariantMap (f.τ₁ ≫ g.τ₁) Y n₁
    exact derivedExtContravariantMap_comp f.τ₁ g.τ₁ Y n₁

variable {D : Type*} [Category D]

/-- An objectwise short exact diagram gives a contravariant diagram of its
six-term derived-Ext sequences. -/
def derivedExtContravariantSequenceDiagram
    (F : D ⥤ ShortComplex C) (hF : ∀ d, (F.obj d).ShortExact)
    (Y : C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    Dᵒᵖ ⥤ ComposableArrows AddCommGrpCat.{w} 5 where
  obj d := CategoryTheory.Abelian.Ext.contravariantSequence
    (hF (unop d)) Y n₀ n₁ h
  map {d e} f := derivedExtContravariantSequenceMap
    (hF (unop e)) (hF (unop d)) (F.map f.unop) Y n₀ n₁ h
  map_id d := by
    dsimp
    rw [F.map_id]
    apply derivedExtContravariantSequenceMap_id
  map_comp f g := by
    dsimp
    rw [F.map_comp]
    symm
    apply derivedExtContravariantSequenceMap_comp

/-- Each six-term sequence in the contravariant diagram is exact. -/
theorem derivedExtContravariantSequenceDiagram_obj_exact
    (F : D ⥤ ShortComplex C) (hF : ∀ d, (F.obj d).ShortExact)
    (Y : C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) (d : Dᵒᵖ) :
    ((derivedExtContravariantSequenceDiagram F hF Y n₀ n₁ h).obj d).Exact :=
  CategoryTheory.Abelian.Ext.contravariantSequence_exact
    (hF (unop d)) Y n₀ n₁ h

end ContravariantSequence

section IdealPowers

variable {R : Type u} [CommRing R]

/-- The exact six-term derived-Ext sequences of the ideal-quotient
Mayer--Vietoris complexes, assembled along simultaneous powers of `I` and
`J`. The index category is the opposite of the quotient-complex powers
diagram because Ext is contravariant in its first argument. -/
def idealQuotientMayerVietorisDerivedExtPowersDiagram
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (ℕᵒᵖ)ᵒᵖ ⥤ ComposableArrows AddCommGrpCat.{u} 5 :=
  derivedExtContravariantSequenceDiagram
    (idealQuotientMayerVietorisPowersDiagram I J)
    (idealQuotientMayerVietorisPowersDiagram_obj_shortExact I J)
    M n₀ n₁ h

/-- Every object of the powers-derived-Ext diagram is an exact six-term
sequence. -/
theorem idealQuotientMayerVietorisDerivedExtPowersDiagram_obj_exact
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) (d : (ℕᵒᵖ)ᵒᵖ) :
    ((idealQuotientMayerVietorisDerivedExtPowersDiagram
      I J M n₀ n₁ h).obj d).Exact :=
  derivedExtContravariantSequenceDiagram_obj_exact
    (idealQuotientMayerVietorisPowersDiagram I J)
    (idealQuotientMayerVietorisPowersDiagram_obj_shortExact I J)
    M n₀ n₁ h d

end IdealPowers

end EtaleFundamentalGroups

end
