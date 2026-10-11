/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomology
import EtaleFundamentalGroups.Purity.IdealQuotientMayerVietorisDerivedExtColimit

/-!
# Exactness in the coefficients of derived local cohomology

For a short exact complex of coefficient modules, the covariant long exact
sequence of derived `Ext` is natural in the first variable.  Applying this
to the quotients by all powers of an ideal gives an objectwise exact diagram.
Exactness of filtered colimits then gives exactness of every adjacent
three-term window after passing to derived local cohomology.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe w v u

section CovariantSequenceNaturality

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Precomposition in the first variable of `Ext` commutes with
postcomposition by a degree-zero morphism in the second variable. -/
theorem derivedExtContravariantMap_postcomp
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    AddCommGrpCat.ofHom
          ((CategoryTheory.Abelian.Ext.mk₀ g).postcomp X' (add_zero n)) ≫
        derivedExtContravariantMap f Y' n =
      derivedExtContravariantMap f Y n ≫
        AddCommGrpCat.ofHom
          ((CategoryTheory.Abelian.Ext.mk₀ g).postcomp X (add_zero n)) := by
  ext x
  dsimp [derivedExtContravariantMap]
  change
    (CategoryTheory.Abelian.Ext.mk₀ f).comp
        (x.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero n))
        (zero_add n) =
      ((CategoryTheory.Abelian.Ext.mk₀ f).comp x (zero_add n)).comp
        (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero n)
  symm
  apply CategoryTheory.Abelian.Ext.comp_assoc
  omega

/-- Precomposition in the first variable of `Ext` commutes with the
connecting morphism of a short exact complex in the second variable. -/
theorem derivedExtContravariantMap_covariantConnecting
    {X X' : C} {S : ShortComplex C} (hS : S.ShortExact)
    (f : X ⟶ X') (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    AddCommGrpCat.ofHom (hS.extClass.postcomp X' h) ≫
        derivedExtContravariantMap f S.X₁ n₁ =
      derivedExtContravariantMap f S.X₃ n₀ ≫
        AddCommGrpCat.ofHom (hS.extClass.postcomp X h) := by
  ext x
  dsimp [derivedExtContravariantMap]
  change
    (CategoryTheory.Abelian.Ext.mk₀ f).comp
        (x.comp hS.extClass h) (zero_add n₁) =
      ((CategoryTheory.Abelian.Ext.mk₀ f).comp x (zero_add n₀)).comp
        hS.extClass h
  symm
  apply CategoryTheory.Abelian.Ext.comp_assoc
  omega

/-- A morphism in the first variable induces a contravariant morphism
between the covariant six-term `Ext` sequences of a fixed short exact
complex. -/
def derivedExtCovariantSequenceMap
    {X X' : C} {S : ShortComplex C} (hS : S.ShortExact) (f : X ⟶ X')
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    CategoryTheory.Abelian.Ext.covariantSequence X' hS n₀ n₁ h ⟶
      CategoryTheory.Abelian.Ext.covariantSequence X hS n₀ n₁ h :=
  ComposableArrows.homMk₅
    (derivedExtContravariantMap f S.X₁ n₀)
    (derivedExtContravariantMap f S.X₂ n₀)
    (derivedExtContravariantMap f S.X₃ n₀)
    (derivedExtContravariantMap f S.X₁ n₁)
    (derivedExtContravariantMap f S.X₂ n₁)
    (derivedExtContravariantMap f S.X₃ n₁)
    (derivedExtContravariantMap_postcomp f S.f n₀)
    (derivedExtContravariantMap_postcomp f S.g n₀)
    (derivedExtContravariantMap_covariantConnecting hS f n₀ n₁ h)
    (derivedExtContravariantMap_postcomp f S.f n₁)
    (derivedExtContravariantMap_postcomp f S.g n₁)

/-- The map of covariant six-term sequences induced by an identity in the
first variable is the identity. -/
@[simp]
theorem derivedExtCovariantSequenceMap_id
    {X : C} {S : ShortComplex C} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    derivedExtCovariantSequenceMap hS (𝟙 X) n₀ n₁ h = 𝟙 _ := by
  apply ComposableArrows.hom_ext₅
  · change derivedExtContravariantMap (𝟙 X) S.X₁ n₀ = 𝟙 _
    apply derivedExtContravariantMap_id
  · change derivedExtContravariantMap (𝟙 X) S.X₂ n₀ = 𝟙 _
    apply derivedExtContravariantMap_id
  · change derivedExtContravariantMap (𝟙 X) S.X₃ n₀ = 𝟙 _
    apply derivedExtContravariantMap_id
  · change derivedExtContravariantMap (𝟙 X) S.X₁ n₁ = 𝟙 _
    apply derivedExtContravariantMap_id
  · change derivedExtContravariantMap (𝟙 X) S.X₂ n₁ = 𝟙 _
    apply derivedExtContravariantMap_id
  · change derivedExtContravariantMap (𝟙 X) S.X₃ n₁ = 𝟙 _
    apply derivedExtContravariantMap_id

/-- Composition law for the contravariant maps between covariant six-term
`Ext` sequences. -/
@[reassoc]
theorem derivedExtCovariantSequenceMap_comp
    {X₁ X₂ X₃ : C} {S : ShortComplex C} (hS : S.ShortExact)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    derivedExtCovariantSequenceMap hS g n₀ n₁ h ≫
        derivedExtCovariantSequenceMap hS f n₀ n₁ h =
      derivedExtCovariantSequenceMap hS (f ≫ g) n₀ n₁ h := by
  apply ComposableArrows.hom_ext₅
  · change derivedExtContravariantMap g S.X₁ n₀ ≫
      derivedExtContravariantMap f S.X₁ n₀ =
        derivedExtContravariantMap (f ≫ g) S.X₁ n₀
    apply derivedExtContravariantMap_comp
  · change derivedExtContravariantMap g S.X₂ n₀ ≫
      derivedExtContravariantMap f S.X₂ n₀ =
        derivedExtContravariantMap (f ≫ g) S.X₂ n₀
    apply derivedExtContravariantMap_comp
  · change derivedExtContravariantMap g S.X₃ n₀ ≫
      derivedExtContravariantMap f S.X₃ n₀ =
        derivedExtContravariantMap (f ≫ g) S.X₃ n₀
    apply derivedExtContravariantMap_comp
  · change derivedExtContravariantMap g S.X₁ n₁ ≫
      derivedExtContravariantMap f S.X₁ n₁ =
        derivedExtContravariantMap (f ≫ g) S.X₁ n₁
    apply derivedExtContravariantMap_comp
  · change derivedExtContravariantMap g S.X₂ n₁ ≫
      derivedExtContravariantMap f S.X₂ n₁ =
        derivedExtContravariantMap (f ≫ g) S.X₂ n₁
    apply derivedExtContravariantMap_comp
  · change derivedExtContravariantMap g S.X₃ n₁ ≫
      derivedExtContravariantMap f S.X₃ n₁ =
        derivedExtContravariantMap (f ≫ g) S.X₃ n₁
    apply derivedExtContravariantMap_comp

variable {D : Type*} [Category D]

/-- A diagram in the first variable gives a contravariant diagram of the
covariant six-term `Ext` sequences of a fixed short exact complex. -/
def derivedExtCovariantSequenceDiagram
    (F : D ⥤ C) {S : ShortComplex C} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Dᵒᵖ ⥤ ComposableArrows AddCommGrpCat.{w} 5 where
  obj d := CategoryTheory.Abelian.Ext.covariantSequence
    (F.obj (unop d)) hS n₀ n₁ h
  map {d e} f := derivedExtCovariantSequenceMap hS
    (F.map f.unop) n₀ n₁ h
  map_id d := by
    dsimp
    rw [F.map_id]
    apply derivedExtCovariantSequenceMap_id
  map_comp f g := by
    dsimp
    rw [F.map_comp]
    symm
    apply derivedExtCovariantSequenceMap_comp

/-- Every object of the diagram of covariant six-term `Ext` sequences is
exact. -/
theorem derivedExtCovariantSequenceDiagram_obj_exact
    (F : D ⥤ C) {S : ShortComplex C} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (d : Dᵒᵖ) :
    ((derivedExtCovariantSequenceDiagram F hS n₀ n₁ h).obj d).Exact :=
  CategoryTheory.Abelian.Ext.covariantSequence_exact
    (F.obj (unop d)) hS n₀ n₁ h

end CovariantSequenceNaturality

section IdealPowers

variable {R : Type u} [CommRing R]

/-- The covariant six-term derived-`Ext` sequences of a short exact
coefficient complex, assembled along all powers of an ideal. -/
def derivedLocalCohomologyCoefficientsPowersSequenceDiagram
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (ℕᵒᵖ)ᵒᵖ ⥤ ComposableArrows AddCommGrpCat.{u} 5 :=
  derivedExtCovariantSequenceDiagram
    (localCohomology.ringModIdeals
      (localCohomology.idealPowersDiagram I))
    hS n₀ n₁ h

/-- Every powers-indexed covariant six-term derived-`Ext` sequence is
exact. -/
theorem derivedLocalCohomologyCoefficientsPowersSequenceDiagram_obj_exact
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (d : (ℕᵒᵖ)ᵒᵖ) :
    ((derivedLocalCohomologyCoefficientsPowersSequenceDiagram
      I hS n₀ n₁ h).obj d).Exact :=
  derivedExtCovariantSequenceDiagram_obj_exact
    (localCohomology.ringModIdeals
      (localCohomology.idealPowersDiagram I))
    hS n₀ n₁ h d

/-- An adjacent three-term window in the powers-indexed covariant
six-term derived-`Ext` sequence. -/
def derivedLocalCohomologyCoefficientsPowersAdjacentShortComplex
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (k : ℕ) (hk : k + 2 ≤ 5) :
    ShortComplex ((ℕᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  exactComposableArrowsDiagramAdjacentShortComplex
    (derivedLocalCohomologyCoefficientsPowersSequenceDiagram
      I hS n₀ n₁ h)
    (derivedLocalCohomologyCoefficientsPowersSequenceDiagram_obj_exact
      I hS n₀ n₁ h)
    k hk

/-- Every adjacent three-term window is exact in the powers-diagram
category. -/
theorem derivedLocalCohomologyCoefficientsPowersAdjacentShortComplex_exact
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (k : ℕ) (hk : k + 2 ≤ 5) :
    (derivedLocalCohomologyCoefficientsPowersAdjacentShortComplex
      I hS n₀ n₁ h k hk).Exact :=
  exactComposableArrowsDiagramAdjacentShortComplex_exact
    (derivedLocalCohomologyCoefficientsPowersSequenceDiagram
      I hS n₀ n₁ h)
    (derivedLocalCohomologyCoefficientsPowersSequenceDiagram_obj_exact
      I hS n₀ n₁ h)
    k hk

/-- The filtered colimits of an adjacent three-term window of the
powers-indexed coefficient sequence. -/
def derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (k : ℕ) (hk : k + 2 ≤ 5) :
    ShortComplex AddCommGrpCat.{u} :=
  shortComplexExactColimit
    (derivedLocalCohomologyCoefficientsPowersAdjacentShortComplex
      I hS n₀ n₁ h k hk)

/-- Filtered colimits preserve exactness of every adjacent three-term
window in the coefficient long exact sequence for derived local cohomology. -/
theorem derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex_exact
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (k : ℕ) (hk : k + 2 ≤ 5) :
    (derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex
      I hS n₀ n₁ h k hk).Exact := by
  let : AB5OfSize.{0, 0} AddCommGrpCat.{u} :=
    AB5OfSize_shrink AddCommGrpCat.{u}
  exact shortComplexExactColimit_exact _
    (derivedLocalCohomologyCoefficientsPowersAdjacentShortComplex_exact
      I hS n₀ n₁ h k hk)

/-- The map on derived local cohomology induced by the first morphism of a
short exact coefficient complex. -/
def derivedLocalCohomologyCoefficientsFirstMap
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) :
    derivedLocalCohomology I S.X₁ n ⟶
      derivedLocalCohomology I S.X₂ n :=
  (derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex
    I hS n (n + 1) rfl 0 (by omega)).f

/-- The map on derived local cohomology induced by the second morphism of a
short exact coefficient complex. -/
def derivedLocalCohomologyCoefficientsSecondMap
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) :
    derivedLocalCohomology I S.X₂ n ⟶
      derivedLocalCohomology I S.X₃ n :=
  (derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex
    I hS n (n + 1) rfl 0 (by omega)).g

/-- The connecting map on derived local cohomology induced by a short exact
coefficient complex. -/
def derivedLocalCohomologyCoefficientsConnectingMap
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) :
    derivedLocalCohomology I S.X₃ n ⟶
      derivedLocalCohomology I S.X₁ (n + 1) :=
  (derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex
    I hS n (n + 1) rfl 1 (by omega)).g

theorem derivedLocalCohomologyCoefficientsFirstMap_comp_secondMap
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) :
    derivedLocalCohomologyCoefficientsFirstMap I hS n ≫
        derivedLocalCohomologyCoefficientsSecondMap I hS n = 0 := by
  exact
    (derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex
      I hS n (n + 1) rfl 0 (by omega)).zero

theorem derivedLocalCohomologyCoefficientsSecondMap_comp_connectingMap
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) :
    derivedLocalCohomologyCoefficientsSecondMap I hS n ≫
        derivedLocalCohomologyCoefficientsConnectingMap I hS n = 0 := by
  exact
    (derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex
      I hS n (n + 1) rfl 1 (by omega)).zero

theorem derivedLocalCohomologyCoefficientsConnectingMap_comp_firstMap
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) :
    derivedLocalCohomologyCoefficientsConnectingMap I hS n ≫
        derivedLocalCohomologyCoefficientsFirstMap I hS (n + 1) = 0 := by
  exact
    (derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex
      I hS n (n + 1) rfl 2 (by omega)).zero

/-- Exactness at the middle coefficient in a fixed degree. -/
theorem derivedLocalCohomologyCoefficients_sameDegree_exact
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk
      (derivedLocalCohomologyCoefficientsFirstMap I hS n)
      (derivedLocalCohomologyCoefficientsSecondMap I hS n)
      (derivedLocalCohomologyCoefficientsFirstMap_comp_secondMap
        I hS n)).Exact := by
  change
    (derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex
      I hS n (n + 1) rfl 0 (by omega)).Exact
  exact derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex_exact
    I hS n (n + 1) rfl 0 (by omega)

/-- Exactness at the last coefficient in degree `n`, immediately before the
connecting morphism. -/
theorem derivedLocalCohomologyCoefficients_beforeConnecting_exact
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk
      (derivedLocalCohomologyCoefficientsSecondMap I hS n)
      (derivedLocalCohomologyCoefficientsConnectingMap I hS n)
      (derivedLocalCohomologyCoefficientsSecondMap_comp_connectingMap
        I hS n)).Exact := by
  change
    (derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex
      I hS n (n + 1) rfl 1 (by omega)).Exact
  exact derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex_exact
    I hS n (n + 1) rfl 1 (by omega)

/-- Exactness immediately after the connecting morphism. -/
theorem derivedLocalCohomologyCoefficients_afterConnecting_exact
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk
      (derivedLocalCohomologyCoefficientsConnectingMap I hS n)
      (derivedLocalCohomologyCoefficientsFirstMap I hS (n + 1))
      (derivedLocalCohomologyCoefficientsConnectingMap_comp_firstMap
        I hS n)).Exact := by
  change
    (derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex
      I hS n (n + 1) rfl 2 (by omega)).Exact
  exact derivedLocalCohomologyCoefficientsAdjacentColimitShortComplex_exact
    I hS n (n + 1) rfl 2 (by omega)

end IdealPowers

end EtaleFundamentalGroups

end
