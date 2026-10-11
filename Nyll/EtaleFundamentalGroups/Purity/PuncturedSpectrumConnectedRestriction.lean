/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionFieldNormalization
import Nyll.SchemeTheory.Normalization.FiniteNormalSource

/-!
# Restricting connected function-field normalizations

This file compares the normalization in the function field of a connected
finite-etale cover with the cover itself.  The comparison is constructed
from the universal property of relative normalization and checked on affine
charts by the uniqueness of integral closure inside the common function
field.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]

private local instance connectedLeftIntegral
    (W : FiniteEtale X) [IsConnected W] : IsIntegral W.left :=
  EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

private local instance connectedLeftNormal
    (W : FiniteEtale X) [IsConnected W] : IsNormalIntegral W.left :=
  EtaleFundamentalGroups.isNormalIntegral_left_of_isConnected_finiteEtale W

/-- The generic-point morphism of the source of a connected finite-etale
cover. -/
noncomputable def connectedCoverGenericMorphism
    (W : FiniteEtale X) [IsConnected W] :
    Spec (.of W.left.functionField) ⟶ W.left := by
  exact W.left.genericExtensionMorphism W.left.functionField

/-- The generic-point morphism of a connected finite-etale cover, composed
with the cover map to the base. -/
noncomputable def connectedCoverGenericComposite
    (W : FiniteEtale X) [IsConnected W] :
    Spec (.of W.left.functionField) ⟶ X :=
  connectedCoverGenericMorphism W ≫ W.hom

/-- Sections on the inverse image of the top open under the generic
composite identify with the function field of the connected cover. -/
noncomputable def connectedCoverGenericCompositeSectionsIso
    (W : FiniteEtale X) [IsConnected W] :
    Γ(Spec (.of W.left.functionField),
        connectedCoverGenericComposite W ⁻¹ᵁ (⊤ : X.Opens)) ≅
      .of W.left.functionField := by
  letI : Nonempty (⊤ : W.left.Opens) :=
    let y : W.left := Classical.choice (inferInstance : Nonempty W.left)
    ⟨⟨y, by trivial⟩⟩
  change Γ(Spec (.of W.left.functionField),
      connectedCoverGenericMorphism W ⁻¹ᵁ (⊤ : W.left.Opens)) ≅
    .of W.left.functionField
  exact W.left.genericExtensionSectionsIso W.left.functionField
    (⊤ : W.left.Opens)

/-- Under the canonical sections identification, the generic composite on
global sections is the canonical map through the two function fields. -/
theorem connectedCoverGenericCompositeSectionsIso_hom_appTop
    (W : FiniteEtale X) [IsConnected W] (r : Γ(X, ⊤)) :
    letI : Nonempty (⊤ : X.Opens) :=
      ⟨⟨Classical.choice (inferInstance : Nonempty X), by simp⟩⟩
    letI : Algebra X.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    (connectedCoverGenericCompositeSectionsIso W).hom
          ((connectedCoverGenericComposite W).appTop r) =
        algebraMap X.functionField W.left.functionField
          (X.germToFunctionField ⊤ r) := by
  dsimp only
  let : Algebra X.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty X), by simp⟩⟩
  let : Nonempty (⊤ : W.left.Opens) :=
    let y : W.left := Classical.choice (inferInstance : Nonempty W.left)
    ⟨⟨y, by trivial⟩⟩
  let hDense : DenseRange W.hom :=
    EtaleFundamentalGroups.finiteEtale_hom_denseRange_of_isConnected W
  have hGeneric :
      (connectedCoverGenericCompositeSectionsIso W).hom
          ((connectedCoverGenericComposite W).appTop r) =
        W.left.germToFunctionField ⊤ (W.hom.appTop r) := by
    change (W.left.genericExtensionSectionsIso W.left.functionField
        (⊤ : W.left.Opens)).hom
          ((W.left.genericExtensionMorphism W.left.functionField).app
            (⊤ : W.left.Opens) (W.hom.appTop r)) = _
    rw [W.left.genericExtensionSectionsIso_hom_app]
    simp
  rw [hGeneric]
  have hFieldMap :
      (@Scheme.Hom.functionFieldMap X W.left W.hom inferInstance
        (EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W)
          hDense).comp (X.germToFunctionField ⊤).hom =
        (W.left.germToFunctionField ⊤).hom.comp W.hom.appTop.hom :=
    @Scheme.Hom.functionFieldMap_comp_germToFunctionField_top
      X W.left W.hom inferInstance
        (EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W)
          hDense
  have hMap := DFunLike.congr_fun hFieldMap r
  change (@Scheme.Hom.functionFieldMap X W.left W.hom inferInstance
      (EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W)
        hDense) (X.germToFunctionField ⊤ r) =
    W.left.germToFunctionField ⊤ (W.hom.appTop r) at hMap
  change W.left.germToFunctionField ⊤ (W.hom.appTop r) =
    (@Scheme.Hom.functionFieldMap X W.left W.hom inferInstance
      (EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W)
        (EtaleFundamentalGroups.finiteEtale_hom_denseRange_of_isConnected W))
          (X.germToFunctionField ⊤ r)
  simpa only [hDense] using hMap.symm

private noncomputable def connectedCoverGenericNormalizationDesc
    (W : FiniteEtale X) [IsConnected W] :
    (connectedCoverGenericComposite W).normalization ⟶ W.left := by
  let hIntegral : IsIntegralHom W.hom :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType W.hom).mp
      W.prop.toIsFinite |>.1
  exact @Scheme.Hom.normalizationDesc _ _
    (connectedCoverGenericComposite W) inferInstance inferInstance _
    (connectedCoverGenericMorphism W) W.hom hIntegral rfl

private lemma connectedCoverGenericNormalizationDesc_comp
    (W : FiniteEtale X) [IsConnected W] :
    connectedCoverGenericNormalizationDesc W ≫ W.hom =
      (connectedCoverGenericComposite W).fromNormalization := by
  let hIntegral : IsIntegralHom W.hom :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType W.hom).mp
      W.prop.toIsFinite |>.1
  dsimp [connectedCoverGenericNormalizationDesc]
  exact @Scheme.Hom.normalizationDesc_comp _ _
    (connectedCoverGenericComposite W) inferInstance inferInstance _
    (connectedCoverGenericMorphism W) W.hom hIntegral rfl

/-- Relative normalization is unchanged when the source of the morphism is
replaced by an isomorphic scheme. -/
private noncomputable def normalizationSourceIso
    {Y Y' Z : Scheme.{u}} (e : Y ≅ Y') (f : Y' ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] :
    (e.hom ≫ f).normalization ≅ f.normalization := by
  let g : Y ⟶ Z := e.hom ≫ f
  let a : g.normalization ⟶ f.normalization :=
    g.normalizationDesc (e.hom ≫ f.toNormalization)
      f.fromNormalization (by simp [g])
  let b : f.normalization ⟶ g.normalization :=
    f.normalizationDesc (e.inv ≫ g.toNormalization)
      g.fromNormalization (by simp [g])
  refine ⟨a, b, ?_, ?_⟩
  · apply Scheme.Hom.normalization.hom_ext g
      (a ≫ b) (𝟙 _) g.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · simp
  · apply Scheme.Hom.normalization.hom_ext f
      (b ≫ a) (𝟙 _) f.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · simp

@[reassoc (attr := simp)]
private lemma normalizationSourceIso_hom_fromNormalization
    {Y Y' Z : Scheme.{u}} (e : Y ≅ Y') (f : Y' ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] :
    (normalizationSourceIso e f).hom ≫ f.fromNormalization =
      (e.hom ≫ f).fromNormalization := by
  simp [normalizationSourceIso]

private noncomputable def normalizationSourceIsoOfEq
    {Y Y' Z : Scheme.{u}} (e : Y ≅ Y') (f : Y' ⟶ Z) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g]
    [QuasiSeparated g] (h : e.hom ≫ f = g) :
    g.normalization ≅ f.normalization := by
  subst g
  exact normalizationSourceIso e f

@[reassoc (attr := simp)]
private lemma normalizationSourceIsoOfEq_hom_fromNormalization
    {Y Y' Z : Scheme.{u}} (e : Y ≅ Y') (f : Y' ⟶ Z) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g]
    [QuasiSeparated g] (h : e.hom ≫ f = g) :
    (normalizationSourceIsoOfEq e f g h).hom ≫ f.fromNormalization =
      g.fromNormalization := by
  subst g
  exact normalizationSourceIso_hom_fromNormalization e f

private theorem monoFactorIsPullback {Y X S : Scheme.{u}}
    (j : X ⟶ S) [Mono j] (f : Y ⟶ X) :
    IsPullback (𝟙 Y) f (f ≫ j) j :=
  @IsPullback.of_horiz_isIso_mono _ _ Y Y X S
    (𝟙 Y) f (f ≫ j) j inferInstance inferInstance ⟨rfl⟩

private noncomputable def monoFactorPullbackIso {Y X S : Scheme.{u}}
    (j : X ⟶ S) [Mono j] (f : Y ⟶ X) :
    Y ≅ Limits.pullback (f ≫ j) j :=
  (monoFactorIsPullback j f).isoPullback

@[reassoc (attr := simp)]
private lemma monoFactorPullbackIso_hom_snd {Y X S : Scheme.{u}}
    (j : X ⟶ S) [Mono j] (f : Y ⟶ X) :
    (monoFactorPullbackIso j f).hom ≫
      Limits.pullback.snd (f ≫ j) j = f :=
  (monoFactorIsPullback j f).isoPullback_hom_snd

/-- The generic normalization of a connected finite étale cover is the cover itself. -/
theorem connectedCoverGenericNormalizationDesc_isIso
    (W : FiniteEtale X) [IsConnected W] :
    IsIso (connectedCoverGenericNormalizationDesc W) := by
  have : IsFinite W.hom := W.prop.toIsFinite
  exact Scheme.Hom.finiteNormalGenericDesc_isIso (Y := W.left) W.hom

/-- The relative normalization in the function field of a connected
finite-etale cover is canonically the cover itself. -/
noncomputable def connectedCoverGenericNormalizationIso
    (W : FiniteEtale X) [IsConnected W] :
    (connectedCoverGenericComposite W).normalization ≅ W.left :=
  letI := connectedCoverGenericNormalizationDesc_isIso W
  asIso (connectedCoverGenericNormalizationDesc W)

@[reassoc (attr := simp)]
theorem connectedCoverGenericNormalizationIso_inv_fromNormalization
    (W : FiniteEtale X) [IsConnected W] :
    (connectedCoverGenericNormalizationIso W).inv ≫
        (connectedCoverGenericComposite W).fromNormalization =
      W.hom := by
  rw [← connectedCoverGenericNormalizationDesc_comp W]
  change (connectedCoverGenericNormalizationIso W).inv ≫
      (connectedCoverGenericNormalizationIso W).hom ≫ W.hom = W.hom
  simp

/-- If `X` maps smoothly and monomorphically to an ambient scheme, the
normalization of that ambient scheme in the function field of a connected
finite-etale cover restricts canonically to the original cover on `X`. -/
noncomputable def connectedCoverGenericNormalizationPullbackIso
    {S : Scheme.{u}} (W : FiniteEtale X) [IsConnected W]
    (j : X ⟶ S) [Mono j] [Smooth j] [QuasiCompact j]
    [QuasiSeparated j] :
    W.left ≅ Limits.pullback
      (connectedCoverGenericComposite W ≫ j).fromNormalization j := by
  let f : Spec (.of W.left.functionField) ⟶ X :=
    connectedCoverGenericComposite W
  let g : Spec (.of W.left.functionField) ⟶ S := f ≫ j
  let p : Limits.pullback g j ⟶ X := Limits.pullback.snd g j
  let eSource : Spec (.of W.left.functionField) ≅ Limits.pullback g j :=
    monoFactorPullbackIso j f
  let hSource : eSource.hom ≫ p = f := by
    exact monoFactorPullbackIso_hom_snd j f
  let eNormalization : f.normalization ≅ p.normalization :=
    normalizationSourceIsoOfEq eSource p f hSource
  exact (connectedCoverGenericNormalizationIso W).symm ≪≫
    eNormalization ≪≫ asIso (g.normalizationPullback j)

@[reassoc (attr := simp)]
theorem connectedCoverGenericNormalizationPullbackIso_hom_snd
    {S : Scheme.{u}} (W : FiniteEtale X) [IsConnected W]
    (j : X ⟶ S) [Mono j] [Smooth j] [QuasiCompact j]
    [QuasiSeparated j] :
    (connectedCoverGenericNormalizationPullbackIso W j).hom ≫
        Limits.pullback.snd
          (connectedCoverGenericComposite W ≫ j).fromNormalization j =
      W.hom := by
  let f : Spec (.of W.left.functionField) ⟶ X :=
    connectedCoverGenericComposite W
  let g : Spec (.of W.left.functionField) ⟶ S := f ≫ j
  let p : Limits.pullback g j ⟶ X := Limits.pullback.snd g j
  let eSource : Spec (.of W.left.functionField) ≅ Limits.pullback g j :=
    monoFactorPullbackIso j f
  let hSource : eSource.hom ≫ p = f := by
    exact monoFactorPullbackIso_hom_snd j f
  let eNormalization : f.normalization ≅ p.normalization :=
    normalizationSourceIsoOfEq eSource p f hSource
  have hNormalization : eNormalization.hom ≫ p.fromNormalization =
      f.fromNormalization := by
    exact normalizationSourceIsoOfEq_hom_fromNormalization
      eSource p f hSource
  change ((connectedCoverGenericNormalizationIso W).symm ≪≫
      eNormalization ≪≫
        asIso (g.normalizationPullback j)).hom ≫
      Limits.pullback.snd g.fromNormalization j = W.hom
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    Scheme.Hom.normalizationPullback_snd]
  rw [hNormalization]
  dsimp only [f]
  exact connectedCoverGenericNormalizationIso_inv_fromNormalization W

end AlgebraicGeometry.FiniteEtale
