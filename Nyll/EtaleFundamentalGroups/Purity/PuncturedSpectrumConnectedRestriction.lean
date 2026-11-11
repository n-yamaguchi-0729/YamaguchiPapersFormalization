/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionFieldNormalization
public import Nyll.SchemeTheory.Normalization.FiniteNormalSource
public import Nyll.SchemeTheory.Normalization.SourceIso
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral

/-!
# Restricting connected function-field normalizations

This file compares the normalization in the function field of a connected
finite-etale cover with the cover itself.  The comparison is constructed
from the universal property of relative normalization and checked on affine
charts by the uniqueness of integral closure inside the common function
field.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]

/-- A connected finite étale cover of an integral normal scheme is integral. -/
local instance connectedLeftIntegral
    (W : FiniteEtale X) [IsConnected W] : IsIntegral W.left :=
  EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W

/-- A connected finite étale cover retains normality of the integral base. -/
local instance connectedLeftNormal
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
  let : Nonempty (⊤ : W.left.Opens) :=
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
    let : Nonempty (⊤ : X.Opens) :=
      ⟨⟨Classical.choice (inferInstance : Nonempty X), by trivial⟩⟩
    let : Algebra X.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    (connectedCoverGenericCompositeSectionsIso W).hom
          ((connectedCoverGenericComposite W).appTop r) =
        algebraMap X.functionField W.left.functionField
          (X.germToFunctionField ⊤ r) := by
  intro sharedOwner1 sharedOwner2
  let : Algebra X.functionField W.left.functionField :=
    sharedOwner2
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
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
    exact Algebra.algebraMap_self_apply _
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

/-- The original finite cover receives the canonical map from its generic normalization. -/
noncomputable def connectedCoverGenericNormalizationDesc
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

/-- Factoring through a monomorphism gives a pullback square with an identity side. -/
theorem monoFactorIsPullback {Y X S : Scheme.{u}}
    (j : X ⟶ S) [Mono j] (f : Y ⟶ X) :
    IsPullback (𝟙 Y) f (f ≫ j) j :=
  @IsPullback.of_horiz_isIso_mono _ _ Y Y X S
    (𝟙 Y) f (f ≫ j) j inferInstance inferInstance ⟨rfl⟩

/-- The source of a map through a monomorphism is its pullback. -/
noncomputable def monoFactorPullbackIso {Y X S : Scheme.{u}}
    (j : X ⟶ S) [Mono j] (f : Y ⟶ X) :
    Y ≅ Limits.pullback (f ≫ j) j :=
  (monoFactorIsPullback j f).isoPullback

/-- The monomorphism pullback identification preserves the original map. -/
@[reassoc (attr := simp)]
lemma monoFactorPullbackIso_hom_snd {Y X S : Scheme.{u}}
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
  let : IsIso (connectedCoverGenericNormalizationDesc W) :=
    connectedCoverGenericNormalizationDesc_isIso W
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
  exact Iso.inv_hom_id_assoc _ _

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
    Scheme.Hom.normalizationSourceIso f p eSource hSource
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
    Scheme.Hom.normalizationSourceIso f p eSource hSource
  have hNormalization : eNormalization.hom ≫ p.fromNormalization =
      f.fromNormalization := by
    exact Scheme.Hom.normalizationSourceIso_hom_fromNormalization
      f p eSource hSource
  change ((connectedCoverGenericNormalizationIso W).symm ≪≫
      eNormalization ≪≫
        asIso (g.normalizationPullback j)).hom ≫
      Limits.pullback.snd g.fromNormalization j = W.hom
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    Scheme.Hom.normalizationPullback_snd]
  rw [hNormalization]
  dsimp only [f]
  exact connectedCoverGenericNormalizationIso_inv_fromNormalization W

/-- The chosen pullback identification preserves the actual generic source. -/
@[reassoc]
theorem connectedCoverGenericMorphism_normalizationPullbackIso_fst
    {S : Scheme.{u}} (W : FiniteEtale X) [IsConnected W]
    (j : X ⟶ S) [Mono j] [Smooth j] [QuasiCompact j]
    [QuasiSeparated j] :
    connectedCoverGenericMorphism W ≫
        (connectedCoverGenericNormalizationPullbackIso W j).hom ≫
        Limits.pullback.fst
          (connectedCoverGenericComposite W ≫ j).fromNormalization j =
      (connectedCoverGenericComposite W ≫ j).toNormalization := by
  let f : Spec (.of W.left.functionField) ⟶ X :=
    connectedCoverGenericComposite W
  let g : Spec (.of W.left.functionField) ⟶ S := f ≫ j
  let p : Limits.pullback g j ⟶ X := Limits.pullback.snd g j
  let eSource : Spec (.of W.left.functionField) ≅ Limits.pullback g j :=
    monoFactorPullbackIso j f
  let hSource : eSource.hom ≫ p = f :=
    monoFactorPullbackIso_hom_snd j f
  let eNormalization : f.normalization ≅ p.normalization :=
    Scheme.Hom.normalizationSourceIso f p eSource hSource
  have hW :
      connectedCoverGenericMorphism W ≫
          (connectedCoverGenericNormalizationIso W).inv =
        f.toNormalization := by
    apply (cancel_mono (connectedCoverGenericNormalizationIso W).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    symm
    let hIntegral : IsIntegralHom W.hom :=
      (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType W.hom).mp
        W.prop.toIsFinite |>.1
    change f.toNormalization ≫ connectedCoverGenericNormalizationDesc W =
      connectedCoverGenericMorphism W
    exact @Scheme.Hom.toNormalization_normalizationDesc _ _
      f inferInstance inferInstance _
      (connectedCoverGenericMorphism W) W.hom hIntegral rfl
  have hfst : eSource.hom ≫ Limits.pullback.fst g j = 𝟙 _ :=
    (monoFactorIsPullback j f).isoPullback_hom_fst
  change connectedCoverGenericMorphism W ≫
      ((connectedCoverGenericNormalizationIso W).symm ≪≫
        eNormalization ≪≫ asIso (g.normalizationPullback j)).hom ≫
      Limits.pullback.fst g.fromNormalization j = g.toNormalization
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [← Category.assoc (connectedCoverGenericMorphism W)
      (connectedCoverGenericNormalizationIso W).inv, hW]
  rw [Scheme.Hom.toNormalization_normalizationSourceIso_hom_assoc f p eSource hSource]
  rw [Scheme.Hom.toNormalization_normalizationPullback_fst]
  rw [← Category.assoc, hfst, Category.id_comp]

end AlgebraicGeometry.FiniteEtale
