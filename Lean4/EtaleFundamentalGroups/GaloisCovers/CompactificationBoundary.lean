/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.ConnectedCoverGenericNormalizationOpenRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The actual normalization compactification and its boundary

The original connected finite étale cover embeds openly in the normalization
of the ambient proper scheme in its own function field. Its complement is
exactly the inverse image of the original boundary. No extension across the
boundary is assumed to be étale.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

open CategoryTheory.PreGaloisCategory

universe u

variable {X U : Scheme.{u}}
  [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
  [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
  (W : FiniteEtale U) [IsConnected W]

/-- The original cover as an open subscheme of the actual normalization. -/
def connectedCoverCompactificationInclusion :
    W.left ⟶ (connectedCoverGenericComposite W ≫ j).normalization :=
  (connectedCoverGenericNormalizationPullbackIso W j).hom ≫
    pullback.fst (connectedCoverGenericComposite W ≫ j).fromNormalization j

instance connectedCoverCompactificationInclusion_isOpenImmersion :
    IsOpenImmersion (connectedCoverCompactificationInclusion j W) := by
  unfold connectedCoverCompactificationInclusion
  infer_instance

omit [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] in
/-- The compactification inclusion commutes with the original covering map. -/
theorem connectedCoverCompactificationInclusion_comp :
    connectedCoverCompactificationInclusion j W ≫
        (connectedCoverGenericComposite W ≫ j).fromNormalization =
      W.hom ≫ j := by
  unfold connectedCoverCompactificationInclusion
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    connectedCoverGenericNormalizationPullbackIso_hom_snd]

omit [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] in
/-- This is the equality of the actual underlying open subsets. -/
theorem range_connectedCoverCompactificationInclusion :
    Set.range (connectedCoverCompactificationInclusion j W) =
      (connectedCoverGenericComposite W ≫ j).fromNormalization ⁻¹' Set.range j := by
  let e := connectedCoverGenericNormalizationPullbackIso W j
  have he : Function.Surjective e.hom := e.hom.homeomorph.surjective
  calc
    Set.range (connectedCoverCompactificationInclusion j W) =
        Set.range (pullback.fst
          (connectedCoverGenericComposite W ≫ j).fromNormalization j) := by
      change Set.range ((pullback.fst
        (connectedCoverGenericComposite W ≫ j).fromNormalization j) ∘ e.hom) = _
      rw [Set.range_comp, Set.range_eq_univ.mpr he, Set.image_univ]
    _ = (connectedCoverGenericComposite W ≫ j).fromNormalization ⁻¹' Set.range j :=
      IsOpenImmersion.range_pullbackFst j _

omit [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] in
/-- Boundary membership is computed by the original boundary, with the
original cover recovered on its full inverse image. -/
theorem not_mem_range_connectedCoverCompactificationInclusion
    (y : (connectedCoverGenericComposite W ≫ j).normalization) :
    y ∉ Set.range (connectedCoverCompactificationInclusion j W) ↔
      (connectedCoverGenericComposite W ≫ j).fromNormalization y ∉ Set.range j := by
  rw [range_connectedCoverCompactificationInclusion]
  rfl

/-- The normalization compactification is genuinely finite over the
ambient scheme, from the finite separable generic extension. -/
theorem connectedCoverCompactification_isFinite :
    IsFinite (connectedCoverGenericComposite W ≫ j).fromNormalization :=
  connectedCoverGenericNormalization_isFinite_of_isOpenImmersion j W

/-- A proper ambient scheme gives an actual proper compactification of
the original finite étale cover. -/
theorem connectedCoverCompactification_isProper
    {B : Scheme.{u}} (c : X ⟶ B) [IsProper c] :
    IsProper ((connectedCoverGenericComposite W ≫ j).fromNormalization ≫ c) := by
  have : IsFinite (connectedCoverGenericComposite W ≫ j).fromNormalization :=
    connectedCoverCompactification_isFinite j W
  infer_instance

end AlgebraicGeometry.FiniteEtale
