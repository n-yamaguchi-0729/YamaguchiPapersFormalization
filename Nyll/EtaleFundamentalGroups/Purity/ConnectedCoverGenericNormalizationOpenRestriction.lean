/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.ConnectedCoverGenericNormalizationFinite

/-!
# The canonical normalization on the original open subscheme

The relative normalization attached to a connected finite-etale cover of an
open subscheme restricts to that cover.  In particular, its restriction to
the range of the open immersion is finite etale.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- The canonical function-field normalization restricts to a finite-etale
morphism on the range of the original open immersion. -/
theorem connectedCoverGenericNormalization_restrictOpensRange_isFiniteEtale
    {X U : Scheme.{u}}
    [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (W : FiniteEtale U) [IsConnected W] :
    IsFiniteEtale
      ((connectedCoverGenericComposite W ≫ j).fromNormalization ∣_
        j.opensRange) := by
  let z : (connectedCoverGenericComposite W ≫ j).normalization ⟶ X :=
    (connectedCoverGenericComposite W ≫ j).fromNormalization
  let : MorphismProperty.RespectsIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) := by
    apply MorphismProperty.RespectsIso.mk
    · intro _ _ _ _ f hf
      let : IsFinite f := hf.toIsFinite
      let : Etale f := hf.toEtale
      exact ⟨⟩
    · intro _ _ _ _ f hf
      let : IsFinite f := hf.toIsFinite
      let : Etale f := hf.toEtale
      exact ⟨⟩
  have hpullback : IsFiniteEtale (pullback.snd z j) := by
    let e := connectedCoverGenericNormalizationPullbackIso W j
    apply (MorphismProperty.cancel_left_of_respectsIso
      (P := @IsFiniteEtale) e.hom _).mp
    rw [connectedCoverGenericNormalizationPullbackIso_hom_snd]
    exact W.prop
  exact (MorphismProperty.arrow_mk_iso_iff (@IsFiniteEtale)
    (morphismRestrictOpensRange z j)).mpr hpullback

/-- Ambient normality and local Noetherianity supply the source hypotheses
needed by the finite-etale open-restriction theorem. -/
theorem
    connectedCoverGenericNormalization_restrictOpensRange_isFiniteEtale_of_isOpenImmersion
    {X U : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    [Nonempty U]
    (W : FiniteEtale U) [IsConnected W] :
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : IsNormalIntegral U := IsNormalIntegral.of_isOpenImmersion j
    letI : IsLocallyNoetherian U :=
      isLocallyNoetherian_of_isOpenImmersion j
    IsFiniteEtale
      ((connectedCoverGenericComposite W ≫ j).fromNormalization ∣_
        j.opensRange) := by
  let hUintegral : IsIntegral U := isIntegral_of_isOpenImmersion j
  let hUnormal : @IsNormalIntegral U hUintegral :=
    @IsNormalIntegral.of_isOpenImmersion X U _ _ hUintegral j _
  let hUnoetherian : IsLocallyNoetherian U :=
    isLocallyNoetherian_of_isOpenImmersion j
  exact
    @connectedCoverGenericNormalization_restrictOpensRange_isFiniteEtale
      X U hUintegral hUnormal hUnoetherian j _ _ _ W _

end AlgebraicGeometry.FiniteEtale

end
