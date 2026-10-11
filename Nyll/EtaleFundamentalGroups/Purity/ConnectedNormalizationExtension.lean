/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedRestriction

/-!
# Packaging connected normalization extensions

For a connected finite-etale cover on a smooth monomorphism, the relative
normalization of the ambient scheme in the cover's function field already
has a canonical restriction isomorphism.  Thus a proof that this one
canonical normalization morphism is finite etale packages the desired
extension object without making any further choice.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X S : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  [IsLocallyNoetherian X]

/-- The canonical relative normalization, packaged as a finite-etale cover
once its finite etaleness has been proved. -/
noncomputable def connectedCoverNormalizationExtension
    (W : FiniteEtale X) [IsConnected W]
    (j : X ⟶ S) [Mono j] [Smooth j] [QuasiCompact j]
    [QuasiSeparated j]
    (hEtale : IsFiniteEtale
      (connectedCoverGenericComposite W ≫ j).fromNormalization) :
    FiniteEtale S :=
  @FiniteEtale.mk S _
    (connectedCoverGenericComposite W ≫ j).fromNormalization hEtale

/-- The canonical normalization extension restricts to the original
connected finite-etale cover. -/
noncomputable def connectedCoverNormalizationExtensionRestrictionIso
    (W : FiniteEtale X) [IsConnected W]
    (j : X ⟶ S) [Mono j] [Smooth j] [QuasiCompact j]
    [QuasiSeparated j]
    (hEtale : IsFiniteEtale
      (connectedCoverGenericComposite W ≫ j).fromNormalization) :
    (pullback j).obj
        (connectedCoverNormalizationExtension W j hEtale) ≅ W :=
  (show W ≅ (pullback j).obj
      (connectedCoverNormalizationExtension W j hEtale) from
    MorphismProperty.Over.isoMk
      (connectedCoverGenericNormalizationPullbackIso W j)
      (connectedCoverGenericNormalizationPullbackIso_hom_snd W j)).symm

/-- Finite etaleness of the canonical normalization is the only remaining
input needed to produce an actual extension and its pullback isomorphism. -/
noncomputable def connectedCoverExtensionOfNormalization
    (W : FiniteEtale X) [IsConnected W]
    (j : X ⟶ S) [Mono j] [Smooth j] [QuasiCompact j]
    [QuasiSeparated j]
    (hEtale : IsFiniteEtale
      (connectedCoverGenericComposite W ≫ j).fromNormalization) :
    Σ Z : FiniteEtale S, (pullback j).obj Z ≅ W :=
  ⟨connectedCoverNormalizationExtension W j hEtale,
    connectedCoverNormalizationExtensionRestrictionIso W j hEtale⟩

end AlgebraicGeometry.FiniteEtale
