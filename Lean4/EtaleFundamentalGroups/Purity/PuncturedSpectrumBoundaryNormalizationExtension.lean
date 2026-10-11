/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.ConnectedNormalizationExtension
import EtaleFundamentalGroups.Purity.ConnectedCoverGenericNormalizationOpenRestriction
import EtaleFundamentalGroups.Purity.FiniteEtaleFromBoundaryStalks
import EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedLefschetzSource
import EtaleFundamentalGroups.FiniteEtale.ConnectedReduction

/-!
# Extending a punctured cover from boundary stalks

For a connected finite-etale cover of the punctured spectrum of a positive-
dimensional Noetherian normal local domain, its canonical function-field
normalization is already finite.  This file combines that finiteness with
the canonical comparison on the punctured locus and the boundary-stalk
criterion for etaleness.  Thus formal etaleness only at points over the
closed complement produces the actual finite-etale extension.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsLocalRing R] [IsNoetherianRing R]
  [IsIntegral (Scheme.puncturedSpectrum R)]

/-- The canonical function-field normalization of a connected punctured
cover is finite etale once its stalk maps over the closed complement are
formally etale. -/
theorem
    connectedPuncturedCoverGenericNormalization_isFiniteEtale_of_boundary_stalkMap_formallyEtale
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (hboundary :
      let j := Scheme.puncturedSpectrumInclusion R
      let z := (connectedCoverGenericComposite W ≫ j).fromNormalization
      ∀ y : (connectedCoverGenericComposite W ≫ j).normalization,
        z y ∉ Scheme.puncturedSpectrumOpen R →
          (z.stalkMap y).hom.FormallyEtale) :
    IsFiniteEtale
      (connectedCoverGenericComposite W ≫
        Scheme.puncturedSpectrumInclusion R).fromNormalization := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : IsNormalIntegral U := inferInstance
  let : IsLocallyNoetherian U := inferInstance
  let : QuasiCompact j := inferInstance
  let : QuasiSeparated j := inferInstance
  let z : (connectedCoverGenericComposite W ≫ j).normalization ⟶ X :=
    (connectedCoverGenericComposite W ≫ j).fromNormalization
  let : IsFinite z :=
    connectedPuncturedCoverGenericNormalization_isFinite R hpos W
  have hrestrictFiniteEtale : IsFiniteEtale (z ∣_ j.opensRange) := by
    change IsFiniteEtale
      ((connectedCoverGenericComposite W ≫ j).fromNormalization ∣_ j.opensRange)
    exact connectedCoverGenericNormalization_restrictOpensRange_isFiniteEtale j W
  have hrestrict : Etale (z ∣_ j.opensRange) :=
    hrestrictFiniteEtale.toEtale
  apply
    (open _root_.EtaleFundamentalGroups in
      isFiniteEtale_of_isFinite_of_restrict_etale_of_boundary_stalkMap_formallyEtale
        z j.opensRange hrestrict)
  simpa only [z, j, Scheme.puncturedSpectrumInclusion,
    Scheme.Opens.opensRange_ι] using hboundary

/-- Formal etaleness at the boundary packages the canonical normalization
as an actual finite-etale extension, together with its canonical restriction
isomorphism to the original punctured cover. -/
noncomputable def connectedPuncturedCoverExtensionOfBoundaryStalks
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (hboundary :
      let j := Scheme.puncturedSpectrumInclusion R
      let z := (connectedCoverGenericComposite W ≫ j).fromNormalization
      ∀ y : (connectedCoverGenericComposite W ≫ j).normalization,
        z y ∉ Scheme.puncturedSpectrumOpen R →
          (z.stalkMap y).hom.FormallyEtale) :
    Σ Z : FiniteEtale (Spec (.of R)),
      (pullback (Scheme.puncturedSpectrumInclusion R)).obj Z ≅ W := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : IsNormalIntegral U := inferInstance
  letI : IsLocallyNoetherian U := inferInstance
  letI : QuasiCompact j := inferInstance
  letI : QuasiSeparated j := inferInstance
  exact connectedCoverExtensionOfNormalization W j
    (connectedPuncturedCoverGenericNormalization_isFiniteEtale_of_boundary_stalkMap_formallyEtale
      R hpos W hboundary)

/-- If the boundary stalk maps of the canonical normalization are formally
etale for every connected punctured cover, then every punctured cover
extends.  The disconnected case is recovered from its finite decomposition
into connected covers. -/
theorem hasPuncturedPurity_of_connected_boundary_stalkMap_formallyEtale
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (hboundary :
      ∀ (W : FiniteEtale (Scheme.puncturedSpectrum R))
        (hW : IsConnected W),
        letI : IsConnected W := hW
        let j := Scheme.puncturedSpectrumInclusion R
        let z := (connectedCoverGenericComposite W ≫ j).fromNormalization
        ∀ y : (connectedCoverGenericComposite W ≫ j).normalization,
          z y ∉ Scheme.puncturedSpectrumOpen R →
            (z.stalkMap y).hom.FormallyEtale) :
    HasPuncturedPurity R := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : ConnectedSpace U := inferInstance
  change (pullback j).EssSurj
  apply pullback_essSurj_of_connected j
  intro W hW
  let : IsConnected W := hW
  let extension := connectedPuncturedCoverExtensionOfBoundaryStalks
    R hpos W (hboundary W hW)
  exact ⟨extension.1, ⟨extension.2⟩⟩

end AlgebraicGeometry.FiniteEtale

end
