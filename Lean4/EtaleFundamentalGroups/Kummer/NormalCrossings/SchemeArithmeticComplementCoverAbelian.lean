/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Spectrum.Prime.Defs
import EtaleFundamentalGroups.FiniteEtale.DominantPreimmersionPullbackAbelian
import EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeArithmeticComplementCover
import EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverInertia

/-!
# Abelian covers on local normal-crossings complements

An abelian connected Galois cover of a global divisor complement remains an
abelian connected Galois cover on the principal local chart supplied by a
split normal-crossings equation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}}

/-- Pullback from a global support complement to a local split
normal-crossings chart preserves commutativity of the Galois automorphism
group. -/
theorem pullbackSupportComplementCoverToBoundaryAway_aut_isMulCommutative
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (x : X)
    (P : Spec (X.presheaf.stalk x)) :
    let : P.asIdeal.IsPrime := P.isPrime
    ∀ {r : ℕ}
    (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x)
            (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r})
    (hNC : IsSplitStrictNormalCrossingsAt
      (boundaryProduct t r) t r)
    (W : FiniteEtale I.supportComplement)
    [IsMulCommutative (Aut W)],
    let hf :=
      EtaleFundamentalGroups.Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
        hNC
    letI : IsDomain (Localization.Away (boundaryProduct t r)) :=
      IsLocalization.Away.isDomain
        (Localization.Away (boundaryProduct t r)) hf
    letI : Nonempty I.supportComplement :=
      supportComplement_nonempty_of_localizationAway
        I x P.asIdeal (boundaryProduct t r) hf hboundary
    ∀ hW : IsGalois W,
      let Y := pullbackSupportComplementCoverToBoundaryAway
        I x P t hboundary W
      let hY : IsGalois Y :=
        pullbackSupportComplementCoverToBoundaryAway_isGalois
          I x P t hboundary hNC W hW
      letI : IsGalois Y := hY
      IsMulCommutative (Aut Y) := by
  intro hPPrime r t hboundary hNC W _
  dsimp only
  let hf :=
    EtaleFundamentalGroups.Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
      hNC
  let : IsDomain (Localization.Away (boundaryProduct t r)) :=
    IsLocalization.Away.isDomain
      (Localization.Away (boundaryProduct t r)) hf
  let : Nonempty I.supportComplement :=
    supportComplement_nonempty_of_localizationAway
      I x P.asIdeal (boundaryProduct t r) hf hboundary
  intro hW
  let j := localizationAwayToSupportComplement
    I x P.asIdeal (boundaryProduct t r) hboundary
  let Y := pullbackSupportComplementCoverToBoundaryAway
    I x P t hboundary W
  have hY : IsGalois Y :=
    pullbackSupportComplementCoverToBoundaryAway_isGalois
      I x P t hboundary hNC W hW
  let : IsGalois Y := hY
  let : IsIntegral I.supportComplement :=
    isIntegral_of_isOpenImmersion I.supportComplement.ι
  let : IsNormalIntegral I.supportComplement := inferInstance
  let : IsLocallyNoetherian I.supportComplement := inferInstance
  let : IsPreimmersion j :=
    localizationAwayToSupportComplement_isPreimmersion
      I x P.asIdeal (boundaryProduct t r) hboundary
  let : IsDominant j :=
    localizationAwayToSupportComplement_isDominant
      I x P.asIdeal (boundaryProduct t r) hf hboundary
  let : QuasiCompact j :=
    localizationAwayToSupportComplement_quasiCompact
      I x P.asIdeal (boundaryProduct t r) hboundary
  exact FiniteEtale.pullback_obj_aut_isMulCommutative_of_isPreimmersion_of_isDominant
    j W hW

end AlgebraicGeometry.Scheme.IdealSheafData

end
