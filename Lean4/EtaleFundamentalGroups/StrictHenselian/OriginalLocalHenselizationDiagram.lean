/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.OriginalLocalGaloisDiagram
import EtaleFundamentalGroups.StrictHenselian.NormalizationOrdinaryBaseSquare
import EtaleFundamentalGroups.StrictHenselian.NormalizationOrdinaryResidueSquare
import EtaleFundamentalGroups.StrictHenselian.OriginalUnramifiedGaloisQuotient

/-!
# The original local Galois square from the actual henselizations

The lower arrow is the actual scheme-induced fundamental-group map of the
ordinary henselization over A, transported by the constructed strict-residue
comparison on the left and the independently constructed maximal unramified
field comparison on the right. Both vertical maps are the original residue
and restriction maps, with their proved surjectivity and inertia kernels.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia SchemeTheory

universe u v

attribute [local instance] normalizationCommAlgGaloisAction

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [hQmax : Q.IsMaximal]

/-- The original Galois square is the same diagram as the actual scheme map
from the ordinary henselization. The bottom arrow is displayed as that map,
with the proved actual strict-residue and maximal-unramified comparisons. -/
theorem originalLocalGaloisDiagram_of_actualHenselizations :
    let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
      normalizationInertiaImageAction A K L
    let nativeQ : Ideal (normalizationCommAlgCat A L).carrier := Q
    let : nativeQ.IsMaximal := hQmax
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed Q.ResidueField :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    let : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
      integralClosurePrimeBaseMap_isLocalHom A L Q (integralClosure_maximalPrime_under A L Q)
    let : Algebra (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A L nativeQ).α :=
      normalizationResidueFieldAlgebra A L nativeQ
    let : Algebra (IsLocalRing.ResidueField A) Q.ResidueField :=
      (IsLocalRing.ResidueField.map (integralClosurePrimeBaseMap A L Q)).toAlgebra
    let φ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : Algebra A (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap A (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    let hQ := integralClosure_maximalPrime_under A L Q
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    let : IsSepClosure (FractionRing A) L := originalFractionField_isSepClosure A K L
    let : IsGalois K (maximalUnramifiedSubfield A K L) :=
      maximalUnramifiedSubfield_isGalois A K L
    let residueMap := normalizationStrictResidueHom A K L Q
    let restriction := AlgEquiv.restrictNormalHom (maximalUnramifiedSubfield A K L)
    let ordinaryComparison := normalizationOrdinaryResidueFundamentalGroupEquiv A K L Q hQ
    let schemeMap := normalizationOrdinaryBaseFundamentalGroupHom A K L Q hQ
    Function.Surjective residueMap ∧
      residueMap.ker = (actualNormalizationInertiaToDecomposition A K L nativeQ).range ∧
      Function.Surjective restriction ∧
      restriction.ker = ProCGroups.Presentations.Subgroup.closedNormalClosure
        (Q.inertia Gal(L/K) : Set Gal(L/K)) ∧
      ∃ eM : π₁ᵉᵗ(ξ (FractionRing A) L ≫ Spec.algebraMap A (FractionRing A)) ≃ₜ*
          Gal(maximalUnramifiedSubfield A K L/K),
        (∀ σ : Gal(L/K), eM (originalFractionAbsoluteGaloisHom A K L σ) = restriction σ) ∧
        ((ContinuousMonoidHom.toContinuousMonoidHom eM).comp
          (schemeMap.comp (ContinuousMonoidHom.toContinuousMonoidHom
            ordinaryComparison.symm))).toMonoidHom.comp residueMap =
          restriction.comp (normalizationDecompositionInclusion A K L nativeQ) := by
  intro actualNormalizationAction nativeQ actualNativeMax actualAlgebraic actualFaithful
    actualHenselian actualSepClosed actualLocal actualQuotientAlgebra actualLocalizationAlgebra
    φ actualStructureAlgebra actualStructureLocal hQ actualOrdinaryLocalAlgebra
    actualOrdinaryAmbientAlgebra actualBaseAlgebra actualFractionAlgebra actualSepClosure
    actualUnramifiedGalois residueMap restriction ordinaryComparison schemeMap
  have hdiagram := exists_unique_originalLocalGaloisDiagram A K L Q
  have hM : ∃ eM : π₁ᵉᵗ(ξ (FractionRing A) L ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) ≃ₜ*
          Gal(maximalUnramifiedSubfield A K L/K),
      ∀ σ : Gal(L/K), eM (originalFractionAbsoluteGaloisHom A K L σ) =
        AlgEquiv.restrictNormalHom (maximalUnramifiedSubfield A K L) σ :=
    exists_originalUnramifiedFundamentalGroupEquivGalois A K L
  obtain ⟨eM, heM⟩ := hM
  refine ⟨hdiagram.1, hdiagram.2.1, hdiagram.2.2.1, hdiagram.2.2.2.1, eM, heM, ?_⟩
  apply MonoidHom.ext
  intro d
  let qH := normalizationOrdinaryGenericGaloisMap A K L Q hQ
  let inclusion := normalizationDecompositionInclusion A K L nativeQ
  have hleft : ordinaryComparison (qH d) = residueMap d :=
    DFunLike.congr_fun
      (normalizationOrdinaryResidueFundamentalGroupEquiv_comp_generic A K L Q hQ) d
  have hinverse : ordinaryComparison.symm (residueMap d) = qH d :=
    (congrArg ordinaryComparison.symm hleft).symm.trans
      (ordinaryComparison.symm_apply_apply (qH d))
  have hright : schemeMap (qH d) = originalFractionAbsoluteGaloisHom A K L (inclusion d) :=
    DFunLike.congr_fun
      (normalizationOrdinaryBaseFundamentalGroupHom_comp_generic A K L Q hQ) d
  change eM (schemeMap (ordinaryComparison.symm (residueMap d))) = restriction (inclusion d)
  exact (congrArg (fun x => eM (schemeMap x)) hinverse).trans
    ((congrArg eM hright).trans (heM (inclusion d)))

end EtaleFundamentalGroups.StrictHenselian
