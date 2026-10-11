/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.NormalizationStrictResidueAction
import EtaleFundamentalGroups.StrictHenselian.OriginalUnramifiedInertiaKernel
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.FieldTheory.Galois.Infinite

/-!
# The original local Galois diagram

The independently constructed maximal unramified subfield and the residue
of the actual strict stalk give the lower vertices. The literal restriction
from the original Galois group descends through the proved decomposition
residue quotient. Both vertical maps retain their original kernels.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia SchemeTheory

universe u v w

private theorem existsUnique_descend_groupHom
    {G : Type u} {H : Type v} {J : Type w} [Group G] [Group H] [Group J]
    (r : G →* H) (hr : Function.Surjective r) (f : G →* J) (hker : r.ker ≤ f.ker) :
    ∃! lower : H →* J, lower.comp r = f := by
  let e : G ⧸ r.ker ≃* H := QuotientGroup.quotientKerEquivOfSurjective r hr
  let lift : G ⧸ r.ker →* J := QuotientGroup.lift r.ker f hker
  let lower : H →* J := lift.comp e.symm.toMonoidHom
  have hcommutes : lower.comp r = f := by
    apply MonoidHom.ext
    intro d
    have he : e (QuotientGroup.mk d) = r d := rfl
    have hinverse : e.symm (r d) = QuotientGroup.mk d :=
      (congrArg e.symm he).symm.trans (e.symm_apply_apply (QuotientGroup.mk d))
    exact (congrArg lift hinverse).trans (QuotientGroup.lift_mk r.ker hker d)
  refine ⟨lower, hcommutes, ?_⟩
  intro other hother
  apply MonoidHom.ext
  intro x
  obtain ⟨d, rfl⟩ := hr x
  exact (DFunLike.congr_fun hother d).trans (DFunLike.congr_fun hcommutes d).symm

attribute [local instance] normalizationCommAlgGaloisAction

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [hQmax : Q.IsMaximal]

/-- The original local Galois square has surjective vertical arrows with
kernels I and the closed normal closure of I. Its lower arrow is uniquely
specified by the original decomposition inclusion and field restriction. -/
theorem exists_unique_originalLocalGaloisDiagram :
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
    let Rsh := IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
    let : IsGalois K (maximalUnramifiedSubfield A K L) :=
      maximalUnramifiedSubfield_isGalois A K L
    let residueMap := normalizationStrictResidueHom A K L Q
    let restriction := AlgEquiv.restrictNormalHom (maximalUnramifiedSubfield A K L)
    Function.Surjective residueMap ∧
      residueMap.ker = (actualNormalizationInertiaToDecomposition A K L nativeQ).range ∧
      Function.Surjective restriction ∧
      restriction.ker = ProCGroups.Presentations.Subgroup.closedNormalClosure
        (Q.inertia Gal(L/K) : Set Gal(L/K)) ∧
      ∃! lower : Gal(Rsh/IsLocalRing.ResidueField A) →*
          Gal(maximalUnramifiedSubfield A K L/K),
        lower.comp residueMap =
          restriction.comp (normalizationDecompositionInclusion A K L nativeQ) := by
  intro actualNormalizationAction nativeQ actualNativeMax actualAlgebraic actualFaithful
    actualHenselian
    actualSepClosed actualLocal actualQuotientAlgebra actualLocalizationAlgebra φ
    actualStructureAlgebra actualStructureLocal Rsh actualUnramifiedGalois
    residueMap restriction
  have hresidue := normalizationStrictResidue_exact A K L Q
  have hrestriction : restriction.ker = ProCGroups.Presentations.Subgroup.closedNormalClosure
      (Q.inertia Gal(L/K) : Set Gal(L/K)) :=
    (maximalUnramifiedSubfield A K L).restrictNormalHom_ker.trans
      (maximalUnramifiedSubfield_fixingSubgroup_eq_normalClosureInertia A K L Q)
  let inclusion := normalizationDecompositionInclusion A K L nativeQ
  let f := restriction.comp inclusion
  have hdescend : residueMap.ker ≤ f.ker := by
    intro d hd
    rw [hresidue.2.2] at hd
    obtain ⟨σ, hσ⟩ := hd
    have hσI : inclusion d ∈ Q.inertia Gal(L/K) := by
      rw [← hσ]
      exact σ.property
    have hσN := ProCGroups.Presentations.subset_closedNormalClosure
      (Q.inertia Gal(L/K) : Set Gal(L/K)) hσI
    have hσker : inclusion d ∈ restriction.ker := hrestriction.symm ▸ hσN
    exact hσker
  have hsurjective : Function.Surjective restriction :=
    AlgEquiv.restrictNormalHom_surjective (F := K)
      (K₁ := maximalUnramifiedSubfield A K L) L
  exact ⟨hresidue.2.1, hresidue.2.2, hsurjective, hrestriction,
    existsUnique_descend_groupHom residueMap hresidue.2.1 f hdescend⟩

end EtaleFundamentalGroups.StrictHenselian
