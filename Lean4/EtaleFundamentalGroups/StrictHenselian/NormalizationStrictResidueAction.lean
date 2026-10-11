/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualNormalizationResidueAction
import EtaleFundamentalGroups.Inertia.NativeResidueRingAction
import EtaleFundamentalGroups.Inertia.NormalizationSeparableResidueSequence
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkResidue
import SchemeTheory.RingTheory.Ramification.NativeMaximalResidue
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The original decomposition action on the actual strict-stalk residue

The proved residue equivalence transports the original separable-residue
homomorphism to the residue field of the actual strict stalk. Its coefficient
formula is the original normalization residue action in κ(B_Q). Its kernel
and surjectivity are the already proved original inertia/decomposition sequence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia SchemeTheory

universe u v w

attribute [local instance] normalizationCommAlgGaloisAction

private theorem quotientResidueEquiv_eq
    (B : Type u) [CommRing B] (q : Ideal B) [q.IsMaximal] :
    (IsLocalization.AtPrime.equivQuotMaximalIdeal q (Localization.AtPrime q)).toRingEquiv =
      maximalQuotientResidueEquiv q := by
  apply RingEquiv.toRingHom_injective
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro b
  exact (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk q
    (Localization.AtPrime q) b).trans
      (RingHom.congr_fun (maximalQuotientResidueEquiv_comp_quotient q) b).symm

private theorem nativeResidueRingHom_equiv
    {A : Type u} [CommRing A] (B : CommAlgCat.{w} A) (q : Ideal B.carrier) [q.IsMaximal]
    (ρ : (nativeAlgebraResidueAutomorphisms B q).carrier) (z : B.carrier ⧸ q) :
    maximalQuotientResidueEquiv q (nativeAlgebraResidueAutomorphismRingEquiv B q ρ z) =
      nativeAlgebraResidueRingHom B q ρ (maximalQuotientResidueEquiv q z) := by
  let e := maximalQuotientResidueEquiv q
  let τ := nativeAlgebraResidueAutomorphismRingEquiv B q ρ
  change e (τ z) = e (τ (e.symm (e z)))
  exact congrArg (fun y => e (τ y)) (e.symm_apply_apply z).symm

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [hQmax : Q.IsMaximal]

/-- The original decomposition group acts on the residue of the actual strict
stalk through the constructed separable-residue comparison. -/
def normalizationStrictResidueHom :
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
    (normalizationDecompositionGroup A K L nativeQ).carrier →*
      Gal(Rsh/IsLocalRing.ResidueField A) := by
  intro nativeQ actualNativeMax actualAlgebraic actualFaithful actualHenselian
    actualSepClosed actualLocal actualQuotientAlgebra actualLocalizationAlgebra φ
    actualStructureAlgebra actualStructureLocal Rsh
  let e : Rsh ≃ₐ[IsLocalRing.ResidueField A]
      separableClosure (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A L nativeQ).α :=
    normalizationPrimeStalkResidueEquiv A K L Q
  let r : (normalizationDecompositionGroup A K L nativeQ).carrier →*
      Gal(separableClosure (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A L nativeQ).α/IsLocalRing.ResidueField A) :=
    (normalizationSeparableResidueMorphism A K L nativeQ).hom'
  exact (AlgEquiv.autCongr e.symm).toMonoidHom.comp r

/-- The same original I-to-D inclusion and the actual strict-residue action
are exact, and the latter is surjective. -/
theorem normalizationStrictResidue_exact :
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
    Function.Injective (actualNormalizationInertiaToDecomposition A K L nativeQ).toFun ∧
      Function.Surjective (normalizationStrictResidueHom A K L Q) ∧
        (normalizationStrictResidueHom A K L Q).ker =
          (actualNormalizationInertiaToDecomposition A K L nativeQ).range := by
  intro nativeQ actualNativeMax actualAlgebraic actualFaithful actualHenselian
    actualSepClosed actualLocal actualQuotientAlgebra actualLocalizationAlgebra φ
    actualStructureAlgebra actualStructureLocal
  let Rsh := IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
  let e : Rsh ≃ₐ[IsLocalRing.ResidueField A]
      separableClosure (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A L nativeQ).α :=
    normalizationPrimeStalkResidueEquiv A K L Q
  let r : (normalizationDecompositionGroup A K L nativeQ).carrier →*
      Gal(separableClosure (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A L nativeQ).α/IsLocalRing.ResidueField A) :=
    (normalizationSeparableResidueMorphism A K L nativeQ).hom'
  refine ⟨actualNormalizationInertiaToDecomposition_injective A K L nativeQ, ?_, ?_⟩
  · exact (AlgEquiv.autCongr e.symm).surjective.comp
      (normalizationSeparableResidueMorphism_surjective A K L nativeQ)
  · exact (MonoidHom.ker_comp_of_injective r (AlgEquiv.autCongr e.symm).toMonoidHom
      (AlgEquiv.autCongr e.symm).injective).trans
        (normalizationSeparableResidueMorphism_ker A K L nativeQ)

/-- On the original κ(B_Q), the strict-residue action is exactly the existing
normalization residue action. This is the coefficient square used by the
actual generic/residue fiber comparison. -/
theorem normalizationStrictResidueHom_coefficient :
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
    ∀ (d : (normalizationDecompositionGroup A K L nativeQ).carrier) (x : Rsh),
      geometricStalkResidueEmbedding (Spec.map (CommRingCat.ofHom φ))
          (normalizationStrictResidueHom A K L Q d x) =
        actualNormalizationResidueFieldMap A K L nativeQ d
          (geometricStalkResidueEmbedding (Spec.map (CommRingCat.ofHom φ)) x) := by
  intro nativeQ actualNativeMax actualAlgebraic actualFaithful actualHenselian
    actualSepClosed actualLocal actualQuotientAlgebra actualLocalizationAlgebra φ
    actualStructureAlgebra actualStructureLocal Rsh d x
  let e : Rsh ≃ₐ[IsLocalRing.ResidueField A]
      separableClosure (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A L nativeQ).α :=
    normalizationPrimeStalkResidueEquiv A K L Q
  let r : (normalizationDecompositionGroup A K L nativeQ).carrier →*
      Gal(separableClosure (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A L nativeQ).α/IsLocalRing.ResidueField A) :=
    (normalizationSeparableResidueMorphism A K L nativeQ).hom'
  let eQ : (normalizationResidueFieldObject A L nativeQ).α ≃ₐ[
      IsLocalRing.ResidueField A] Q.ResidueField := normalizationResidueLocalizationAlgEquiv A L Q
  have heQ : eQ.toRingEquiv = maximalQuotientResidueEquiv nativeQ :=
    quotientResidueEquiv_eq (integralClosure A L) Q
  have heQvalue (z : (normalizationResidueFieldObject A L nativeQ).α) :
      eQ z = maximalQuotientResidueEquiv nativeQ z :=
    congrArg (fun f : (normalizationResidueFieldObject A L nativeQ).α ≃+* Q.ResidueField => f z) heQ
  let action : Q.ResidueField →+* Q.ResidueField :=
    actualNormalizationResidueFieldMap A K L nativeQ d
  let ρ := (normalizationResidueMorphism A K L nativeQ).hom' d
  have htransport (z : (normalizationResidueFieldObject A L nativeQ).α) :
      eQ (normalizationResidueActionScalar A L nativeQ ρ z) =
        action (eQ z) :=
    (heQvalue (normalizationResidueActionScalar A L nativeQ ρ z)).trans
      ((nativeResidueRingHom_equiv (normalizationCommAlgCat A L) nativeQ ρ z).trans
        (congrArg (actualNormalizationResidueFieldMap A K L nativeQ d) (heQvalue z).symm))
  have hconj : e (normalizationStrictResidueHom A K L Q d x) = r d (e x) := by
    change e (e.symm (r d (e x))) = r d (e x)
    exact e.apply_symm_apply _
  let coeff := nativeSeparableResidueScalar (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A L nativeQ) (normalizationResidueFieldAlgebra A L nativeQ)
  have hrestriction : coeff (r d (e x)) =
      normalizationResidueActionScalar A L nativeQ ρ (coeff (e x)) :=
    normalizationSeparableResidueIso_commutes A K L nativeQ ρ (e x)
  have hcoefficient (y : Rsh) :
      (eQ (coeff (e y)) : Q.ResidueField) =
        geometricStalkResidueEmbedding (Spec.map (CommRingCat.ofHom φ)) y :=
    normalizationPrimeStalkResidueEquiv_comp A K L Q y
  have haction :
      (eQ (coeff (e (normalizationStrictResidueHom A K L Q d x))) : Q.ResidueField) =
        action (geometricStalkResidueEmbedding (Spec.map (CommRingCat.ofHom φ)) x) :=
    (congrArg (fun y => eQ (coeff y)) hconj).trans
      ((congrArg eQ hrestriction).trans
        ((htransport (coeff (e x))).trans (congrArg action (hcoefficient x))))
  exact (hcoefficient (normalizationStrictResidueHom A K L Q d x)).symm.trans haction

end EtaleFundamentalGroups.StrictHenselian
