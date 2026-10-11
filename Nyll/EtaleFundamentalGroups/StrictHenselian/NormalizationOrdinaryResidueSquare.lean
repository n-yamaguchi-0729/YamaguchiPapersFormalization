/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationOrdinaryGenericGalois
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationOrdinaryComparisonComputation
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationSpecializationResidueAction
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationStrictResidueAction
import Nyll.EtaleFundamentalGroups.GeometricFiber.HenselianSpecializationAutomorphism

/-!
# The actual ordinary generic/residue fundamental-group square

Under the canonical specialization and henselian residue comparison, the
actual generic-point image of an original decomposition automorphism is its
already constructed action on the actual strict-stalk residue. Both sides
are compared on the same finite étale geometric points, using the original
ambient and localization-residue automorphisms.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia SchemeTheory
open scoped Pointwise

universe u v

attribute [local instance] normalizationInertiaImageAction

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [hQmax : Q.IsMaximal]
  (hQ : Q.under A = IsLocalRing.maximalIdeal A)

/-- The canonical actual ordinary fundamental-group comparison sends the
actual generic-point map of D to the original strict-residue action of D. -/
theorem normalizationOrdinaryResidueFundamentalGroupEquiv_comp_generic :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).2
    let : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
      integralClosurePrimeBaseMap_isLocalHom A L Q hQ
    let φ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : Algebra A (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap A (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    (normalizationOrdinaryResidueFundamentalGroupEquiv A K L Q hQ).toMonoidHom.comp
        (normalizationOrdinaryGenericGaloisMap A K L Q hQ) =
      normalizationStrictResidueHom A K L Q := by
  intro actualHenselian actualSepClosed actualLocal φ actualStructureAlgebra actualStructureLocal
    actualLocalAlgebra actualAmbientAlgebra
  apply MonoidHom.ext
  intro d
  let H := ordinaryHenselization A
  let R := Localization.AtPrime Q
  let Ω := IsLocalRing.ResidueField R
  let k := IsLocalRing.ResidueField A
  let C := IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
  let nativeQ : Ideal (normalizationCommAlgCat A L).carrier := Q
  have : nativeQ.IsMaximal := hQmax
  let ρ : Ω →+* Ω := actualNormalizationResidueFieldMap A K L nativeQ d
  let σ : Gal(C/k) := normalizationStrictResidueHom A K L Q d
  let a : π₁ᵉᵗ(Spec.algebraMap H L) := normalizationOrdinaryGenericGaloisMap A K L Q hQ d
  let τ : R ≃ₐ[H] R := normalizationDecompositionLocalHenselizationAlgEquiv A K L Q hQ d
  let e : L ≃ₐ[H] L := normalizationDecompositionFieldHenselizationAlgEquiv A K L Q hQ d
  let S := normalizationSpecializationFundamentalGroupEquiv A K L Q hQ
  let E := normalizationClosedResidueGaloisEquiv A K L Q hQ
  let B := integralClosure A L
  have : IsFractionRing B L := integralClosure_isFractionRing_of_fractionField_algebraic A K L
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B L
  have : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  let : Algebra R L := (integralClosurePrimeToAmbientField A K L Q).toAlgebra
  have : IsScalarTower B R L := IsScalarTower.of_algebraMap_eq'
    (integralClosurePrimeToAmbientField_comp_coefficient A K L Q).symm
  have : IsFractionRing R L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl R L
  have : IsScalarTower H R L := IsScalarTower.of_algebraMap_eq' rfl
  have hcompat (r : R) : e (algebraMap R L r) = algebraMap R L (τ r) :=
    RingHom.congr_fun (integralClosurePrimeToAmbientField_comp_decomposition A K L Q d) r
  have haction : (SchemeTheory.residueAlgEquiv H R τ).toRingHom = ρ :=
    normalizationSpecializationResidueAction_eq A K L Q hQ d
  have hambient : e.toRingHom = d.val.toRingHom := rfl
  have hspecialization : S a = henselianSpecializationFundamentalGroupEquiv H R L a :=
    normalizationSpecializationFundamentalGroupEquiv_apply A K L Q hQ a
  have heq : S a = E σ := hspecialization.trans
    (henselianSpecializationFundamentalGroupEquiv_eq_of_point_actions H R L τ e hcompat
      d.val.toRingHom hambient ρ haction a (E σ)
      (normalizationOrdinaryGenericGaloisMap_point A K L Q hQ d)
      (normalizationClosedResidueGaloisEquiv_point A K L Q hQ σ ρ
        (fun z => (normalizationStrictResidueHom_coefficient A K L Q d z).symm)))
  exact (normalizationOrdinaryResidueFundamentalGroupEquiv_apply A K L Q hQ a).trans
    (E.symm_apply_eq.mpr heq)

/-- The actual generic-point map from the original decomposition group is
surjective, with kernel the actual original inertia inclusion. -/
theorem normalizationOrdinaryGenericGaloisMap_exact :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).2
    let : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
      integralClosurePrimeBaseMap_isLocalHom A L Q hQ
    let φ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : Algebra A (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap A (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    Function.Surjective (normalizationOrdinaryGenericGaloisMap A K L Q hQ) ∧
      (normalizationOrdinaryGenericGaloisMap A K L Q hQ).ker =
        (actualNormalizationInertiaToDecomposition A K L Q).range := by
  intro actualHenselian actualSepClosed actualLocal φ actualStructureAlgebra actualStructureLocal
    actualLocalAlgebra actualAmbientAlgebra
  let e := normalizationOrdinaryResidueFundamentalGroupEquiv A K L Q hQ
  let g := normalizationOrdinaryGenericGaloisMap A K L Q hQ
  let r := normalizationStrictResidueHom A K L Q
  have hcomp : e.toMonoidHom.comp g = r :=
    normalizationOrdinaryResidueFundamentalGroupEquiv_comp_generic A K L Q hQ
  have hsurj : Function.Surjective r := (normalizationStrictResidue_exact A K L Q).2.1
  have hker : r.ker = (actualNormalizationInertiaToDecomposition A K L Q).range :=
    (normalizationStrictResidue_exact A K L Q).2.2
  constructor
  · intro x
    obtain ⟨d, hd⟩ := hsurj (e x)
    refine ⟨d, e.injective ?_⟩
    exact (DFunLike.congr_fun hcomp d).trans hd
  · exact (MonoidHom.ker_comp_of_injective g e.toMonoidHom e.injective).symm.trans
      ((congrArg (fun f => f.ker) hcomp).trans hker)

end EtaleFundamentalGroups.StrictHenselian
