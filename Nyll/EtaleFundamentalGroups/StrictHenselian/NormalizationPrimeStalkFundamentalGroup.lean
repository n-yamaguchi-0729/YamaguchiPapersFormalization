/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFundamentalGroupConjugacy
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkFieldTower
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkGaloisRestriction
import Nyll.EtaleFundamentalGroups.StrictHenselian.OriginalFractionFieldGalois

/-!
# The actual strict-generic fundamental group has image original inertia

The existing field-fiber comparison identifies the actual strict-generic
fundamental-group map with scalar restriction. The explicit comparison of
fiber functors accounts for the inner conjugation in the generic scheme
map. The canonical fraction field permits this comparison in the scheme
universe while the original displayed fraction field remains independent.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia

universe u v

attribute [local instance] normalizationInertiaImageAction

/-- Under the explicit geometric-fiber comparison, the image of the actual
strict-generic fundamental-group map is exactly the original inertia group.
The source is the fraction field of the constructed stalk, and the target
comparison preserves the independently supplied original fraction field. -/
theorem geometricStalkFundamentalGroup_originalInertia_range
    (A : Type u) (K : Type v) (L : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [Q.IsMaximal] :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    let ψ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : IsLocalHom ψ := normalizationResiduePoint_isLocalHom A L Q
    let E := FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom ψ)))
    let : Algebra K E := (normalizationStalkFractionBaseMap A K L Q).toAlgebra
    let : Algebra E L := (geometricStalkFractionToNormalizationField A L Q).toAlgebra
    let : IsScalarTower K E L := normalizationStalkFractionField_isScalarTower A K L Q
    let : IsSepClosure E L := normalizationStalkFractionField_isSepClosure A K L Q
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    let : IsSepClosure (FractionRing A) L := originalFractionField_isSepClosure A K L
    let : Algebra (FractionRing A) E := (geometricStalkFractionFieldMap ψ).toAlgebra
    let : IsScalarTower (FractionRing A) E L :=
      normalizationStalkFractionField_isScalarTower A (FractionRing A) L Q
    let comparison :=
      ((fieldBasePointFiberIso (FractionRing A) E L).conjAut.trans
        (MulAut.conj (fieldFundamentalGroupComparisonAut (FractionRing A) E L))).trans
          ((absoluteGaloisToFiberAutMulEquiv (FractionRing A) L inferInstance).symm.trans
            (originalFractionFieldGaloisEquiv A K L))
    (comparison.toMonoidHom.comp
      (fundamentalGroupHom (ξ (FractionRing A) E) (ξ E L)).toMonoidHom).range =
        Q.inertia Gal(L/K) := by
  intro actualAlgebraic actualFaithful actualHenselian actualResidueSepClosed
    ψ actualLocal E actualBaseAlgebra actualAmbientAlgebra actualTower actualSepClosure
    actualFractionAlgebra actualFractionAmbientAlgebra actualFractionSepClosure
    actualCanonicalBaseAlgebra actualCanonicalTower comparison
  let sourceEquiv := absoluteGaloisToFiberAutMulEquiv E L (inferInstance : IsSepClosed L)
  let targetMap := comparison.toMonoidHom.comp
    (fundamentalGroupHom (ξ (FractionRing A) E) (ξ E L)).toMonoidHom
  have hvalue (τ : Gal(L/E)) : targetMap (sourceEquiv τ) = τ.restrictScalars K := by
    change originalFractionFieldGaloisEquiv A K L
      ((absoluteGaloisToFiberAutMulEquiv (FractionRing A) L inferInstance).symm
        (MulAut.conj (fieldFundamentalGroupComparisonAut (FractionRing A) E L)
          ((fieldBasePointFiberIso (FractionRing A) E L).conjAut
            (fundamentalGroupHom (ξ (FractionRing A) E) (ξ E L)
              (absoluteGaloisToFiberAutMulEquiv E L inferInstance τ))))) = _
    rw [← fieldFundamentalGroupHom_eq_conj_fundamentalGroupHom,
      fieldFundamentalGroupHom_toAutMulEquiv, MulEquiv.symm_apply_apply]
    apply AlgEquiv.ext
    intro x
    rfl
  have hrange : (AlgEquiv.restrictScalarsHom K : Gal(L/E) →* Gal(L/K)).range =
      Q.inertia Gal(L/K) := geometricStalkAbsoluteGalois_restriction_range A K L Q
  change targetMap.range = _
  rw [← hrange]
  apply Subgroup.ext
  intro σ
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨τ, rfl⟩ := sourceEquiv.surjective a
    exact ⟨τ, (hvalue τ).symm⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨sourceEquiv τ, hvalue τ⟩

end EtaleFundamentalGroups.StrictHenselian
