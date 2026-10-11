/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Boundary.ArithmeticComponentBranch
import EtaleFundamentalGroups.LocalGeometry.HeightOne.ComponentFunctionField
import EtaleFundamentalGroups.LocalGeometry.HeightOne.LocalizationGeometricIntegrality

/-!
# Residue fields of specialized arithmetic component branches

The residue field of the canonical height-one branch at any specialization
is canonically the residue field at the component generic point.  Consequently
the geometric-integrality conclusion in the arithmetic boundary condition is
available at the actual prime used in local inertia calculations.
-/

noncomputable section


open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u

variable {X S : Scheme.{u}}

/-- The canonical branch prime at a specialization of an arithmetic boundary
component has a geometrically integral residue field over the generic residue
field of the base. -/
theorem
    galoisPullback_componentBranchPrime_exists_geometricallyIntegralResidueAlgebra
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme)
    (z : (D.1.comap Y.hom).subscheme) (hz : z ∈ Z) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    let q := (I.componentBranchPrimeAt Z hZ z hz).asIdeal
    letI : q.IsPrime := (I.componentBranchPrimeAt Z hZ z hz).isPrime
    let k := S.residueField (genericPoint S)
    ∃ hAlg : Algebra k q.ResidueField,
      letI : Algebra k q.ResidueField := hAlg
      GeometricallyIntegral
        (Spec.map (CommRingCat.ofHom
          (algebraMap k q.ResidueField))) := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
  let I : Y.left.IdealSheafData := D.1.comap Y.hom
  let x := I.componentGenericPoint Z hZ
  let x₀ : Y.left := I.subschemeι z
  let b := I.componentBranchPrimeAt Z hZ z hz
  let q := b.asIdeal
  let : q.IsPrime := b.isPrime
  let k := S.residueField (genericPoint S)
  obtain ⟨hAlg, hgeo⟩ :=
    D.galoisPullback_componentGenericPoint_exists_geometricallyIntegralResidueAlgebra
      p hD Y hY Z hZ
  let : Algebra k (Y.left.residueField x) := hAlg
  have hb : Y.left.fromSpecStalk x₀ b = x := by
    exact I.fromSpecStalk_componentBranchPrimeAt Z hZ z hz
  let e₀ : Y.left.residueField x ≃+*
      Y.left.residueField (Y.left.fromSpecStalk x₀ b) :=
    (Y.left.residueFieldCongr hb.symm).commRingCatIsoToRingEquiv
  let e : Y.left.residueField x ≃+* q.ResidueField :=
    e₀.trans (Y.left.residueFieldFromSpecStalkEquiv x₀ b)
  let hAlgQ : Algebra k q.ResidueField :=
    (e.toRingHom.comp (algebraMap k (Y.left.residueField x))).toAlgebra
  refine ⟨hAlgQ, ?_⟩
  exact geometricallyIntegral_specMap_transport_ringEquiv' e hgeo

/-- Geometric integrality of the canonical branch residue field persists in
the height-two localization at every containing prime. -/
theorem
    galoisPullback_componentLocalizedBranchPrime_exists_geometricallyIntegralResidueAlgebra
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme)
    (z : (D.1.comap Y.hom).subscheme) (hz : z ∈ Z) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    let A : Type u := Y.left.presheaf.stalk (I.subschemeι z)
    let q : Ideal A := (I.componentBranchPrimeAt Z hZ z hz).asIdeal
    letI : q.IsPrime := (I.componentBranchPrimeAt Z hZ z hz).isPrime
    ∀ (P : Ideal A) [P.IsPrime] (hqP : q ≤ P),
      let qV := q.map (algebraMap A (Localization.AtPrime P))
      letI : qV.IsPrime :=
        Ideal.isPrime_map_of_isLocalizationAtPrime P hqP
      let k := S.residueField (genericPoint S)
      ∃ hAlg : Algebra k qV.ResidueField,
        letI : Algebra k qV.ResidueField := hAlg
        GeometricallyIntegral
          (Spec.map (CommRingCat.ofHom
            (algebraMap k qV.ResidueField))) := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
  let I : Y.left.IdealSheafData := D.1.comap Y.hom
  let A : Type u := Y.left.presheaf.stalk (I.subschemeι z)
  let q : Ideal A := (I.componentBranchPrimeAt Z hZ z hz).asIdeal
  let : q.IsPrime := (I.componentBranchPrimeAt Z hZ z hz).isPrime
  dsimp only
  intro P hP hqP
  let : P.IsPrime := hP
  let qV := q.map (algebraMap A (Localization.AtPrime P))
  let : qV.IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime P hqP
  let k := S.residueField (genericPoint S)
  obtain ⟨hAlg, hgeo⟩ :=
    D.galoisPullback_componentBranchPrime_exists_geometricallyIntegralResidueAlgebra
      p hD Y hY Z hZ z hz
  let : Algebra k q.ResidueField := hAlg
  let e : q.ResidueField ≃+* qV.ResidueField :=
    EtaleFundamentalGroups.localizationAtPrimeMapResidueFieldRingEquiv
      A P q hqP
  let hAlgV : Algebra k qV.ResidueField :=
    (e.toRingHom.comp (algebraMap k q.ResidueField)).toAlgebra
  refine ⟨hAlgV, ?_⟩
  exact EtaleFundamentalGroups.geometricallyIntegral_localizationAtPrimeMapResidueField
    P q hqP hgeo

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
