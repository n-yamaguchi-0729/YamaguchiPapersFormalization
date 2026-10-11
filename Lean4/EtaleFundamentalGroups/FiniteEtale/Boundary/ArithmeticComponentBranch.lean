/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Boundary.ArithmeticComponentResidue
import SchemeTheory.Divisors.ComponentStalkBranch
import SchemeTheory.FunctionFields.IntegerBase

/-!
# Height-one branches at arithmetic component specializations

Every component of an arithmetic Galois pullback contains a residue-
characteristic-two normal-crossings point.  The component generic point
determines a canonical height-one prime in the ambient stalk at that point.
-/

noncomputable section


open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u

variable {X S : Scheme.{u}}

/-- A normal-crossings point on each component is already enough to produce
the regular residue-characteristic branch on a finite-etale Galois
pullback.  In particular, regularity at the selected point is not a separate
boundary hypothesis: it descends from the strict-normal-crossings chart. -/
theorem
    galoisPullback_component_exists_residueCharacteristicBranch_of_normalCrossingPoints
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X) (q : ℕ)
    (hD : D.HasNormalCrossingPointOfResidueCharacteristicOnEachComponent q)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    letI : IsLocallyNoetherian Y.left :=
      EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    ∃ (z : I.subscheme) (hz : z ∈ Z),
      let x₀ : Y.left := I.subschemeι z
      let branch := (I.componentBranchPrimeAt Z hZ z hz).asIdeal
      Y.left.IsRegularAt x₀ ∧
        ringChar (Y.left.residueField x₀) = q ∧
          I.IsNormalCrossingsAt x₀ ∧
            branch.height = 1 ∧ I.stalkIdeal x₀ ≤ branch ∧
              branch ≤ IsLocalRing.maximalIdeal (Y.left.presheaf.stalk x₀) := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
  let : IsLocallyNoetherian Y.left :=
    EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
  let I : Y.left.IdealSheafData := D.1.comap Y.hom
  let D' : EffectiveCartierDivisor Y.left := D.comapFiniteEtale Y
  let hfiniteEtale : IsFiniteEtale Y.hom := Y.prop
  obtain ⟨z, hz, hzChar, hzNC⟩ :=
    D.exists_normalCrossingPointOfResidueCharacteristic_on_comapComponent
      Y.hom q hD Z hZ
  refine ⟨z, hz, ?_, hzChar, hzNC, ?_, ?_, ?_⟩
  · exact IdealSheafData.IsNormalCrossingsAt.isRegularAt
      (X := Y.left) hzNC (I.range_subschemeι.le ⟨z, rfl⟩)
  · exact D'.2.componentBranchPrimeAt_height_eq_one Z hZ z hz
  · exact I.stalkIdeal_le_componentBranchPrimeAt Z hZ z hz
  · exact IsLocalRing.le_maximalIdeal
      (I.componentBranchPrimeAt Z hZ z hz).isPrime.ne_top

/-- A component of an arithmetic Galois pullback supplies an actual
residue-characteristic-two point and its canonical height-one branch prime.
The boundary containment and containment in the closed prime are conclusions,
not additional branch hypotheses. -/
theorem galoisPullback_component_exists_residueCharacteristicTwoBranch
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    letI : IsLocallyNoetherian Y.left :=
      EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    ∃ (z : I.subscheme) (hz : z ∈ Z),
      let x₀ : Y.left := I.subschemeι z
      let q := (I.componentBranchPrimeAt Z hZ z hz).asIdeal
      Y.left.IsRegularAt x₀ ∧
        ringChar (Y.left.residueField x₀) = 2 ∧
          I.IsNormalCrossingsAt x₀ ∧
            q.height = 1 ∧ I.stalkIdeal x₀ ≤ q ∧
              q ≤ IsLocalRing.maximalIdeal (Y.left.presheaf.stalk x₀) := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
  let : IsLocallyNoetherian Y.left :=
    EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
  let I : Y.left.IdealSheafData := D.1.comap Y.hom
  exact D.galoisPullback_component_exists_residueCharacteristicBranch_of_normalCrossingPoints
    2 hD.2.2.2.1 Y hY Z hZ

/-- If the generic residue field of the arithmetic base is rational, the
component branch quotient at every specialization has characteristic zero.
This is the characteristic-zero input required to cut the branch by a
positive residue characteristic. -/
theorem galoisPullback_componentBranchQuotient_charZero_of_ratEquiv
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (ek : S.residueField (genericPoint S) ≃+* ℚ)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme)
    (z : (D.1.comap Y.hom).subscheme) (hz : z ∈ Z) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    let q := (I.componentBranchPrimeAt Z hZ z hz).asIdeal
    CharZero (Y.left.presheaf.stalk (I.subschemeι z) ⧸ q) := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
  let I : Y.left.IdealSheafData := D.1.comap Y.hom
  let x := I.componentGenericPoint Z hZ
  let k := S.residueField (genericPoint S)
  have hdata :=
    D.galoisPullback_componentGenericPoint_localResidueData
      p hD Y hY Z hZ
  dsimp only at hdata
  obtain ⟨_hregular, _hheight, hAlg, _hgeo⟩ := hdata
  let : Algebra k (Y.left.residueField x) := hAlg
  let : CharZero k := ek.toRingHom.charZero
  let : CharZero (Y.left.residueField x) :=
    Algebra.charZero_of_charZero k _
  exact AlgebraicGeometry.Scheme.specializationPrime_quotient_charZero
    (I.componentGenericPoint_specializes_subschemeι Z hZ z hz)

section IntegerBase

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

/-- Integer-base form of the characteristic-zero branch quotient.  The
structure morphism and generic residue-field identification are canonical. -/
theorem galoisPullback_componentBranchQuotient_charZero_overIntegers
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryConditionOverIntegers)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme)
    (z : (D.1.comap Y.hom).subscheme) (hz : z ∈ Z) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    let q := (I.componentBranchPrimeAt Z hZ z hz).asIdeal
    CharZero (Y.left.presheaf.stalk (I.subschemeι z) ⧸ q) := by
  exact D.galoisPullback_componentBranchQuotient_charZero_of_ratEquiv
    (specULiftZIsTerminal.from X) hD
      specULiftZGenericResidueFieldEquivQ Y hY Z hZ z hz

/-- Over the canonical integer base, the residue-characteristic-two point,
its normal-crossings condition, its height-one component branch, and the
characteristic-zero branch quotient are all produced simultaneously. -/
theorem
    galoisPullback_component_exists_residueCharacteristicTwoBranch_overIntegers
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryConditionOverIntegers)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    letI : IsLocallyNoetherian Y.left :=
      EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    ∃ (z : I.subscheme) (hz : z ∈ Z),
      let x₀ : Y.left := I.subschemeι z
      let q := (I.componentBranchPrimeAt Z hZ z hz).asIdeal
      Y.left.IsRegularAt x₀ ∧
        ringChar (Y.left.residueField x₀) = 2 ∧
          I.IsNormalCrossingsAt x₀ ∧
            q.height = 1 ∧ I.stalkIdeal x₀ ≤ q ∧
              q ≤ IsLocalRing.maximalIdeal (Y.left.presheaf.stalk x₀) ∧
                CharZero (Y.left.presheaf.stalk x₀ ⧸ q) := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
  let : IsLocallyNoetherian Y.left :=
    EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
  let I : Y.left.IdealSheafData := D.1.comap Y.hom
  have hbranch :=
    D.galoisPullback_component_exists_residueCharacteristicTwoBranch
      (specULiftZIsTerminal.from X) hD Y hY Z hZ
  dsimp only at hbranch
  obtain ⟨z, hz, hregular, hzChar, hzNC, hqHeight, hIq, hqMax⟩ := hbranch
  have hqCharZero :=
    D.galoisPullback_componentBranchQuotient_charZero_overIntegers
      hD Y hY Z hZ z hz
  dsimp only at hqCharZero
  exact ⟨z, hz, hregular, hzChar, hzNC, hqHeight, hIq, hqMax,
    hqCharZero⟩

end IntegerBase

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
