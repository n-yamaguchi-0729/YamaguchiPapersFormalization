/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Boundary.ArithmeticComponentBranchResidue
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeArithmeticChart

/-!
# Characteristic zero along every arithmetic boundary branch

Every height-one stalk prime containing a pulled-back effective Cartier
boundary is the generic point of an irreducible boundary component.  The
arithmetic geometric-integrality condition therefore forces characteristic
zero along every such branch, not only along a preselected component.
-/

noncomputable section


open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u

variable {X S : Scheme.{u}}

/-- Horizontality over an integral base with characteristic-zero generic
residue field forces characteristic zero along every height-one boundary
branch. -/
theorem IsHorizontalOver.hasCharacteristicZeroBranchesAt
    [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.IsHorizontalOver p)
    [CharZero (S.residueField (genericPoint S))]
    (x : X) : D.1.HasCharacteristicZeroBranchesAt x := by
  let I : X.IdealSheafData := D.1
  dsimp only [Scheme.IdealSheafData.HasCharacteristicZeroBranchesAt]
  intro q hqPrime hqHeight hIq
  let : q.IsPrime := hqPrime
  let qSpec : Spec (X.presheaf.stalk x) := ⟨q, hqPrime⟩
  obtain ⟨Z, hZ, hgeneric⟩ :=
    D.2.exists_componentGenericPoint_eq_fromSpecStalk
      x qSpec hqHeight hIq
  let eta := I.componentGenericPoint Z hZ
  have hetaBase : p eta = genericPoint S := by
    have h := I.componentToBase_genericPoint p Z hZ (hD Z hZ)
    exact h
  let eBase : S.residueField (genericPoint S) ≃+*
      S.residueField (p eta) :=
    (S.residueFieldCongr hetaBase.symm).commRingCatIsoToRingEquiv
  let phi : S.residueField (genericPoint S) →+* X.residueField eta :=
    (p.residueFieldMap eta).hom.comp eBase.toRingHom
  let : CharZero (X.residueField eta) :=
    charZero_of_injective_ringHom phi.injective
  let ePoint : X.residueField eta ≃+*
      X.residueField (X.fromSpecStalk x qSpec) :=
    (X.residueFieldCongr hgeneric).commRingCatIsoToRingEquiv
  let e : X.residueField eta ≃+* q.ResidueField :=
    ePoint.trans (X.residueFieldFromSpecStalkEquiv x qSpec)
  let : CharZero q.ResidueField := e.symm.toRingHom.charZero
  exact (algebraMap (X.presheaf.stalk x ⧸ q) q.ResidueField).charZero

/-- After a connected finite-etale Galois pullback, every height-one branch
of an arithmetic boundary has characteristic zero when the generic residue
field of the base is rational. -/
theorem galoisPullback_hasCharacteristicZeroBranchesAt_of_ratEquiv
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (ek : S.residueField (genericPoint S) ≃+* ℚ)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (x : Y.left) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    letI : IsLocallyNoetherian Y.left :=
      EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    I.HasCharacteristicZeroBranchesAt x := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
  let : IsLocallyNoetherian Y.left :=
    EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
  let I : Y.left.IdealSheafData := D.1.comap Y.hom
  let D' : EffectiveCartierDivisor Y.left := D.comapFiniteEtale Y
  dsimp only [Scheme.IdealSheafData.HasCharacteristicZeroBranchesAt]
  intro q hqPrime hqHeight hIq
  let : q.IsPrime := hqPrime
  let qSpec : Spec (Y.left.presheaf.stalk x) := ⟨q, hqPrime⟩
  obtain ⟨Z, hZ, hgeneric⟩ :=
    D'.2.exists_componentGenericPoint_eq_fromSpecStalk
      x qSpec hqHeight hIq
  let eta := I.componentGenericPoint Z hZ
  let k := S.residueField (genericPoint S)
  obtain ⟨hAlg, _hgeo⟩ :=
    D.galoisPullback_componentGenericPoint_exists_geometricallyIntegralResidueAlgebra
      p hD Y hY Z hZ
  let : Algebra k (Y.left.residueField eta) := hAlg
  let : CharZero k := ek.toRingHom.charZero
  let : CharZero (Y.left.residueField eta) :=
    Algebra.charZero_of_charZero k _
  let ePoint : Y.left.residueField eta ≃+*
      Y.left.residueField (Y.left.fromSpecStalk x qSpec) :=
    (Y.left.residueFieldCongr hgeneric).commRingCatIsoToRingEquiv
  let e : Y.left.residueField eta ≃+* q.ResidueField :=
    ePoint.trans (Y.left.residueFieldFromSpecStalkEquiv x qSpec)
  let : CharZero q.ResidueField := e.symm.toRingHom.charZero
  exact (algebraMap
    (Y.left.presheaf.stalk x ⧸ q) q.ResidueField).charZero

section IntegerBase

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

/-- Integer-base form: the structure morphism and rational generic residue
field are canonical. -/
theorem galoisPullback_hasCharacteristicZeroBranchesAt_overIntegers
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryConditionOverIntegers)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (x : Y.left) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    letI : IsLocallyNoetherian Y.left :=
      EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    I.HasCharacteristicZeroBranchesAt x := by
  exact D.galoisPullback_hasCharacteristicZeroBranchesAt_of_ratEquiv
    (specULiftZIsTerminal.from X) hD
      specULiftZGenericResidueFieldEquivQ Y hY x

end IntegerBase

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
