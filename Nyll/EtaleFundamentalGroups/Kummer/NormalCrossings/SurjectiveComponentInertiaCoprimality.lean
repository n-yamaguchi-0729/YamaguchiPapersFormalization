/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.FiniteQuotientComponentInertiaCoprimality
import Nyll.SchemeTheory.Divisors.SurjectiveArithmeticBoundary

/-!
# Component inertia over every arithmetic residue characteristic

If every irreducible component of a normal-crossings divisor is surjective
over the integer base, a prescribed component contains a normal-crossings
point in every rational-prime residue characteristic.  Applying the local
component theorem at those points gives prime-to-`p` normalization inertia
for one fixed connected finite-etale Galois cover of the complement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups TopologicalSpace
open AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u

variable {X : Scheme.{u}}

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

/-- For one fixed connected finite-etale Galois cover of the boundary
complement, every rational prime occurs at a normal-crossings point of the
chosen surjective component and yields a normalization prime whose inertia
has order prime to that rational prime. -/
theorem
    HasSurjectiveComponentsOverIntegers.forall_prime_exists_componentNormalizationInertia_coprime
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hSurjective : D.HasSurjectiveComponentsOverIntegers)
    (hNC : D.IsNormalCrossings)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W) :
    ∀ p : ℕ, p.Prime →
      ∃ (z : D.1.subscheme) (hz : z ∈ Z)
        (hchar : ringChar
          (X.residueField (D.1.subschemeι z)) = p),
        let : CharP (X.residueField (D.1.subschemeι z)) p :=
          ringChar.of_eq hchar
        ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U)
          (hfu : f u = D.1.subschemeι z), Etale f ∧
          let K := (D.1.supportComplement : Scheme).functionField
          let : IsIntegral D.1.supportComplement :=
            isIntegral_of_isOpenImmersion D.1.supportComplement.ι
          let : IsIntegral W.left :=
            EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
          let L := W.left.functionField
          let : Algebra K L :=
            EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
          let : FiniteDimensional K L :=
            EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
          let : _root_.IsGalois K L :=
            EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
          let A := X.presheaf.stalk (f u)
          let : Algebra A K :=
            D.1.supportComplementFunctionFieldAlgebra (f u)
          let : IsFractionRing A K :=
            D.1.supportComplementFunctionField_isFractionRing (f u)
          let : Algebra A L :=
            ((algebraMap K L).comp (algebraMap A K)).toAlgebra
          let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
          let B := integralClosure A L
          let : IsFractionRing B L :=
            IsIntegralClosure.isFractionRing_of_finite_extension A K L B
          let branchPrime : Ideal (X.presheaf.stalk (f u)) :=
            hfu.symm ▸ (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
          ∃ q : Ideal B, q.IsPrime ∧ q.LiesOver branchPrime ∧
            Nat.Coprime
              (Nat.card (q.toAddSubgroup.inertia Gal(L/K))) p := by
  intro p hp
  obtain ⟨z, hz, hchar, hNCz⟩ :=
    hSurjective.hasNormalCrossingPointOfResidueCharacteristicOnEachComponent
      hNC p hp Z hZ
  refine ⟨z, hz, hchar, ?_⟩
  intro residueChar
  have hHorizontal :
      D.ComponentsThroughPointAreHorizontal
        (specULiftZIsTerminal.from X) z := by
    intro Z' hZ' _hz'
    exact hSurjective.isHorizontalOverIntegers Z' hZ'
  let Base := Spec (CommRingCat.of (ULift.{u} ℤ))
  let e : Base.residueField (genericPoint Base) ≃+* ℚ :=
    specULiftZGenericResidueFieldEquivQ
  let : CharZero (Base.residueField (genericPoint Base)) :=
    e.toRingHom.charZero
  exact
    hHorizontal.exists_componentNormalizationInertia_coprime
      D (specULiftZIsTerminal.from X) Z hZ z hz hNCz p hp W hW

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
