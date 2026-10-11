/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.ComponentNormalizationEtale
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Normalization etaleness at arbitrary height-one boundary primes

A height-one prime of a boundary stalk which contains the boundary ideal is
the canonical branch prime of an irreducible component through the chosen
point.  This identifies the arbitrary prime with the input expected by the
fixed-component normalization theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- A height-one stalk prime containing an effective Cartier ideal is the
canonical branch prime of a component through the chosen boundary point. -/
theorem IsEffectiveCartier.exists_component_branch_representation_of_height_one
    [IsIntegral X] [IsLocallyNoetherian X]
    (hI : I.IsEffectiveCartier) (z : I.subscheme)
    (q : Spec (X.presheaf.stalk (I.subschemeι z)))
    (hqheight : q.asIdeal.height = 1)
    (hIq : I.stalkIdeal (I.subschemeι z) ≤ q.asIdeal) :
    ∃ (Z : Set I.subscheme)
      (hZ : Z ∈ irreducibleComponents I.subscheme)
      (hz : z ∈ Z),
      I.componentBranchPrimeAt Z hZ z hz = q := by
  obtain ⟨Z, hZ, hgeneric⟩ :=
    hI.exists_componentGenericPoint_eq_fromSpecStalk
      (I.subschemeι z) q hqheight hIq
  have hfromSpec :
      X.fromSpecStalk (I.subschemeι z) q ⤳ I.subschemeι z := by
    have hmem : X.fromSpecStalk (I.subschemeι z) q ∈
        Set.range (X.fromSpecStalk (I.subschemeι z)) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem
    exact hmem
  have hgenericSpecializes :
      I.componentGenericPoint Z hZ ⤳ I.subschemeι z := by
    rw [hgeneric]
    exact hfromSpec
  have hz : z ∈ Z := by
    apply (genericPoints.isGenericPoint_ofComponent
      (⟨Z, hZ⟩ : irreducibleComponents I.subscheme)).specializes_iff_mem.mp
    apply I.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp
    rw [← I.componentGenericPoint_eq Z hZ]
    exact hgenericSpecializes
  refine ⟨Z, hZ, hz, ?_⟩
  apply (X.fromSpecStalk (I.subschemeι z)).isEmbedding.injective
  rw [I.fromSpecStalk_componentBranchPrimeAt, hgeneric]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

universe u

variable {X : Scheme.{u}}

/-- At an arbitrary height-one boundary stalk prime, the normalization of a
connected Galois cover's component function field is etale over the localized
ambient stalk. -/
theorem HasSurjectiveComponentsOverIntegers.heightOneBoundaryIntegralClosure_etale_of_stalkIdeal_le
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hSurjective : D.HasSurjectiveComponentsOverIntegers)
    (hNC : D.IsNormalCrossings)
    [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (z : D.1.subscheme)
    (q : Spec (X.presheaf.stalk (D.1.subschemeι z)))
    (hqheight : q.asIdeal.height = 1)
    (hDq : D.1.stalkIdeal (D.1.subschemeι z) ≤ q.asIdeal) :
    letI : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    let K := (D.1.supportComplement : Scheme).functionField
    let L := W.left.functionField
    letI : Algebra K L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : _root_.IsGalois K L :=
      EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
    let x := D.1.subschemeι z
    let p := q.asIdeal
    let : p.IsPrime := q.isPrime
    let Ax := X.presheaf.stalk x
    letI : Algebra Ax K := D.1.supportComplementFunctionFieldAlgebra x
    letI : IsFractionRing Ax K :=
      D.1.supportComplementFunctionField_isFractionRing x
    letI : Algebra Ax L :=
      ((algebraMap K L).comp (algebraMap Ax K)).toAlgebra
    letI : IsScalarTower Ax K L := IsScalarTower.of_algebraMap_eq' rfl
    let V := Localization.AtPrime p
    letI : Algebra V L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p
    Algebra.Etale V (integralClosure V L) := by
  obtain ⟨Z, hZ, hz, hq⟩ :=
    D.2.exists_component_branch_representation_of_height_one
      z q hqheight hDq
  subst q
  exact
    hSurjective.componentBranchIntegralClosure_etale
      D hNC Z hZ W hW z hz

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
