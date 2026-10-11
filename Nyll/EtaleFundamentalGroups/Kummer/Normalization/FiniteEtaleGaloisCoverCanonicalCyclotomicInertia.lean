/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverCanonicalFundamentalGroup
import Nyll.EtaleFundamentalGroups.Kummer.Normalization.HeightOneCyclotomicInertia

/-!
# Cyclotomic vanishing for canonical divisorial quotients

For an abelian finite-etale Galois cover, geometric integrality of a rational
height-one residue field and odd inertia force the image of the corrected
canonical fundamental-group quotient to vanish.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Inertia
open scoped IsMulCommutative

namespace EtaleFundamentalGroups.Kummer

universe u

/-- At a height-one prime, geometric integrality over a rational field and
coprimality with two kill the image of the corrected canonical field
fundamental-group quotient attached to every normalization prime above it. -/
theorem
    canonicalInertia_eq_bot_of_finiteEtaleGaloisCover_geometricallyIntegralResidue
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y)
    [IsMulCommutative (Aut Y)] :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K : Type u := X.functionField
    let L : Type u := Y.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected Y
    letI : _root_.IsGalois K L :=
      isGalois_functionField_of_isGalois_finiteEtale Y hY
    ∀ {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
      [Algebra A K] [IsFractionRing A K]
      [Algebra A L] [IsScalarTower A K L]
      (P : Ideal A) [P.IsPrime] (_hP : P.height = 1)
      (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
      [Algebra k P.ResidueField],
      GeometricallyIntegral
          (Spec.map (CommRingCat.ofHom
            (algebraMap k P.ResidueField))) →
        Nat.Coprime
            (Nat.card
              (localizedNormalizationInertiaFieldCanonicalHom
                (K := K) (L := L) P Q).range) 2 →
          (localizedNormalizationInertiaFieldCanonicalHom
              (K := K) (L := L) P Q).range = ⊥ := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K : Type u := X.functionField
  let L : Type u := Y.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  dsimp only
  intro A instCommA instDomainA instRegularA instAlgAK instFracAK
    instAlgAL instTowerAKL P instPPrime hP Q instQPrime instQLiesOver
    instAlgk hgeo hCoprime
  have hSourceCoprime :
      Nat.Coprime
        (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) 2 := by
    rw [normalizationInertia_eq_localizedNormalizationInertia
        (K := K) (L := L) P Q,
      ← localizedNormalizationInertiaFieldCanonicalHom_range
        (K := K) (L := L) P Q]
    exact hCoprime
  have hSourceBot : Q.toAddSubgroup.inertia Gal(L/K) = ⊥ :=
    finiteEtaleGaloisCover_heightOneNormalizationInertia_eq_bot_of_geometricallyIntegral_residue
      k ek Y hY (A := A) P hP Q hgeo hSourceCoprime
  rw [localizedNormalizationInertiaFieldCanonicalHom_range
      (K := K) (L := L) P Q,
    ← normalizationInertia_eq_localizedNormalizationInertia
      (K := K) (L := L) P Q]
  exact hSourceBot

end EtaleFundamentalGroups.Kummer

end
