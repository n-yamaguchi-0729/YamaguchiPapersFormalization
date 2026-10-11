/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.DivisorialCategoricalImage
import Nyll.ProCGroups.Boundary.CyclotomicInversion

/-!
# Triviality of finite divisorial inertia

A finite ideal-inertia subgroup is trivial once its order is prime to every
rational prime.  The finite-etale specialization below applies this criterion
to the range of the canonical inertia-fixed-field quotient, without unfolding
the pointed quotient construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u uA uB uG

/-- An ideal-inertia subgroup is trivial if its finite order is prime to every
rational prime. -/
theorem idealInertia_eq_bot_of_card_coprime_every_prime
    {B : Type uB} {G : Type uG}
    [Ring B] [Group G] [MulSemiringAction G B]
    (Q : Ideal B) [Finite (Q.toAddSubgroup.inertia G)]
    (hCoprime : ∀ p : ℕ, p.Prime →
      Nat.Coprime (Nat.card (Q.toAddSubgroup.inertia G)) p) :
    Q.toAddSubgroup.inertia G = ⊥ :=
  ProCGroups.Boundary.subgroup_eq_bot_of_card_coprime_every_prime
    (Q.toAddSubgroup.inertia G) hCoprime

/-- For a connected finite-etale Galois cover, prime-to-every-prime order of
the canonical inertia-fixed-field quotient range forces the corresponding
categorical normalization-prime inertia subgroup to be trivial. -/
theorem
    finiteEtaleGaloisCoverIdealInertia_eq_bot_of_quotientRange_coprime_every_prime
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K := X.functionField
    let L := Y.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) [CommRing A] [IsDomain A]
      [Algebra A K] [IsFractionRing A K]
      [Algebra A L] [IsScalarTower A K L]
      [IsIntegrallyClosed A]
      (P : Ideal A) [P.IsPrime]
      (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P],
      letI : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      letI : _root_.IsGalois K L :=
        isGalois_functionField_of_isGalois_finiteEtale Y hY
      let B := integralClosure A L
      letI : IsFractionRing B L :=
        IsIntegralClosure.isFractionRing_of_finite_extension A K L B
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
          Y hY A B
      (∀ p : ℕ, p.Prime →
        Nat.Coprime
          (Nat.card
            (finiteEtaleGaloisCoverIdealInertiaFieldQuotientHom
              Y hY A P Q).range) p) →
      Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ = ⊥ := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K := X.functionField
  let L := Y.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  dsimp only
  intro A instCommRing instDomain instAK instFracAK instAL instTower instNormal P
    instPprime Q instQprime instQover
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  let B := integralClosure A L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
    EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
      Y hY A B
  intro hCoprime
  have hrange :=
    finiteEtaleGaloisCoverIdealInertiaFieldQuotientHom_range
      Y hY A P Q
  let : IsConnected Y := inferInstance
  let : Finite (Aut Y) := inferInstance
  let : Finite ((Aut Y)ᵐᵒᵖ) :=
    Finite.of_injective MulOpposite.unop MulOpposite.unop_injective
  let : Finite (Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  apply idealInertia_eq_bot_of_card_coprime_every_prime
  intro p hp
  rw [← hrange]
  exact hCoprime p hp

end EtaleFundamentalGroups.Inertia

end
