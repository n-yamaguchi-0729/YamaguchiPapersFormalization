/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteTameIndex
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationRamificationTower
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTower
import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.FiniteLevelFieldAlgebra
import EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import EtaleFundamentalGroups.Inertia.FiniteIdealTameRamification
import EtaleFundamentalGroups.Inertia.FiniteIdealNormalizationCoprimality
import EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationTameProperties
import SchemeTheory.Normalization.IntegralClosureAutomorphisms
import ValuedFieldTheory.Ramification.HilbertRamification.CanonicalCharacterTower
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Divisibility of tame orders in finite towers

Supplies the finite-stage tame arithmetic and proves that tame orders divide along inclusions of
finite Galois stages.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory RamificationTheory.HilbertRamification

universe u v w

/-- The accepted finite-normalization field-to-ring boundary, used only to
supply the two numerical facts needed by the actual tower below. -/
private theorem finiteNormalization_tame_arithmetic
    (A : Type u) (K : Type v) (C : Type w)
    [rA : CommRing A] [dA : IsDomain A] [vA : IsDiscreteValuationRing A]
    [fK : Field K] [fC : Field C]
    [aAK : Algebra A K] [fAK : IsFractionRing A K]
    [aKC : Algebra K C] [aAC : Algebra A C] [tAKC : IsScalarTower A K C]
    [fKC : FiniteDimensional K C] [gKC : IsGalois K C] :
    letI : IsDedekindDomain (normalizationCommAlgCat A C) :=
      integralClosure.isDedekindDomain A K C
    ∀ (Q : Ideal (normalizationCommAlgCat A C)) [_qPrime : Q.IsPrime] (hQ : Q ≠ ⊥),
      commAlgIdealTameOrder A (normalizationCommAlgCat A C) Q hQ ∣ Q.ramificationIdx A ∧
      ∀ n : ℕ, IsUnit (n : A) →
        Nat.Coprime n (Q.ramificationIdx A /
          commAlgIdealTameOrder A (normalizationCommAlgCat A C) Q hQ) := by
  let B : CommAlgCat.{w} A := normalizationCommAlgCat A C
  have dB : IsDedekindDomain B := integralClosure.isDedekindDomain A K C
  have tAC : Module.IsTorsionFree A C := .trans_faithfulSMul A K C
  have tAB : Module.IsTorsionFree A B :=
    inferInstanceAs (Module.IsTorsionFree A (integralClosure A C))
  have fAB : Module.Finite A B :=
    nativeNormalization_finite A K (CommAlgCat.of A C) (Field.toIsField C)
  have gAB : IsGaloisGroup (B ≃ₐ[A] B) A B :=
    integralClosure_automorphisms_isGaloisGroup A K C
  change ∀ (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥),
    commAlgIdealTameOrder A B Q hQ ∣ Q.ramificationIdx A ∧
      ∀ n : ℕ, IsUnit (n : A) →
        Nat.Coprime n (Q.ramificationIdx A / commAlgIdealTameOrder A B Q hQ)
  clear_value B
  clear tAC gKC fKC tAKC aAC aKC fAK aAK fC C fK K
  intro Q qPrime hQ
  have hmax : Q.IsMaximal := Ideal.IsPrime.isMaximal qPrime hQ
  have hbaseMax : (Q.under A).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  have hover : Q.LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal hbaseMax).symm⟩
  constructor
  · exact finiteIdealTameOrder_dvd_ramificationIdx A B (B ≃ₐ[A] B) Q hQ
  · intro n hn
    exact finiteIdealNormalizationExponent_coprime_of_isUnit_base A B Q hQ n hn

/-- Instantiate the proved normalization arithmetic at one original finite
stage before a second stage and its ordering relation are introduced. -/
theorem actualFiniteStage_tame_arithmetic
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L) :
    actualFiniteStageTameOrder A K L Q E ∣
        (finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A ∧
      ∀ n : ℕ, IsUnit (n : A) → Nat.Coprime n
        ((finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
          actualFiniteStageTameOrder A K L Q E) := by
  exact finiteNormalization_tame_arithmetic A K (finiteLevelFieldAlgebra A K L E)
    (tAKC := finiteLevelFieldAlgebra_tower A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (_qPrime := finiteAbsoluteNormalizationPrime_isPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

/-- The actual finite tame orders form a divisibility tower. The lower order
is invertible in the original base, so it cannot enter the upper
characteristic-power normalization factor. Every numerical input is
constructed from the original finite normalizations. -/
theorem actualFiniteStageTameOrder_dvd_of_le
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    actualFiniteStageTameOrder A K L Q E ∣ actualFiniteStageTameOrder A K L Q F := by
  let nE : ℕ := actualFiniteStageTameOrder A K L Q E
  let nF : ℕ := actualFiniteStageTameOrder A K L Q F
  let eE : ℕ := (finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A
  let eF : ℕ := (finiteAbsoluteNormalizationPrime A K L Q F).ramificationIdx A
  have hE : nE ∣ eE := (actualFiniteStage_tame_arithmetic A K L Q E).1
  have hF : nF ∣ eF ∧ ∀ n : ℕ, IsUnit (n : A) → Nat.Coprime n (eF / nF) :=
    actualFiniteStage_tame_arithmetic A K L Q F
  have he : eE ∣ eF := by
    let : Algebra (finiteAbsoluteNormalizationAlgebra A K L E)
        (finiteAbsoluteNormalizationAlgebra A K L F) :=
      (actualFiniteNormalizationTowerRingMap A K L E F h).toAlgebra
    refine ⟨(finiteAbsoluteNormalizationPrime A K L Q F).ramificationIdx
      (finiteAbsoluteNormalizationAlgebra A K L E), ?_⟩
    exact actualFiniteNormalization_ramificationIdx_tower A K L Q E F h
  have hnE : IsUnit (nE : A) := actualFiniteStageTameOrder_isUnit A K L Q E
  exact tameOrder_dvd_of_ramificationIdx_dvd hE hF.1 he (hF.2 nE hnE)

end EtaleFundamentalGroups.Inertia

end
