/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.Henselian.LocalizationComparison
import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.LocalFactor
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Tag coordinates starting from an arbitrary normalization prime

The older chosen-factor comparison starts with the Tag 00UJ data and then
extracts a generic-fibre component.  Here the direction is reversed: an
arbitrary prime of the normalization is first supplied to 00UJ itself.
The contraction equality returned by 00UJ recovers the local ring of that
input prime, while smooth normalization base change extracts the actual
generic component selected by the same Tag prime.

Thus the chosen Away factor, the input normalization prime, and the produced
component prime are compared by constructed equivalences.  No comparison
equivalence or ideal equality is an input.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uR uL

/-- The canonical local ring map preserves the base action before and after localization.
Compute this compatibility before specializing to the normalization component. -/
private noncomputable def localPrimeComparisonRestrictScalars
    {R A B X : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing X]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    [Algebra R X] [Algebra (Localization.AtPrime p) X]
    [IsScalarTower R (Localization.AtPrime p) X]
    (E : let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
      Localization.AtPrime q ≃ₐ[Localization.AtPrime p] X) :
    Localization.AtPrime q ≃ₐ[R] X := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  refine { toRingEquiv := E.toRingEquiv, commutes' := fun r ↦ ?_ }
  change E (algebraMap R (Localization.AtPrime q) r) = algebraMap R X r
  have hlocal :
      algebraMap (Localization.AtPrime p) (Localization.AtPrime q)
        (algebraMap R (Localization.AtPrime p) r) =
          algebraMap R (Localization.AtPrime q) r := by
    rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime p)]
    change Localization.localRingHom p q (algebraMap A B)
      Ideal.LiesOver.over (algebraMap A (Localization.AtPrime p) (algebraMap R A r)) =
        algebraMap R (Localization.AtPrime q) r
    rw [Localization.localRingHom_to_map,
      ← IsScalarTower.algebraMap_apply A B (Localization.AtPrime q),
      ← IsScalarTower.algebraMap_apply R A (Localization.AtPrime q)]
  rw [← hlocal, E.commutes,
    ← IsScalarTower.algebraMap_apply R (Localization.AtPrime p) X]

/-- Apply Tag 00UJ directly to an arbitrary prime `p` of a finite
normalization over a Henselian local ring.

The theorem returns both canonical views of the same chosen local factor:
the localization at the original input prime and the localization at the
normalization prime in the source-produced generic tensor component. -/
theorem
    exists_etaleChosenLocalFactor_arbitraryNormalizationPrime_component
    {R : Type uR} {L : Type uL}
    [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [Field L] [Algebra R L]
    [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L]
    [Module.Finite R (integralClosure R L)]
    (p : Ideal (integralClosure R L)) [p.IsPrime]
    [p.LiesOver (IsLocalRing.maximalIdeal R)] :
    ∃ (C : Type uR) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra.Etale R C)
      (P : Ideal C) (_ : P.IsPrime)
      (_ : P.LiesOver (IsLocalRing.maximalIdeal R))
      (e : C ⊗[R] integralClosure R L) (_ : IsIdempotentElem e)
      (P' : Ideal (C ⊗[R] integralClosure R L))
      (_ : P'.IsPrime) (_ : P'.LiesOver P)
      (heP' : e ∉ P'),
        P'.comap Algebra.TensorProduct.includeRight.toRingHom = p ∧
        Function.Bijective
          (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P
            (Algebra.ofId R C)
            (P.over_def (IsLocalRing.maximalIdeal R))) ∧
        Module.Finite C (Localization.Away e) ∧
        (∀ P'' : Ideal (C ⊗[R] integralClosure R L),
          P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') ∧
        let Q := etaleChosenAwayPrime e P'
        let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
        let Cₚ := Localization.AtPrime P
        let Dₚ := Localization.AtPrime Q
        ∃ (m : MaximalSpectrum (Cₚ ⊗[R] L))
          (q : PrimeSpectrum
            (integralClosure Cₚ (FiniteEtaleGenericFiberComponent m.asIdeal))),
          Nonempty (Dₚ ≃ₐ[R] Localization.AtPrime p) ∧
            Nonempty (Dₚ ≃ₐ[R] Localization.AtPrime q.asIdeal) ∧
            Nonempty (Localization.AtPrime p ≃ₐ[R] Localization.AtPrime q.asIdeal) := by
  let S := integralClosure R L
  obtain ⟨C, _, _, _, P, _, _, e, heidem, P', _, _, heP',
      hP'p, hres, hfinite, hunique, ⟨Einput⟩⟩ :=
    exists_etaleChosenLocalFactor_henselian_inputPrimeAlgEquiv
      (R := R) (S := S) p
  refine ⟨C, inferInstance, inferInstance, inferInstance,
    P, inferInstance, inferInstance, e, heidem,
    P', inferInstance, inferInstance, heP',
    hP'p, hres, hfinite, hunique, ?_⟩
  intro Q hQprime Cₚ Dₚ
  have : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  have : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  obtain ⟨m, q, ⟨Ecomponent⟩⟩ :=
    exists_etaleChosenLocalFactor_finiteGenericFiberComponent_algEquiv
      (R := R) (C := C) (L := L) P e P' heP'
  let EcomponentR := localPrimeComparisonRestrictScalars
    (R := R) (A := C) (B := Localization.Away e)
    (X := Localization.AtPrime q.asIdeal) P Q Ecomponent
  let Etotal := Einput.symm.trans EcomponentR
  exact ⟨m, q, ⟨Einput⟩, ⟨EcomponentR⟩, ⟨Etotal⟩⟩

end EtaleFundamentalGroups.Kummer

end
