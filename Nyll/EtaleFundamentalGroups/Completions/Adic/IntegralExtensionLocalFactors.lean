/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.CoprimeProduct
import Nyll.SchemeTheory.RingTheory.AdicCompletion.LocalizationAtPrime
import Nyll.EtaleFundamentalGroups.Completions.Adic.PowerCofinality

/-!
# Local factors of a completed integral extension

For a finite integral extension of a Dedekind domain, completion along the
extension of a nonzero maximal ideal first splits over the primes above it.
Power-adic cofinality removes the ramification exponent in each factor, and
localization at that prime identifies the factor with the completion of the
corresponding local ring.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uB

variable {A : Type uA} [CommRing A] [IsDomain A]
variable {B : Type uB} [CommRing B] [IsDedekindDomain B]
variable [Algebra A B] [Algebra.IsIntegral A B]
variable [Module.IsTorsionFree A B] [Module.Finite A B]

/-- The ramification-power completion at `Q` is canonically the completion of
the local ring `B_Q`.  Positivity of the ramification index follows from the
primality of `Q` and finiteness of `B` over `A`. -/
noncomputable def adicCompletionPrimePowerLocalFactorAlgEquiv
    (p : Ideal A) [p.IsMaximal] (Q : p.primesOver B) :
    AdicCompletion (Q.1 ^ Q.1.ramificationIdx A) B ≃ₐ[B]
      AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q.1))
        (Localization.AtPrime Q.1) :=
  (adicCompletionPowerAlgEquiv Q.1 (Q.1.ramificationIdx A)
      (Q.1.ramificationIdx_pos A)).trans
    (adicCompletionLocalizationAtPrimeAlgEquiv Q.1)

omit [IsDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] in
@[simp]
theorem adicCompletionPrimePowerLocalFactorAlgEquiv_of
    (p : Ideal A) [p.IsMaximal] (Q : p.primesOver B) (x : B) :
    adicCompletionPrimePowerLocalFactorAlgEquiv p Q
        (AdicCompletion.of (Q.1 ^ Q.1.ramificationIdx A) B x) =
      algebraMap B
        (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q.1))
          (Localization.AtPrime Q.1)) x :=
  (adicCompletionPrimePowerLocalFactorAlgEquiv p Q).commutes x

/-- Completion along the extended ideal is the product of the completed local
rings at all primes above `p`. -/
noncomputable def adicCompletionIntegralExtensionLocalFactorsRingEquiv
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) :
    AdicCompletion (p.map (algebraMap A B)) B ≃+*
      ∀ Q : p.primesOver B,
        AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q.1))
          (Localization.AtPrime Q.1) :=
  (adicCompletionIntegralExtensionEquivPi p hp).trans
    (RingEquiv.piCongrRight fun Q =>
      (adicCompletionPrimePowerLocalFactorAlgEquiv p Q).toRingEquiv)

@[simp]
theorem adicCompletionIntegralExtensionLocalFactorsRingEquiv_apply
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (x : AdicCompletion (p.map (algebraMap A B)) B)
    (Q : p.primesOver B) :
    adicCompletionIntegralExtensionLocalFactorsRingEquiv p hp x Q =
      adicCompletionPrimePowerLocalFactorAlgEquiv p Q
        (adicCompletionIntegralExtensionEquivPi p hp x Q) := by
  rw [adicCompletionIntegralExtensionLocalFactorsRingEquiv,
    RingEquiv.trans_apply, RingEquiv.piCongrRight_apply]
  rfl

@[simp]
theorem adicCompletionIntegralExtensionLocalFactorsRingEquiv_of_apply
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) (x : B)
    (Q : p.primesOver B) :
    adicCompletionIntegralExtensionLocalFactorsRingEquiv p hp
        (AdicCompletion.of (p.map (algebraMap A B)) B x) Q =
      algebraMap B
        (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q.1))
          (Localization.AtPrime Q.1)) x := by
  rw [adicCompletionIntegralExtensionLocalFactorsRingEquiv_apply,
    adicCompletionIntegralExtensionEquivPi_of,
    adicCompletionPrimePowerLocalFactorAlgEquiv_of]

end EtaleFundamentalGroups
