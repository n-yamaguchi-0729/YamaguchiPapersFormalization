/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FiniteEtale.Away.TensorBaseChange
import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.LocalFactor
import EtaleFundamentalGroups.Normalization.IntegralClosure.IntegralBase.ChosenLocalization.Core

/-!
# The primitive boundary Away map on the Tag 00UJ local factor

The boundary-complement hypothesis belongs to the original finite
normalization.  After the Tag 00UJ etale base change, it is first transported
to the tensor product, then to the finite idempotent factor, and finally to
the chosen prime-local factor.  This construction never uses a root cover or
a generic field component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uA uB

/-- If `q` is the only prime of an integral algebra above `p`, then the
prime-local ring at `q` is already the localization obtained by inverting
the image of `pᶜ`.

The divisibility condition in the localization criterion is produced by
integrality and uniqueness of the prime; it is not an additional comparison
hypothesis. -/
theorem isLocalization_localizationAtPrime_of_primesOver_eq_singleton
    {A : Type uA} {B : Type uB}
    [CommRing A] [CommRing B] [Algebra A B]
    {p : Ideal A} [p.IsPrime]
    {q : Ideal B} [q.IsPrime]
    [Algebra.IsIntegral A B]
    (hunique : p.primesOver B = {q}) :
    IsLocalization
      (Algebra.algebraMapSubmonoid B p.primeCompl)
      (Localization.AtPrime q) := by
  have hqOver : q.LiesOver p := (hunique.ge rfl).2
  have hle :
      Algebra.algebraMapSubmonoid B p.primeCompl ≤ q.primeCompl := by
    rintro x ⟨a, ha, rfl⟩
    change algebraMap A B a ∉ q
    intro hmem
    exact ha <| by
      rw [hqOver.over]
      exact hmem
  have hdvd : ∀ x ∈ q.primeCompl,
      ∃ y ∈ Algebra.algebraMapSubmonoid B p.primeCompl, x ∣ y := by
    intro x hx
    change x ∉ q at hx
    obtain ⟨a, ha, hax⟩ :=
      Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton
        hunique x hx
    exact ⟨algebraMap A B a, ⟨a, ha, rfl⟩, hax⟩
  exact
    (IsLocalization.iff_of_le_of_exists_dvd
      (M := Algebra.algebraMapSubmonoid B p.primeCompl)
      (S := Localization.AtPrime q) q.primeCompl hle hdvd).2
      (inferInstance :
        IsLocalization q.primeCompl (Localization.AtPrime q))

universe uR uC uS

/-- The primitive Away hypothesis on `R → S` survives passage to the finite
Tag idempotent factor.  Finiteness of that factor is exactly the production
output of Tag 00UJ. -/
theorem etaleChosenAway_boundaryAway
    {R : Type uR} {C : Type uC} {S : Type uS}
    [CommRing R] [CommRing C] [CommRing S]
    [IsNoetherianRing C]
    [Algebra R C] [Algebra R S]
    (f : R)
    (hAway :
      (Localization.awayMap (algebraMap R S) f).Etale)
    (e : C ⊗[R] S)
    (hfinite : Module.Finite C (Localization.Away e)) :
    (Localization.awayMap
      (algebraMap C (Localization.Away e))
      (algebraMap R C f)).Etale := by
  let T := C ⊗[R] S
  let D := Localization.Away e
  let fC : C := algebraMap R C f
  let : Module.Finite C D := hfinite
  let : Algebra.FormallyEtale T D :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers e)
  have hTensor :
      (Localization.awayMap (algebraMap C T) fC).Etale := by
    exact localization_awayMap_tensorProduct_etale
      (X := S) (Y := C) f hAway
  exact
    localization_awayMap_etale_of_finite_formallyEtale_extension
      (A := C) (C := T) (D := D) fC hTensor

/-- The literal boundary Away map on the chosen Tag prime-local factor.

The singleton-fibre assertion supplied by Tag 00UJ makes the chosen local
factor a pushout from the pointed base localization.  Hence this conclusion
is produced solely from the original normalization's Away hypothesis and
the literal Tag data.  In particular, no root cover, generic component, or
comparison equivalence occurs in the statement. -/
theorem etaleChosenLocalFactor_pointed_boundaryAway
    {R : Type uR} {C : Type uC} {S : Type uS}
    [CommRing R] [CommRing C] [CommRing S]
    [IsNoetherianRing C]
    [Algebra R C] [Algebra R S]
    (f : R)
    (hAway :
      (Localization.awayMap (algebraMap R S) f).Etale)
    (P : Ideal C) [P.IsPrime]
    (e : C ⊗[R] S)
    (P' : Ideal (C ⊗[R] S))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (hfinite : Module.Finite C (Localization.Away e))
    (hunique : ∀ P'' : Ideal (C ⊗[R] S),
      P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') :
    let Q := etaleChosenAwayPrime e P'
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
    letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    let Cₚ := Localization.AtPrime P
    let Dₚ := Localization.AtPrime Q
    letI : Algebra Cₚ Dₚ :=
      Localization.AtPrime.algebraOfLiesOver P Q
    @Algebra.Etale
      (Localization.Away
        (algebraMap C Cₚ (algebraMap R C f)))
      (Localization.Away
        (algebraMap Cₚ Dₚ
          (algebraMap C Cₚ (algebraMap R C f))))
      _ _
      (Localization.awayMap
        (algebraMap Cₚ Dₚ)
        (algebraMap C Cₚ (algebraMap R C f))).toAlgebra := by
  dsimp only
  let T := C ⊗[R] S
  let D := Localization.Away e
  let Q : Ideal D := etaleChosenAwayPrime e P'
  let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  let : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  let Cₚ := Localization.AtPrime P
  let Dₚ := Localization.AtPrime Q
  let fC : C := algebraMap R C f
  let : Module.Finite C D := hfinite
  let : Algebra.IsIntegral C D := Algebra.IsIntegral.of_finite C D
  let : Algebra Cₚ Dₚ :=
    Localization.AtPrime.algebraOfLiesOver P Q
  have hQunique : P.primesOver D = {Q} :=
    etaleChosenAway_primesOver_eq_singleton
      P e P' heP' hunique
  let : IsLocalization
      (Algebra.algebraMapSubmonoid D P.primeCompl) Dₚ :=
    isLocalization_localizationAtPrime_of_primesOver_eq_singleton
      hQunique
  let : Algebra.IsPushout C D Cₚ Dₚ :=
    Algebra.isPushout_of_isLocalization P.primeCompl Cₚ D Dₚ
  have hD :
      (Localization.awayMap (algebraMap C D) fC).Etale :=
    etaleChosenAway_boundaryAway f hAway e hfinite
  exact
    localization_awayMap_etale_of_isPushout
      (A := C) (B := D) (C := Cₚ) (D := Dₚ) fC hD

end EtaleFundamentalGroups

end
