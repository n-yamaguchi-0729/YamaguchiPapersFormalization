/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ChosenPrime.Basic
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.Component
import Nyll.SchemeTheory.RingTheory.GenericFiber.Finite
import Nyll.SchemeTheory.Normalization.IntegralClosure.FiniteProduct
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# The non-Henselian local factor selected by Tag 00UJ

The idempotent furnished by Tag 00UJ cuts out a finite factor after an
etale change of the base.  Its chosen prime remains the unique prime over
the pointed prime after inverting the idempotent.  Consequently the prime
localization of that factor is finite over the pointed base localization.

No Henselian hypothesis is used here.  This is the part of the chosen-factor
construction which precedes any root-cover or purity argument.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

section FiniteProductPrimeCoordinate

universe uI uA uBase

/-- Every prime-local ring of a finite product is canonically the
prime-local ring of one actual coordinate.  The coordinate and its prime are
extracted from the given prime; neither is supplied as auxiliary data.

The computation on algebra maps records that this is the literal evaluation
map.  It is the local form of `PrimeSpectrum.exists_comap_evalRingHom_eq`
needed when a generic tensor product is decomposed into its field
components. -/
theorem exists_localizationAtPrime_pi_factor_ringEquiv
    {I : Type uI} [Finite I]
    (A : I → Type uA) [∀ i, CommRing (A i)]
    (P : Ideal (∀ i, A i)) [P.IsPrime] :
    ∃ (i : I) (q : PrimeSpectrum (A i)),
      ∃ E : Localization.AtPrime P ≃+*
          Localization.AtPrime q.asIdeal,
        ∀ x : ∀ i, A i,
          E (algebraMap (∀ i, A i) (Localization.AtPrime P) x) =
            algebraMap (A i) (Localization.AtPrime q.asIdeal) (x i) := by
  let p : PrimeSpectrum (∀ i, A i) := ⟨P, inferInstance⟩
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
  have hqIdeal :
      q.asIdeal.comap (Pi.evalRingHom A i) = P :=
    congrArg PrimeSpectrum.asIdeal hq
  subst P
  let E :
      Localization.AtPrime
          (q.asIdeal.comap (Pi.evalRingHom A i)) ≃+*
        Localization.AtPrime q.asIdeal :=
    RingEquiv.ofBijective
      (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
      (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
  refine ⟨i, q, E, ?_⟩
  intro x
  change Localization.AtPrime.mapPiEvalRingHom q.asIdeal
      (algebraMap (∀ i, A i)
        (Localization.AtPrime
          (q.asIdeal.comap (Pi.evalRingHom A i))) x) =
    algebraMap (A i) (Localization.AtPrime q.asIdeal) (x i)
  exact Localization.AtPrime.mapPiEvalRingHom_algebraMap_apply
    (R := A) (i := i) (I := q.asIdeal)

/-- Algebra-linear form of
`exists_localizationAtPrime_pi_factor_ringEquiv`.  The algebra structures on
the product and the selected factor are the canonical coordinatewise ones. -/
theorem exists_localizationAtPrime_pi_factor_algEquiv
    {R : Type uBase} [CommRing R]
    {I : Type uI} [Finite I]
    (A : I → Type uA) [∀ i, CommRing (A i)]
    [∀ i, Algebra R (A i)]
    (P : Ideal (∀ i, A i)) [P.IsPrime] :
    ∃ (i : I) (q : PrimeSpectrum (A i)),
      Nonempty
        (Localization.AtPrime P ≃ₐ[R]
          Localization.AtPrime q.asIdeal) := by
  obtain ⟨i, q, E, hE⟩ :=
    exists_localizationAtPrime_pi_factor_ringEquiv A P
  refine ⟨i, q, ⟨AlgEquiv.ofRingEquiv (f := E) fun r ↦ ?_⟩⟩
  simpa only [Pi.algebraMap_apply,
    IsScalarTower.algebraMap_apply R (∀ i, A i)
      (Localization.AtPrime P),
    IsScalarTower.algebraMap_apply R (A i)
      (Localization.AtPrime q.asIdeal)] using
    hE (algebraMap R (∀ i, A i) r)

end FiniteProductPrimeCoordinate

section ArtinianNormalizationPrimeCoordinate

universe uB uG

/-- A prime-local factor of the normalization in a reduced Artinian algebra
comes from one actual residue-field component of that algebra.

Both the component and the prime in its normalization are extracted from the
given prime.  This is the normalization-level coordinate producer used after
smooth base change of the Tag 00UJ tensor product. -/
theorem
    exists_integralClosure_artinianComponent_localizationAtPrime_algEquiv
    {B : Type uB} {G : Type uG}
    [CommRing B] [CommRing G] [Algebra B G]
    [IsArtinianRing G] [IsReduced G]
    (P : Ideal (integralClosure B G)) [P.IsPrime] :
    ∃ (m : MaximalSpectrum G)
      (q : PrimeSpectrum (integralClosure B (G ⧸ m.asIdeal))),
      Nonempty
        (Localization.AtPrime P ≃ₐ[B]
          Localization.AtPrime q.asIdeal) := by
  let A := fun m : MaximalSpectrum G ↦ G ⧸ m.asIdeal
  let eIC : integralClosure B G ≃ₐ[B]
      (∀ m, integralClosure B (A m)) :=
    SchemeTheory.integralClosureFactorsEquiv B G
  let Pprod : Ideal (∀ m, integralClosure B (A m)) :=
    P.map eIC.toRingEquiv
  let : Pprod.IsPrime := by
    exact Ideal.map_isPrime_of_surjective eIC.surjective fun x hx ↦ by
      have hx0 : x = 0 := eIC.injective (hx.trans eIC.map_zero.symm)
      subst x
      exact P.zero_mem
  obtain ⟨m, q, ⟨Ecoord⟩⟩ :=
    exists_localizationAtPrime_pi_factor_algEquiv
      (R := B) (fun m ↦ integralClosure B (A m)) Pprod
  have hcomap : P = Pprod.comap eIC.toRingHom := by
    symm
    exact Ideal.comap_map_of_bijective eIC.toRingEquiv eIC.bijective
  let Eprod : Localization.AtPrime P ≃ₐ[B]
      Localization.AtPrime Pprod :=
    Localization.localAlgEquiv P Pprod eIC hcomap
  exact ⟨m, q, ⟨Eprod.trans Ecoord⟩⟩

end ArtinianNormalizationPrimeCoordinate

universe uR uC uS

variable {R : Type uR} {C : Type uC} {S : Type uS}
variable [CommRing R] [CommRing C] [CommRing S]
variable [Algebra R C] [Algebra R S]

/-- The prime in the idempotent Away factor induced by the Tag 00UJ prime. -/
noncomputable def etaleChosenAwayPrime
    (e : TensorProduct R C S)
    (P' : Ideal (TensorProduct R C S)) :
    Ideal (Localization.Away e) :=
  P'.map (algebraMap (TensorProduct R C S) (Localization.Away e))

/-- A Tag prime avoiding the chosen idempotent remains prime in the Away
factor. -/
theorem etaleChosenAwayPrime_isPrime
    (e : TensorProduct R C S)
    (P' : Ideal (TensorProduct R C S)) [P'.IsPrime]
    (heP' : e ∉ P') :
    (etaleChosenAwayPrime e P').IsPrime := by
  let T := TensorProduct R C S
  let D := Localization.Away e
  let Q : Ideal D := etaleChosenAwayPrime e P'
  have hdisj : Disjoint ((Submonoid.powers e : Submonoid T) : Set T)
      (P' : Set T) := by
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    exact heP'
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (.powers e) D P' inferInstance hdisj

/-- The prime in the Away factor contracts to the original Tag prime. -/
theorem etaleChosenAwayPrime_liesOver
    (e : TensorProduct R C S)
    (P' : Ideal (TensorProduct R C S)) [P'.IsPrime]
    (heP' : e ∉ P') :
    (etaleChosenAwayPrime e P').LiesOver P' := by
  let T := TensorProduct R C S
  let D := Localization.Away e
  have hdisj : Disjoint ((Submonoid.powers e : Submonoid T) : Set T)
      (P' : Set T) := by
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    exact heP'
  exact IsLocalization.liesOver_map_of_isPrime_disjoint
    (.powers e) D hdisj

/-- Tag uniqueness before localization is exactly uniqueness of the prime
over the pointed base prime in the idempotent Away factor. -/
theorem etaleChosenAway_primesOver_eq_singleton
    (P : Ideal C) [P.IsPrime]
    (e : TensorProduct R C S)
    (P' : Ideal (TensorProduct R C S))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (hunique : ∀ P'' : Ideal (TensorProduct R C S),
      P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') :
    P.primesOver (Localization.Away e) =
      {etaleChosenAwayPrime e P'} := by
  let T := TensorProduct R C S
  let D := Localization.Away e
  let Q : Ideal D := etaleChosenAwayPrime e P'
  let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  let : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  ext J
  constructor
  · rintro ⟨hJprime, hJover⟩
    let : J.IsPrime := hJprime
    let : J.LiesOver P := hJover
    let J₀ : Ideal T := J.comap (algebraMap T D)
    let : J₀.IsPrime := Ideal.IsPrime.under T J
    let : J.LiesOver J₀ := ⟨rfl⟩
    let : J₀.LiesOver P := Ideal.LiesOver.tower_bot J J₀ P
    have heJ₀ : e ∉ J₀ := by
      intro heJ
      have heJD : algebraMap T D e ∈ J := heJ
      exact hJprime.ne_top
        (J.eq_top_of_isUnit_mem heJD
          (IsLocalization.map_units D ⟨e, Submonoid.mem_powers e⟩))
    have hJ₀ : J₀ = P' := hunique J₀ inferInstance inferInstance heJ₀
    rw [Set.mem_singleton_iff]
    calc
      J = J₀.map (algebraMap T D) :=
        (IsLocalization.map_under (.powers e) D J).symm
      _ = P'.map (algebraMap T D) :=
        congrArg (Ideal.map (algebraMap T D)) hJ₀
      _ = Q := rfl
  · intro hJ
    rw [Set.mem_singleton_iff] at hJ
    subst J
    exact ⟨inferInstance, inferInstance⟩

/-- The chosen prime-local factor is finite over the pointed localization.
This is the non-Henselian finiteness step: the singleton fibre, rather than
Hensel's lemma, is what makes localization preserve module finiteness. -/
theorem moduleFinite_etaleChosenAway_localizationAtPrime
    (P : Ideal C) [P.IsPrime]
    (e : TensorProduct R C S)
    (P' : Ideal (TensorProduct R C S))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (hfinite : Module.Finite C (Localization.Away e))
    (hunique : ∀ P'' : Ideal (TensorProduct R C S),
      P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') :
    let Q := etaleChosenAwayPrime e P'
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
    letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    Module.Finite (Localization.AtPrime P) (Localization.AtPrime Q) := by
  dsimp only
  let D := Localization.Away e
  let Q : Ideal D := etaleChosenAwayPrime e P'
  let : Module.Finite C D := hfinite
  let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  let : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  let : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver P Q
  exact Localization.finite_of_primesOver_eq_singleton
    (etaleChosenAway_primesOver_eq_singleton P e P' heP' hunique)

/-- The canonical inclusion of the literal local factor into the integral
closure of the pointed base in its total fraction ring.  No domain claim is
made here: identifying the total fraction ring with the actual selected field
component is precisely the later generic-component comparison.  The map
itself and its integrality require only the Tag singleton fibre. -/
noncomputable def etaleChosenLocalFactorToIntegralClosureAlgHom
    (P : Ideal C) [P.IsPrime]
    (e : TensorProduct R C S)
    (P' : Ideal (TensorProduct R C S))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (hfinite : Module.Finite C (Localization.Away e))
    (hunique : ∀ P'' : Ideal (TensorProduct R C S),
      P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') :
    let Q := etaleChosenAwayPrime e P'
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
    letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    let Cₚ := Localization.AtPrime P
    let Dₚ := Localization.AtPrime Q
    letI : Algebra Cₚ Dₚ :=
      Localization.AtPrime.algebraOfLiesOver P Q
    letI : Module.Finite Cₚ Dₚ :=
      moduleFinite_etaleChosenAway_localizationAtPrime
        P e P' heP' hfinite hunique
    let Ω := FractionRing Dₚ
    letI : Algebra Cₚ Ω :=
      ((algebraMap Dₚ Ω).comp (algebraMap Cₚ Dₚ)).toAlgebra
    Dₚ →ₐ[Cₚ] integralClosure Cₚ Ω := by
  dsimp only
  let Q := etaleChosenAwayPrime e P'
  letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  let Cₚ := Localization.AtPrime P
  let Dₚ := Localization.AtPrime Q
  letI : Algebra Cₚ Dₚ :=
    Localization.AtPrime.algebraOfLiesOver P Q
  letI : Module.Finite Cₚ Dₚ :=
    moduleFinite_etaleChosenAway_localizationAtPrime
      P e P' heP' hfinite hunique
  letI : Algebra.IsIntegral Cₚ Dₚ := Algebra.IsIntegral.of_finite Cₚ Dₚ
  let Ω := FractionRing Dₚ
  letI : Algebra Cₚ Ω :=
    ((algebraMap Dₚ Ω).comp (algebraMap Cₚ Dₚ)).toAlgebra
  let toΩ : Dₚ →ₐ[Cₚ] Ω :=
    { toRingHom := algebraMap Dₚ Ω
      commutes' := fun _ ↦ rfl }
  exact toΩ.codRestrict (integralClosure Cₚ Ω) fun x ↦
    IsIntegral.map_of_comp_eq (RingHom.id Cₚ) (algebraMap Dₚ Ω)
      (by rfl) (Algebra.IsIntegral.isIntegral x)

/-- The canonical local-factor map to the normalization in its total fraction
ring is injective. -/
theorem etaleChosenLocalFactorToIntegralClosureAlgHom_injective
    (P : Ideal C) [P.IsPrime]
    (e : TensorProduct R C S)
    (P' : Ideal (TensorProduct R C S))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (hfinite : Module.Finite C (Localization.Away e))
    (hunique : ∀ P'' : Ideal (TensorProduct R C S),
      P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') :
    let Q := etaleChosenAwayPrime e P'
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
    letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    let Cₚ := Localization.AtPrime P
    let Dₚ := Localization.AtPrime Q
    letI : Algebra Cₚ Dₚ :=
      Localization.AtPrime.algebraOfLiesOver P Q
    letI : Module.Finite Cₚ Dₚ :=
      moduleFinite_etaleChosenAway_localizationAtPrime
        P e P' heP' hfinite hunique
    let Ω := FractionRing Dₚ
    letI : Algebra Cₚ Ω :=
      ((algebraMap Dₚ Ω).comp (algebraMap Cₚ Dₚ)).toAlgebra
    Function.Injective
      (etaleChosenLocalFactorToIntegralClosureAlgHom
        P e P' heP' hfinite hunique) := by
  dsimp only
  let Q := etaleChosenAwayPrime e P'
  let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  let : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  let Cₚ := Localization.AtPrime P
  let Dₚ := Localization.AtPrime Q
  let : Algebra Cₚ Dₚ :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let : Module.Finite Cₚ Dₚ :=
    moduleFinite_etaleChosenAway_localizationAtPrime
      P e P' heP' hfinite hunique
  let Ω := FractionRing Dₚ
  let : Algebra Cₚ Ω :=
    ((algebraMap Dₚ Ω).comp (algebraMap Cₚ Dₚ)).toAlgebra
  intro x y hxy
  apply IsFractionRing.injective Dₚ Ω
  have hxy' := congrArg Subtype.val hxy
  change algebraMap Dₚ Ω x = algebraMap Dₚ Ω y at hxy'
  exact hxy'

/-- Localizing the idempotent factor at its chosen prime is canonically the
same as localizing the original tensor product at the Tag prime. -/
noncomputable def etaleChosenAwayLocalizationAtPrimeAlgEquiv
    (e : TensorProduct R C S)
    (P' : Ideal (TensorProduct R C S)) [P'.IsPrime]
    (heP' : e ∉ P') :
    let Q := etaleChosenAwayPrime e P'
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    Localization.AtPrime Q ≃ₐ[C] Localization.AtPrime P' := by
  dsimp only
  let T := TensorProduct R C S
  let D := Localization.Away e
  let Q : Ideal D := etaleChosenAwayPrime e P'
  letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  letI hDQT : IsLocalization P'.primeCompl (Localization.AtPrime Q) := by
    have hloc :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (.powers e) (Localization.AtPrime Q) Q
    have hsub :
        (Q.comap (algebraMap T D)).primeCompl = P'.primeCompl := by
      ext x
      change (x ∉ Q.comap (algebraMap T D)) ↔ x ∉ P'
      rw [Q.over_def P']
    exact hsub ▸ hloc
  exact
    (IsLocalization.algEquiv P'.primeCompl
      (Localization.AtPrime Q) (Localization.AtPrime P')).restrictScalars C

/-- Base change the Tag tensor product from the pointed etale neighborhood
to the local ring at its chosen point. -/
noncomputable def etaleChosenPointedTensorBaseChangeAlgHom
    (P : Ideal C) [P.IsPrime] :
    (C ⊗[R] S) →ₐ[C] (Localization.AtPrime P ⊗[R] S) :=
  Algebra.TensorProduct.map
    (Algebra.ofId C (Localization.AtPrime P)) (AlgHom.id R S)

/-- The actual Tag prime after base change to the pointed local base. -/
noncomputable def etaleChosenPointedTensorPrime
    (P : Ideal C) [P.IsPrime]
    (P' : Ideal (C ⊗[R] S)) :
    Ideal (Localization.AtPrime P ⊗[R] S) :=
  P'.map (etaleChosenPointedTensorBaseChangeAlgHom
    (R := R) (S := S) P).toRingHom

/-- The actual Tag prime remains prime after pointed-base localization. -/
theorem etaleChosenPointedTensorPrime_isPrime
    (P : Ideal C) [P.IsPrime]
    (P' : Ideal (C ⊗[R] S)) [P'.IsPrime] [P'.LiesOver P] :
    (etaleChosenPointedTensorPrime
      (R := R) (S := S) P P').IsPrime := by
  let T := C ⊗[R] S
  let Cₚ := Localization.AtPrime P
  let BS := Cₚ ⊗[R] S
  let φ := etaleChosenPointedTensorBaseChangeAlgHom
    (R := R) (S := S) P
  let : Algebra T BS := φ.toAlgebra
  let : IsScalarTower C T BS :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : IsScalarTower R T BS :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      simp [RingHom.algebraMap_toAlgebra, φ])
  let : IsLocalization
      (Algebra.algebraMapSubmonoid T P.primeCompl) BS := by
    exact IsLocalization.tensorProduct_tensorProduct
      R S P.primeCompl Cₚ (by
        ext s
        change φ (1 ⊗ₜ[R] s) = 1 ⊗ₜ[R] s
        change (Algebra.TensorProduct.map
          (Algebra.ofId C Cₚ) (AlgHom.id R S))
            (1 ⊗ₜ[R] s) = 1 ⊗ₜ[R] s
        rw [Algebra.TensorProduct.map_tmul, map_one]
        rfl)
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid T P.primeCompl) BS P'
    inferInstance (Ideal.disjoint_primeCompl_of_liesOver P' P)

/-- The pointed-base Tag prime contracts to the original Tag prime. -/
theorem etaleChosenPointedTensorPrime_comap
    (P : Ideal C) [P.IsPrime]
    (P' : Ideal (C ⊗[R] S)) [P'.IsPrime] [P'.LiesOver P] :
    (etaleChosenPointedTensorPrime
      (R := R) (S := S) P P').comap
        (etaleChosenPointedTensorBaseChangeAlgHom
          (R := R) (S := S) P).toRingHom = P' := by
  let T := C ⊗[R] S
  let Cₚ := Localization.AtPrime P
  let BS := Cₚ ⊗[R] S
  let φ := etaleChosenPointedTensorBaseChangeAlgHom
    (R := R) (S := S) P
  let PBS := etaleChosenPointedTensorPrime
    (R := R) (S := S) P P'
  let : Algebra T BS := φ.toAlgebra
  let : IsScalarTower C T BS :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : IsScalarTower R T BS :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      simp [RingHom.algebraMap_toAlgebra, φ])
  let : IsLocalization
      (Algebra.algebraMapSubmonoid T P.primeCompl) BS := by
    exact IsLocalization.tensorProduct_tensorProduct
      R S P.primeCompl Cₚ (by
        ext s
        change φ (1 ⊗ₜ[R] s) = 1 ⊗ₜ[R] s
        change (Algebra.TensorProduct.map
          (Algebra.ofId C Cₚ) (AlgHom.id R S))
            (1 ⊗ₜ[R] s) = 1 ⊗ₜ[R] s
        rw [Algebra.TensorProduct.map_tmul, map_one]
        rfl)
  have hover := IsLocalization.liesOver_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid T P.primeCompl) BS
    (Ideal.disjoint_primeCompl_of_liesOver P' P)
  exact hover.over.symm

/-- The Tag local factor is unchanged when the pointed etale neighborhood is
localized at its chosen point.  More precisely, both displayed local rings
are the localization of the original tensor product at the complement of
the same literal Tag prime.

This is the non-Henselian comparison: no cancellation of the pointed etale
neighborhood with the original local base is used. -/
noncomputable def
    etaleChosenAwayPointedBaseChangeLocalizationAlgEquiv
    (P : Ideal C) [P.IsPrime]
    (e : C ⊗[R] S)
    (P' : Ideal (C ⊗[R] S))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P') :
    let Q := etaleChosenAwayPrime e P'
    let PBS := etaleChosenPointedTensorPrime
      (R := R) (S := S) P P'
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    letI : PBS.IsPrime :=
      etaleChosenPointedTensorPrime_isPrime
        (R := R) (S := S) P P'
    Localization.AtPrime Q ≃ₐ[C] Localization.AtPrime PBS := by
  dsimp only
  let T := C ⊗[R] S
  let D := Localization.Away e
  let Q : Ideal D := etaleChosenAwayPrime e P'
  let Cₚ := Localization.AtPrime P
  let BS := Cₚ ⊗[R] S
  let φ : T →ₐ[C] BS :=
    etaleChosenPointedTensorBaseChangeAlgHom
      (R := R) (S := S) P
  let PBS : Ideal BS := etaleChosenPointedTensorPrime
    (R := R) (S := S) P P'
  letI : Algebra T BS := φ.toAlgebra
  letI : IsScalarTower C T BS :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  letI : IsScalarTower R T BS :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      simp [RingHom.algebraMap_toAlgebra, φ])
  letI hBS : IsLocalization
      (Algebra.algebraMapSubmonoid T P.primeCompl) BS := by
    exact IsLocalization.tensorProduct_tensorProduct
      R S P.primeCompl Cₚ (by
        ext s
        change φ (1 ⊗ₜ[R] s) = 1 ⊗ₜ[R] s
        change (Algebra.TensorProduct.map
          (Algebra.ofId C Cₚ) (AlgHom.id R S))
            (1 ⊗ₜ[R] s) = 1 ⊗ₜ[R] s
        rw [Algebra.TensorProduct.map_tmul, map_one]
        rfl)
  have hPdisj :
      Disjoint
        ((Algebra.algebraMapSubmonoid T P.primeCompl : Submonoid T) : Set T)
        (P' : Set T) :=
    Ideal.disjoint_primeCompl_of_liesOver P' P
  letI : PBS.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid T P.primeCompl) BS P'
      inferInstance hPdisj
  have hPBSoverP' : PBS.LiesOver P' :=
    IsLocalization.liesOver_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid T P.primeCompl) BS hPdisj
  have hPBSunder : PBS.comap (algebraMap T BS) = P' :=
    hPBSoverP'.over.symm
  letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  letI hDQT : IsLocalization P'.primeCompl
      (Localization.AtPrime Q) := by
    have hloc :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (.powers e) (Localization.AtPrime Q) Q
    have hsub :
        (Q.comap (algebraMap T D)).primeCompl = P'.primeCompl := by
      ext x
      change (x ∉ Q.comap (algebraMap T D)) ↔ x ∉ P'
      rw [Q.over_def P']
    exact hsub ▸ hloc
  letI hBSPT : IsLocalization P'.primeCompl
      (Localization.AtPrime PBS) := by
    have hloc :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Algebra.algebraMapSubmonoid T P.primeCompl)
        (Localization.AtPrime PBS) PBS
    have hsub :
        (PBS.comap (algebraMap T BS)).primeCompl = P'.primeCompl := by
      ext x
      change (x ∉ PBS.comap (algebraMap T BS)) ↔ x ∉ P'
      rw [hPBSunder]
    exact hsub ▸ hloc
  exact
    (IsLocalization.algEquiv P'.primeCompl
      (Localization.AtPrime Q)
      (Localization.AtPrime PBS)).restrictScalars C

/-- The pointed-base comparison is linear over the pointed local ring
itself.  The source algebra is the canonical one induced by the chain of
lies-over primes. -/
noncomputable def
    etaleChosenAwayPointedBaseChangeLocalizationAtPrimeAlgEquiv
    (P : Ideal C) [P.IsPrime]
    (e : C ⊗[R] S)
    (P' : Ideal (C ⊗[R] S))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P') :
    let Q := etaleChosenAwayPrime e P'
    let PBS := etaleChosenPointedTensorPrime
      (R := R) (S := S) P P'
    let Cₚ := Localization.AtPrime P
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
    letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    letI : PBS.IsPrime :=
      etaleChosenPointedTensorPrime_isPrime
        (R := R) (S := S) P P'
    letI : Algebra Cₚ (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    Localization.AtPrime Q ≃ₐ[Cₚ] Localization.AtPrime PBS := by
  dsimp only
  let Q := etaleChosenAwayPrime e P'
  let PBS := etaleChosenPointedTensorPrime
    (R := R) (S := S) P P'
  let Cₚ := Localization.AtPrime P
  letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  letI : PBS.IsPrime :=
    etaleChosenPointedTensorPrime_isPrime
      (R := R) (S := S) P P'
  letI : Algebra Cₚ (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let EC : Localization.AtPrime Q ≃ₐ[C]
      Localization.AtPrime PBS :=
    etaleChosenAwayPointedBaseChangeLocalizationAlgEquiv
      (R := R) (S := S) P e P' heP'
  refine AlgEquiv.ofRingEquiv (f := EC.toRingEquiv) fun x ↦ ?_
  have hmaps :
      EC.toRingHom.comp
          (algebraMap Cₚ (Localization.AtPrime Q)) =
        algebraMap Cₚ (Localization.AtPrime PBS) := by
    apply IsLocalization.ringHom_ext P.primeCompl
    ext c
    simp only [RingHom.comp_apply]
    calc
      EC (algebraMap Cₚ (Localization.AtPrime Q)
          (algebraMap C Cₚ c)) =
          EC (algebraMap C (Localization.AtPrime Q) c) := by
            rw [IsScalarTower.algebraMap_apply C Cₚ
              (Localization.AtPrime Q)]
      _ = algebraMap C (Localization.AtPrime PBS) c := EC.commutes c
      _ = algebraMap Cₚ (Localization.AtPrime PBS)
          (algebraMap C Cₚ c) := by
            rw [IsScalarTower.algebraMap_apply C Cₚ
              (Localization.AtPrime PBS)]
  exact DFunLike.congr_fun hmaps x

section SmoothNormalizationComparison

universe uK uL

variable {K : Type uK} {L : Type uL}
variable [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra K L] [Algebra R L] [IsScalarTower R K L]
variable [Algebra.Smooth R C]

/-- Smooth base change identifies the literal tensor product of a
normalization with the relative integral closure in the base-changed
ambient algebra.  This is the production smooth comparison, retained as an
equivalence so that the actual Tag prime can be localized without choosing
a new component. -/
private noncomputable def smoothNormalizationBaseChangeAlgEquiv :
    (C ⊗[R] integralClosure R L) ≃ₐ[C]
      integralClosure C (C ⊗[R] L) :=
  AlgEquiv.ofBijective
    (TensorProduct.toIntegralClosure R C L)
    TensorProduct.toIntegralClosure_bijective_of_smooth

/-- Smooth base change followed by localization at the pointed prime still
preserves integral closure.  The proof composes the production smooth
comparison with the production localization comparison; it does not assume a
new comparison equivalence. -/
private noncomputable def
    pointedSmoothNormalizationBaseChangeAlgEquiv
    (P : Ideal C) [P.IsPrime] :
    let Cₚ := Localization.AtPrime P
    (Cₚ ⊗[R] integralClosure R L) ≃ₐ[Cₚ]
      integralClosure Cₚ (Cₚ ⊗[R] L) := by
  dsimp only
  let Cₚ := Localization.AtPrime P
  have hSmooth : Function.Bijective
      (TensorProduct.toIntegralClosure R C L) :=
    TensorProduct.toIntegralClosure_bijective_of_smooth
  have hLocalization : Function.Bijective
      (TensorProduct.toIntegralClosure C Cₚ (C ⊗[R] L)) :=
    TensorProduct.toIntegralClosure_bijective_of_isLocalization
      (R := C) (S := Cₚ) (B := C ⊗[R] L) P.primeCompl
  exact AlgEquiv.ofBijective
    (TensorProduct.toIntegralClosure R Cₚ L)
    (TensorProduct.toIntegralClosure_bijective_of_tower
      (R := R) (S := C) (T := Cₚ) (B := L)
      hSmooth hLocalization)

/-- The non-Henselian Tag local factor is the local ring at the transported
prime of the smooth base-changed integral closure.  In particular this
comparison preserves the chosen prime; it does not reselect an abstract
generic component. -/
noncomputable def
    etaleChosenLocalFactorSmoothIntegralClosureAlgEquiv
    (e : C ⊗[R] integralClosure R L)
    (P' : Ideal (C ⊗[R] integralClosure R L)) [P'.IsPrime]
    (heP' : e ∉ P') :
    let E := smoothNormalizationBaseChangeAlgEquiv
      (R := R) (C := C) (L := L)
    let Pᵢ := P'.map E.toRingEquiv
    let Q := etaleChosenAwayPrime e P'
    letI : Pᵢ.IsPrime := inferInstance
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    Localization.AtPrime Q ≃ₐ[C] Localization.AtPrime Pᵢ := by
  dsimp only
  let E := smoothNormalizationBaseChangeAlgEquiv
    (R := R) (C := C) (L := L)
  let Pᵢ : Ideal (integralClosure C (C ⊗[R] L)) := P'.map E.toRingEquiv
  let Q := etaleChosenAwayPrime e P'
  letI : Pᵢ.IsPrime := inferInstance
  letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  have hcomap : P' = Pᵢ.comap E.toRingHom := by
    symm
    exact Ideal.comap_map_of_bijective E.toRingEquiv E.bijective
  exact
    (etaleChosenAwayLocalizationAtPrimeAlgEquiv e P' heP').trans
      (Localization.localAlgEquiv P' Pᵢ E hcomap)

/-- The actual generic field component selected by the non-Henselian Tag
local factor.

After localizing the pointed etale base at `P`, smooth base change identifies
the Tag tensor product with the normalization in its generic algebra.  That
generic algebra is a reduced Artinian algebra over `L`; hence the transported
Tag prime canonically selects one literal maximal-ideal quotient field and a
prime in its normalization.  The resulting local ring is the original Tag
local factor, as an algebra over the pointed local base. -/
theorem
    exists_etaleChosenLocalFactor_finiteGenericFiberComponent_algEquiv
    [Algebra.Etale R C]
    (P : Ideal C) [P.IsPrime]
    (e : C ⊗[R] integralClosure R L)
    (P' : Ideal (C ⊗[R] integralClosure R L))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P') :
    let Cₚ := Localization.AtPrime P
    let G := Cₚ ⊗[R] L
    let Q := etaleChosenAwayPrime e P'
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
    letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    letI : Algebra Cₚ (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    ∃ (m : MaximalSpectrum G)
      (q : PrimeSpectrum
        (integralClosure Cₚ
          (FiniteEtaleGenericFiberComponent m.asIdeal))),
      Nonempty
        (Localization.AtPrime Q ≃ₐ[Cₚ]
          Localization.AtPrime q.asIdeal) := by
  dsimp only
  let Cₚ := Localization.AtPrime P
  let Sₙ := integralClosure R L
  let BS := Cₚ ⊗[R] Sₙ
  let G := Cₚ ⊗[R] L
  let Q := etaleChosenAwayPrime e P'
  let PBS := etaleChosenPointedTensorPrime
    (R := R) (S := Sₙ) P P'
  let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  let : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  let : Algebra Cₚ (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let : PBS.IsPrime :=
    etaleChosenPointedTensorPrime_isPrime
      (R := R) (S := Sₙ) P P'
  let Epoint : BS ≃ₐ[Cₚ] integralClosure Cₚ G :=
    pointedSmoothNormalizationBaseChangeAlgEquiv
      (R := R) (C := C) (L := L) P
  let Pnorm : Ideal (integralClosure Cₚ G) :=
    PBS.map Epoint.toRingEquiv
  let : Pnorm.IsPrime := by
    exact Ideal.map_isPrime_of_surjective Epoint.surjective fun x hx ↦ by
      have hx0 : x = 0 := Epoint.injective (hx.trans Epoint.map_zero.symm)
      subst x
      exact PBS.zero_mem
  have hcomap : PBS = Pnorm.comap Epoint.toRingHom := by
    symm
    exact Ideal.comap_map_of_bijective Epoint.toRingEquiv Epoint.bijective
  let Esmooth : Localization.AtPrime PBS ≃ₐ[Cₚ]
      Localization.AtPrime Pnorm :=
    Localization.localAlgEquiv PBS Pnorm Epoint hcomap
  let ETag : Localization.AtPrime Q ≃ₐ[Cₚ]
      Localization.AtPrime PBS :=
    etaleChosenAwayPointedBaseChangeLocalizationAtPrimeAlgEquiv
      (R := R) (S := Sₙ) P e P' heP'
  let Gleft := L ⊗[R] Cₚ
  let : Algebra L G := Algebra.TensorProduct.rightAlgebra
  let commL : Gleft ≃ₐ[L] G :=
    { toRingEquiv :=
        (Algebra.TensorProduct.comm R L Cₚ).toRingEquiv
      commutes' := by
        intro l
        exact (Algebra.TensorProduct.right_algebraMap_apply l).symm }
  let : Algebra.FormallyEtale R Cₚ := inferInstance
  let : Algebra.FormallyEtale L Gleft := inferInstance
  let : Module.Finite L Gleft :=
    Algebra.FormallyUnramified.finite_of_free L Gleft
  let : IsArtinianRing Gleft := IsArtinianRing.of_finite L Gleft
  let : IsArtinianRing G := commL.toRingEquiv.isArtinianRing
  let : Algebra.EssFiniteType L G :=
    Algebra.EssFiniteType.of_surjective commL.toAlgHom commL.surjective
  let : Algebra.FormallyEtale L G :=
    Algebra.FormallyEtale.of_equiv commL
  let : IsReduced G :=
    Algebra.FormallyUnramified.isReduced_of_field L G
  obtain ⟨m, q, ⟨Ecomponent⟩⟩ :=
    exists_integralClosure_artinianComponent_localizationAtPrime_algEquiv
      Pnorm
  exact ⟨m, q, ⟨(ETag.trans Esmooth).trans Ecomponent⟩⟩

end SmoothNormalizationComparison

end EtaleFundamentalGroups

end
