/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.Localization.FractionFieldComparison
import Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenLocalizationEtale
import Nyll.EtaleFundamentalGroups.Kummer.Completions.Conditional.ChosenFactorTargetAction

/-!
# Conditional completed root actions in the selected generic component

The completed conditional root cover has a chosen local normalization factor
inside an already selected finite generic component `M`.  Completeness and
finite etaleness make that localization a genuine finite chosen factor, so
the completed chosen-factor theorem supplies all root coordinates in its
literal fraction ring.  The canonical normalization-localization comparison
then transports those coordinates to the same `M`.

No action on an unrelated global field, universal embedding, or
right-coordinate bijectivity is used.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe u

/-- The canonical residue lift of the localization selected inside a fixed
generic component.  Henselian localization and the unique closed prime are
constructed here once, instead of being repeated in every theorem type and
proof that names this lift. -/
noncomputable def completedChosenFactorComponentResidueLift_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i,
      a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let aHat : Fin r → Ahat := fun i ↦ algebraMap A Ahat (a i)
    let Bhat := iteratedRadical Ahat r n aHat
    let hstageHat : ∀ i,
        aHat i ∈ IsLocalRing.maximalIdeal Ahat ∨ n i = 1 := fun i ↦ by
      rcases hstage i with ha | hOne
      · left
        rw [AdicCompletion.maximalIdeal_eq_map]
        exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
      · exact Or.inr hOne
    letI : IsLocalRing Bhat :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n aHat hn hstageHat
    ∀ {M : Type u} [Field M] [Algebra Bhat M],
      ∀ (q : Ideal (integralClosure Bhat M)) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal Bhat)],
        Algebra.Etale Bhat (integralClosure Bhat M) → CommAlgCat Ahat := by
  dsimp only
  intro M _ _ q _ _ hEtale
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let aHat : Fin r → Ahat := fun i ↦ algebraMap A Ahat (a i)
  let Bhat := iteratedRadical Ahat r n aHat
  have hstageHat : ∀ i,
      aHat i ∈ IsLocalRing.maximalIdeal Ahat ∨ n i = 1 := fun i ↦ by
    rcases hstage i with ha | hOne
    · left
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
    · exact Or.inr hOne
  letI : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n aHat hn hstageHat
  have hmaxFG : (IsLocalRing.maximalIdeal Ahat).FG := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.FG.map
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
      (algebraMap A Ahat)
  letI : HenselianLocalRing Bhat :=
    henselianLocalRing_iteratedRadical_of_isAdicComplete_of_fg_of_mem_or_eq_one
      hmaxFG n aHat hn hstageHat
  letI : Module.FaithfullyFlat Ahat Bhat :=
    faithfullyFlat_iteratedRadical n aHat hn
  letI : IsLocalHom (algebraMap Ahat Bhat) := by
    let : Module.Finite Ahat Bhat := finite_iteratedRadical n aHat hn
    let : Algebra.IsIntegral Ahat Bhat :=
      Algebra.IsIntegral.of_finite Ahat Bhat
    exact Algebra.IsIntegral.isLocalHom Ahat Bhat
  let C := integralClosure Bhat M
  letI : Algebra.Etale Bhat C := hEtale
  let D := Localization.AtPrime q
  letI : Module.Finite Bhat D :=
    moduleFinite_localizationAtPrime_of_henselian_of_etale q
  letI : Algebra.Etale Bhat D :=
    etale_localizationAtPrime_of_henselian_of_etale q
  letI : IsLocalHom (algebraMap Bhat D) :=
    isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal q
  let aDAlgebra : Algebra Ahat D :=
    ((algebraMap Bhat D).comp (algebraMap Ahat Bhat)).toAlgebra
  letI : Algebra Ahat D := aDAlgebra
  letI : IsScalarTower Ahat Bhat D :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalHom (algebraMap Ahat D) := by
    rw [IsScalarTower.algebraMap_eq Ahat Bhat D]
    exact
      RingHom.isLocalHom_comp
        (algebraMap Bhat D) (algebraMap Ahat Bhat)
  let k := IsLocalRing.ResidueField Ahat
  let kB := IsLocalRing.ResidueField Bhat
  let l := IsLocalRing.ResidueField D
  let eResidue : k ≃ₐ[k] kB :=
    AlgEquiv.ofBijective (Algebra.ofId k kB)
      (residueFieldMap_bijective_iteratedRadical_of_mem_or_eq_one
        n aHat hn hstageHat)
  letI : Module.Finite k kB :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  letI : Module.Finite k l := Module.Finite.trans kB l
  letI : Algebra.IsSeparable k kB :=
    AlgEquiv.Algebra.isSeparable eResidue
  letI : Algebra.IsSeparable k l := Algebra.IsSeparable.trans k kB l
  exact CommAlgCat.of Ahat (FiniteEtaleResidueLift Ahat l)

/-- Evaluation of an algebra equivalence on a base-ring coordinate, isolated
from the larger completed-factor instance environment. -/
private theorem algEquiv_apply_algebraMap
    {D F M : Type u} [CommRing D] [CommRing F] [CommRing M]
    [Algebra D F] [Algebra D M]
    (e : F ≃ₐ[D] M) (x : D) :
    e (algebraMap D F x) = algebraMap D M x :=
  e.commutes x

/-- Transport an already constructed radical action across compatible
fraction-field equivalences.  The source and target algebra structures are
explicit inputs, so this proof performs no reconstruction of the completed
chosen-factor instance tower. -/
private theorem transport_iteratedRadicalTargetAction
    {Ahat D F M : Type u}
    [CommRing Ahat] [CommRing D] [Field F] [Field M]
    {r : ℕ} (n : Fin r → ℕ) (aHat : Fin r → Ahat)
    [Algebra Ahat F] [Algebra Ahat M]
    [Algebra D F] [Algebra D M]
    [Algebra (iteratedRadical Ahat r n aHat) D]
    [Algebra (iteratedRadical Ahat r n aHat) M]
    [IsScalarTower (iteratedRadical Ahat r n aHat) D M]
    [IsScalarTower Ahat (iteratedRadical Ahat r n aHat) M]
    (eDM : F ≃ₐ[D] M) (eAhat : F ≃ₐ[Ahat] M)
    (hcompat : ∀ y, eAhat y = eDM y)
    (xF : Fin r → F)
    (hxF : ∀ i, xF i ^ n i = algebraMap Ahat F (aHat i))
    (hinjectiveF : Function.Injective
      (iteratedRadicalTargetAlgHom n aHat xF hxF))
    (hcoordinatesF : ∀ i, xF i =
      algebraMap D F
        (algebraMap (iteratedRadical Ahat r n aHat) D
          (iteratedRadicalRoot Ahat n aHat i))) :
    ∃ (xM : Fin r → M)
        (hxM : ∀ i, xM i ^ n i = algebraMap Ahat M (aHat i)),
      Function.Injective
          (iteratedRadicalTargetAlgHom n aHat xM hxM) ∧
        iteratedRadicalTargetAlgHom n aHat xM hxM =
          (Algebra.ofId (iteratedRadical Ahat r n aHat) M).restrictScalars Ahat ∧
        ∀ i, xM i =
          algebraMap D M
            (algebraMap (iteratedRadical Ahat r n aHat) D
              (iteratedRadicalRoot Ahat n aHat i)) := by
  let Bhat := iteratedRadical Ahat r n aHat
  let xM : Fin r → M := fun i ↦ eAhat (xF i)
  have hxM : ∀ i, xM i ^ n i = algebraMap Ahat M (aHat i) := by
    intro i
    calc
      xM i ^ n i = eAhat (xF i ^ n i) :=
        (map_pow eAhat (xF i) (n i)).symm
      _ = eAhat (algebraMap Ahat F (aHat i)) := congrArg eAhat (hxF i)
      _ = algebraMap Ahat M (aHat i) := eAhat.commutes (aHat i)
  have hAction :
      iteratedRadicalTargetAlgHom n aHat xM hxM =
        eAhat.toAlgHom.comp
          (iteratedRadicalTargetAlgHom n aHat xF hxF) := by
    apply iteratedRadical_algHom_ext n aHat
    intro i
    rw [iteratedRadicalTargetAlgHom_apply_root,
      AlgHom.comp_apply, iteratedRadicalTargetAlgHom_apply_root]
    rfl
  have hinjectiveM : Function.Injective
      (iteratedRadicalTargetAlgHom n aHat xM hxM) := by
    rw [hAction]
    exact eAhat.injective.comp hinjectiveF
  have hcoordinatesM : ∀ i, xM i =
      algebraMap D M
        (algebraMap Bhat D
          (iteratedRadicalRoot Ahat n aHat i)) := by
    intro i
    calc
      eAhat (xF i) = eDM (xF i) := hcompat (xF i)
      _ = eDM
          (algebraMap D F
            (algebraMap Bhat D
              (iteratedRadicalRoot Ahat n aHat i))) :=
        congrArg eDM (hcoordinatesF i)
      _ = algebraMap D M
          (algebraMap Bhat D
            (iteratedRadicalRoot Ahat n aHat i)) :=
        algEquiv_apply_algebraMap eDM _
  have hCanonicalAction :
      iteratedRadicalTargetAlgHom n aHat xM hxM =
        (Algebra.ofId Bhat M).restrictScalars Ahat := by
    apply iteratedRadical_algHom_ext n aHat
    intro i
    rw [iteratedRadicalTargetAlgHom_apply_root, hcoordinatesM i]
    exact
      (IsScalarTower.algebraMap_apply Bhat D M
        (iteratedRadicalRoot Ahat n aHat i)).symm
  exact ⟨xM, hxM, hinjectiveM, hCanonicalAction, hcoordinatesM⟩

/-- The complete dependent result carried by a selected conditional
component.  Keeping it opaque prevents callers from repeatedly normalizing
the canonical residue-lift and algebra setup merely to state the result. -/
def HasCompletedChosenFactorComponentTargetAction
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i,
      a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) : Prop :=
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let aHat : Fin r → Ahat := fun i ↦ algebraMap A Ahat (a i)
  let Bhat := iteratedRadical Ahat r n aHat
  let hstageHat : ∀ i,
      aHat i ∈ IsLocalRing.maximalIdeal Ahat ∨ n i = 1 := fun i ↦ by
    rcases hstage i with ha | hOne
    · left
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
    · exact Or.inr hOne
  letI : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n aHat hn hstageHat
  ∀ [IsDomain Bhat],
    ∀ {M : Type u} [Field M]
    [Algebra Bhat M]
    [Algebra (FractionRing Bhat) M]
    [IsScalarTower Bhat (FractionRing Bhat) M]
    [FiniteDimensional (FractionRing Bhat) M],
    ∀ (q : Ideal (integralClosure Bhat M)) [q.IsPrime]
      [q.LiesOver (IsLocalRing.maximalIdeal Bhat)],
      ∀ (hEtale : Algebra.Etale Bhat (integralClosure Bhat M)),
        let D := Localization.AtPrime q
        let CResidue :=
          completedChosenFactorComponentResidueLift_of_mem_or_eq_one
            n a hn hstage (M := M) q hEtale
        let dComponentAlgebra : Algebra D M := by
          let C := integralClosure Bhat M
          letI : IsFractionRing C M :=
            IsIntegralClosure.isFractionRing_of_finite_extension
              Bhat (FractionRing Bhat) M C
          exact localizationAtPrimeToFractionFieldAlgebra (K := M) q
        letI : Algebra D M := dComponentAlgebra
        let aComponentAlgebra : Algebra Ahat M :=
          ((algebraMap Bhat M).comp (algebraMap Ahat Bhat)).toAlgebra
        letI : Algebra Ahat M := aComponentAlgebra
        letI : IsScalarTower Ahat Bhat M :=
          IsScalarTower.of_algebraMap_eq' rfl
        Nonempty
            ((Bhat ⊗[Ahat] CResidue) ≃ₐ[Bhat] D) ∧
          Nonempty (FractionRing D ≃ₐ[D] M) ∧
          ∃ (x : Fin r → M)
              (hx : ∀ i, x i ^ n i = algebraMap Ahat M (aHat i)),
            Function.Injective
                (iteratedRadicalTargetAlgHom n aHat x hx) ∧
              iteratedRadicalTargetAlgHom n aHat x hx =
                  (Algebra.ofId Bhat M).restrictScalars Ahat ∧
                ∀ i, x i =
                  algebraMap D M
                    (algebraMap Bhat D
                      (iteratedRadicalRoot Ahat n aHat i))

/-- A finite-etale normalization of the completed conditional root cover,
localized at a specified closed prime, produces an injective simultaneous
root action in the *same selected generic component* `M`.

The finite local factor, its residue-lift tensor presentation, and its
fraction-field comparison with `M` are all constructed internally.  The
returned action is explicitly identified with the existing map `Bhat → M`.
Its coordinate formula records that each target root is the image of the
distinguished root through the canonical localization map `D → M`.
-/
theorem
    exists_completedChosenFactorComponentTargetAction_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i,
      a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    HasCompletedChosenFactorComponentTargetAction n a hn hstage := by
  unfold HasCompletedChosenFactorComponentTargetAction
  dsimp only
  intro _ M _ _ _ _ _ q _ _ hEtale
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let aHat : Fin r → Ahat := fun i ↦ algebraMap A Ahat (a i)
  let Bhat := iteratedRadical Ahat r n aHat
  have hstageHat : ∀ i,
      aHat i ∈ IsLocalRing.maximalIdeal Ahat ∨ n i = 1 := fun i ↦ by
    rcases hstage i with ha | hOne
    · left
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
    · exact Or.inr hOne
  let : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n aHat hn hstageHat
  have hmaxFG : (IsLocalRing.maximalIdeal Ahat).FG := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.FG.map
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
      (algebraMap A Ahat)
  let : HenselianLocalRing Bhat :=
    henselianLocalRing_iteratedRadical_of_isAdicComplete_of_fg_of_mem_or_eq_one
      hmaxFG n aHat hn hstageHat
  let C := integralClosure Bhat M
  let : Algebra.Etale Bhat C := hEtale
  let D := Localization.AtPrime q
  let : Module.Finite Bhat D :=
    moduleFinite_localizationAtPrime_of_henselian_of_etale q
  let : Algebra.Etale Bhat D :=
    etale_localizationAtPrime_of_henselian_of_etale q
  let : IsLocalHom (algebraMap Bhat D) :=
    isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal q
  let aDAlgebra : Algebra Ahat D :=
    ((algebraMap Bhat D).comp (algebraMap Ahat Bhat)).toAlgebra
  let : Algebra Ahat D := aDAlgebra
  let : IsScalarTower Ahat Bhat D :=
    IsScalarTower.of_algebraMap_eq' rfl
  let qD := IsLocalRing.maximalIdeal D
  let : qD.IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal D).isPrime
  let : qD.LiesOver (IsLocalRing.maximalIdeal Bhat) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap Bhat D)).symm⟩
  have hunique : ∀ Q : Ideal D, Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal Bhat) → Q = qD := by
    intro Q hQPrime hQOver
    let : Q.IsPrime := hQPrime
    let : Algebra.IsIntegral Bhat D := Algebra.IsIntegral.of_finite Bhat D
    have hQMaximal : Q.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
        (algebraMap Bhat D) (fun x ↦ Algebra.IsIntegral.isIntegral x) Q <| by
          rw [← Ideal.under_def,
            ← hQOver.over]
          exact IsLocalRing.maximalIdeal.isMaximal Bhat
    exact IsLocalRing.eq_maximalIdeal hQMaximal
  let CResidue :=
    completedChosenFactorComponentResidueLift_of_mem_or_eq_one
      n a hn hstage (M := M) q hEtale
  let F := FractionRing D
  let bFracAlgebra : Algebra Bhat F :=
    ((algebraMap D F).comp (algebraMap Bhat D)).toAlgebra
  let : Algebra Bhat F := bFracAlgebra
  let aFracAlgebra : Algebra Ahat F :=
    ((algebraMap Bhat F).comp (algebraMap Ahat Bhat)).toAlgebra
  let : Algebra Ahat F := aFracAlgebra
  obtain ⟨hTensor, xF, hxF, hinjectiveF, hcoordinatesF⟩ :=
    exists_completedChosenFactorTensorAndFractionTargetAction_of_mem_or_eq_one
      n a hn hstage (D := D) qD hunique
  have hTensorComponent : Nonempty
      ((Bhat ⊗[Ahat] CResidue) ≃ₐ[Bhat] D) := by
    change Nonempty
      ((Bhat ⊗[Ahat]
        completedChosenFactorResidueLift_of_mem_or_eq_one
          n aHat hn hstageHat qD hunique) ≃ₐ[Bhat] D)
    exact hTensor
  let : IsFractionRing C M :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      Bhat (FractionRing Bhat) M C
  let dComponentAlgebra : Algebra D M :=
    localizationAtPrimeToFractionFieldAlgebra (K := M) q
  let : Algebra D M := dComponentAlgebra
  let : IsScalarTower C D M :=
    localizationAtPrimeToFractionField_isScalarTower (K := M) q
  let : IsScalarTower Bhat D M := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    calc
      algebraMap Bhat M z =
          algebraMap C M (algebraMap Bhat C z) :=
        IsScalarTower.algebraMap_apply Bhat C M z
      _ = algebraMap D M (algebraMap C D (algebraMap Bhat C z)) :=
        IsScalarTower.algebraMap_apply C D M _
      _ = algebraMap D M (algebraMap Bhat D z) := by
        rw [IsScalarTower.algebraMap_apply Bhat C D z]
  let aComponentAlgebra : Algebra Ahat M :=
    ((algebraMap Bhat M).comp (algebraMap Ahat Bhat)).toAlgebra
  let : Algebra Ahat M := aComponentAlgebra
  let : IsScalarTower Ahat Bhat M :=
    IsScalarTower.of_algebraMap_eq' rfl
  let eDM : F ≃ₐ[D] M :=
    integralClosureLocalizationFractionRingAlgEquiv
      (B := Bhat) (K := FractionRing Bhat) (M := M) q
  let eAhat : F ≃ₐ[Ahat] M :=
    { toRingEquiv := eDM.toRingEquiv
      commutes' := by
        intro z
        change eDM
            (algebraMap D F
              (algebraMap Bhat D (algebraMap Ahat Bhat z))) =
          algebraMap Bhat M (algebraMap Ahat Bhat z)
        rw [eDM.commutes]
        exact
          (IsScalarTower.algebraMap_apply Bhat D M
            (algebraMap Ahat Bhat z)).symm }
  obtain ⟨xM, hxM, hinjectiveM, hCanonicalAction, hcoordinatesM⟩ :=
    transport_iteratedRadicalTargetAction
      n aHat eDM eAhat (fun _ ↦ rfl)
        xF hxF hinjectiveF hcoordinatesF
  exact
    ⟨hTensorComponent, ⟨eDM⟩, xM, hxM, hinjectiveM,
      hCanonicalAction, hcoordinatesM⟩

end EtaleFundamentalGroups.Kummer

end
