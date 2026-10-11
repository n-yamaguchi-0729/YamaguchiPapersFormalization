/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Completions.Conditional.IteratedRadical
import EtaleFundamentalGroups.Kummer.IteratedRadical.TargetAction

/-!
# A full target action from a conditional completed chosen factor

A uniquely selected finite-etale local factor over the completed conditional
root cover already carries every radical coordinate through its structure
map.  If that factor is a domain, composing with its fraction field puts all
coordinates in one field.  This includes exponent-one stages without any
closed-point condition on their radicands.

The theorem below returns the finite-residue-lift tensor presentation and the
field-valued action together.  It deliberately does not identify that
fraction field with an independently supplied global target field: such an
identification is additional generic-component data, not a consequence of
completion or of the residue lift.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe u

/-- Algebra maps out of an iterated radical are determined by all of its
distinguished root coordinates. -/
theorem iteratedRadical_algHom_ext
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    {f g : iteratedRadical A r n a →ₐ[A] S}
    (hroot : ∀ i,
      f (iteratedRadicalRoot A n a i) =
        g (iteratedRadicalRoot A n a i)) :
    f = g := by
  induction r with
  | zero =>
    apply AlgHom.ext
    intro z
    exact (f.commutes z).trans (g.commutes z).symm
  | succ r ih =>
    let T : CommAlgCat.{u} A := iteratedRadical A r (Fin.init n) (Fin.init a)
    let p : Polynomial T := Polynomial.X ^ n (Fin.last r) -
      Polynomial.C (algebraMap A T (a (Fin.last r)))
    let f' : AdjoinRoot p →ₐ[A] S := f
    let g' : AdjoinRoot p →ₐ[A] S := g
    have hfg : f' = g' := by
      apply AdjoinRoot.algHom_ext'
      · apply ih (Fin.init n) (Fin.init a)
        intro i
        exact (congrArg f' (iteratedRadicalRoot_castSucc n a i)).symm.trans
          ((hroot i.castSucc).trans (congrArg g' (iteratedRadicalRoot_castSucc n a i)))
      · exact (congrArg f' (iteratedRadicalRoot_last n a)).symm.trans
          ((hroot (Fin.last r)).trans (congrArg g' (iteratedRadicalRoot_last n a)))
    exact hfg

/-- The residue lift attached to the unique closed factor of a conditional
iterated radical.  All local and residue-field instances are fixed inside
this construction, so downstream statements do not have to repeat that
instance environment merely to name the lift. -/
abbrev completedChosenFactorResidueLift_of_mem_or_eq_one
    {Ahat D : Type u} [CommRing Ahat] [IsLocalRing Ahat]
    {r : ℕ} (n : Fin r → ℕ) (aHat : Fin r → Ahat)
    (hn : ∀ i, 0 < n i)
    (hstageHat : ∀ i,
      aHat i ∈ IsLocalRing.maximalIdeal Ahat ∨ n i = 1)
    [CommRing D]
    [Algebra (iteratedRadical Ahat r n aHat) D]
    [Algebra Ahat D]
    [IsScalarTower Ahat (iteratedRadical Ahat r n aHat) D]
    [Module.Finite (iteratedRadical Ahat r n aHat) D]
    [Algebra.Etale (iteratedRadical Ahat r n aHat) D]
    [IsLocalRing (iteratedRadical Ahat r n aHat)]
    (q : Ideal D) [q.IsPrime]
    [q.LiesOver
      (IsLocalRing.maximalIdeal (iteratedRadical Ahat r n aHat))]
    (hunique : ∀ Q : Ideal D, Q.IsPrime →
      Q.LiesOver
        (IsLocalRing.maximalIdeal (iteratedRadical Ahat r n aHat)) →
      Q = q) : Type u := by
  let Bhat := iteratedRadical Ahat r n aHat
  letI : Module.FaithfullyFlat Ahat Bhat :=
    faithfullyFlat_iteratedRadical n aHat hn
  letI : IsLocalHom (algebraMap Ahat Bhat) := by
    let : Module.Finite Ahat Bhat := finite_iteratedRadical n aHat hn
    let : Algebra.IsIntegral Ahat Bhat :=
      Algebra.IsIntegral.of_finite Ahat Bhat
    exact Algebra.IsIntegral.isLocalHom Ahat Bhat
  letI : IsLocalRing D :=
    isLocalRing_of_unique_prime_over_maximal q hunique
  letI : IsLocalHom (algebraMap Bhat D) :=
    isLocalHom_of_unique_prime_over_maximal q hunique
  letI : Module.FaithfullyFlat Bhat D :=
    faithfullyFlat_of_unique_prime_over_maximal q hunique
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
  exact FiniteEtaleResidueLift Ahat l

/-- A uniquely chosen finite-etale local factor over a completed conditional
iterated radical supplies, in one call,

* its finite-residue-lift tensor presentation; and
* an injective simultaneous action of the whole completed root cover on the
  fraction field of that same chosen factor.

The domain assumption on `D` is honest in the intended application, where
`D` is a localization of a normalization inside a field.  No domain claim is
made for an arbitrary finite-etale local algebra. -/
theorem
    exists_completedChosenFactorTensorAndFractionTargetAction_of_mem_or_eq_one
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
    ∀ {D : Type u} [CommRing D] [IsDomain D]
      [Algebra Bhat D] [Algebra Ahat D]
      [IsScalarTower Ahat Bhat D]
      [Module.Finite Bhat D] [Algebra.Etale Bhat D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal Bhat)],
        ∀ (hunique : ∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal Bhat) → Q = q),
          let C :=
            completedChosenFactorResidueLift_of_mem_or_eq_one
              n aHat hn hstageHat q hunique
          let F := FractionRing D
          let bFracAlgebra : Algebra Bhat F :=
            ((algebraMap D F).comp (algebraMap Bhat D)).toAlgebra
          letI : Algebra Bhat F := bFracAlgebra
          let aFracAlgebra : Algebra Ahat F :=
            ((algebraMap Bhat F).comp (algebraMap Ahat Bhat)).toAlgebra
          letI : Algebra Ahat F := aFracAlgebra
          Nonempty
              ((Bhat ⊗[Ahat] C) ≃ₐ[Bhat] D) ∧
            ∃ (x : Fin r → F)
                (hx : ∀ i, x i ^ n i = algebraMap Ahat F (aHat i)),
                Function.Injective
                  (iteratedRadicalTargetAlgHom n aHat x hx) ∧
                ∀ i, x i =
                  algebraMap D F
                    (algebraMap Bhat D
                      (iteratedRadicalRoot Ahat n aHat i)) := by
  dsimp only
  intro D _ _ _ _ _ _ _ q _ _ hunique
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
  let : Module.FaithfullyFlat Ahat Bhat :=
    faithfullyFlat_iteratedRadical n aHat hn
  let : IsLocalHom (algebraMap Ahat Bhat) := by
    let : Module.Finite Ahat Bhat := finite_iteratedRadical n aHat hn
    let : Algebra.IsIntegral Ahat Bhat :=
      Algebra.IsIntegral.of_finite Ahat Bhat
    exact Algebra.IsIntegral.isLocalHom Ahat Bhat
  let : IsLocalRing D :=
    isLocalRing_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap Bhat D) :=
    isLocalHom_of_unique_prime_over_maximal q hunique
  let : Module.FaithfullyFlat Bhat D :=
    faithfullyFlat_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap Ahat D) := by
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
  let : Module.Finite k kB :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  let : Module.Finite k l := Module.Finite.trans kB l
  let : Algebra.IsSeparable k kB :=
    AlgEquiv.Algebra.isSeparable eResidue
  let : Algebra.IsSeparable k l := Algebra.IsSeparable.trans k kB l
  let C := completedChosenFactorResidueLift_of_mem_or_eq_one
    n aHat hn hstageHat q hunique
  let F := FractionRing D
  let bFracAlgebra : Algebra Bhat F :=
    ((algebraMap D F).comp (algebraMap Bhat D)).toAlgebra
  let : Algebra Bhat F := bFracAlgebra
  let aFracAlgebra : Algebra Ahat F :=
    ((algebraMap Bhat F).comp (algebraMap Ahat Bhat)).toAlgebra
  let : Algebra Ahat F := aFracAlgebra
  have hTensor : Nonempty
      ((Bhat ⊗[Ahat] C) ≃ₐ[Bhat] D) := by
    change Nonempty
      ((Bhat ⊗[Ahat] FiniteEtaleResidueLift Ahat l) ≃ₐ[Bhat] D)
    simpa only [Ahat, aHat, Bhat, l] using
      exists_baseChange_chosenFactorAlgEquiv_iteratedRadicalCompletion_of_mem_or_eq_one
        n a hn hstage (D := D) q hunique
  let x : Fin r → F := fun i ↦
    algebraMap Bhat F (iteratedRadicalRoot Ahat n aHat i)
  have hx : ∀ i, x i ^ n i = algebraMap Ahat F (aHat i) := by
    intro i
    change
      (algebraMap Bhat F (iteratedRadicalRoot Ahat n aHat i)) ^ n i =
        algebraMap Ahat F (aHat i)
    rw [← map_pow, iteratedRadicalRoot_pow]
    rfl
  let inclusion : Bhat →ₐ[Ahat] F :=
    { algebraMap Bhat F with
      commutes' := fun _ ↦ rfl }
  have hAction : iteratedRadicalTargetAlgHom n aHat x hx = inclusion := by
    apply iteratedRadical_algHom_ext n aHat
    intro i
    rw [iteratedRadicalTargetAlgHom_apply_root]
    rfl
  have hInclusion : Function.Injective inclusion := by
    exact
      (IsFractionRing.injective D F).comp
        (FaithfulSMul.algebraMap_injective Bhat D)
  refine ⟨hTensor, x, hx, ?_, ?_⟩
  · rw [hAction]
    exact hInclusion
  · intro i
    rfl

end EtaleFundamentalGroups.Kummer

end
