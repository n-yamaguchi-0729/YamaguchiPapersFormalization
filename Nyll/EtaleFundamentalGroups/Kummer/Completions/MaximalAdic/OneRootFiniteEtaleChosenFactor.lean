/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.IsTensorProduct
import Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenLocalizationEtale
import Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.CompletionBaseChange
import Nyll.EtaleFundamentalGroups.Kummer.Completions.MaximalAdic.RegularPairNoetherian

/-!
# A finite etale chosen factor after one-root completion

Let `B₀` be the one-root radical of a regular parameter `y` over a
Noetherian local ring `R`, and let `E / B₀` be finite etale with a chosen
closed prime `p`.  Put `A = R̂`, form the corresponding one-root radical
`B̂ / A`, and retain the literal completion tensor

`T = A ⊗[R] E`.

The radical base-change square is a pushout.  Cancelling this pushout gives
the canonical comparison

`B̂ ⊗[B₀] E ≃ T`.

It transports finite etaleness to `T / B̂`.  Independently, exact extension
of `p` along `E → T` is a maximal ideal.  Its contraction to the local ring
`B̂` is therefore the closed point.  Since the regular pair makes `A`
Noetherian and complete, `B̂` is Henselian; localization at the retained
prime is consequently finite etale and has a unique prime over the closed
point.

No domain assertion about the whole tensor ring `T`, and no comparison with
an independently chosen component or normalization prime, is used.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing
open RingTheory.Sequence
open scoped TensorProduct

universe uR uE

/-- The canonical `R`-algebra structure on an algebra over the one-root
radical.  Naming it keeps the literal tensor `R̂ ⊗[R] E` independent of a
public scalar-tower hypothesis. -/
@[reducible]
noncomputable def oneRootFiniteEtaleBaseAlgebra
    {R : Type uR} [CommRing R] {N : ℕ} {y : R}
    {E : Type uE} [CommRing E]
    [Algebra
      (iteratedRadical R 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E] :
    Algebra R E :=
  ((algebraMap
      (iteratedRadical R 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E).comp
    (algebraMap R
      (iteratedRadical R 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)))).toAlgebra

/-- Cancelling the completed one-root pushout identifies base change of the
finite-etale algebra over the root cover with the literal completion tensor.

This is kept as a ring equivalence so that the named transported
`B̂`-algebra structure below is the only `B̂`-algebra structure placed on the
literal tensor. -/
noncomputable def maximalAdicCompletionOneRootTensorRingEquiv
    {R : Type uR} [CommRing R] [IsLocalRing R]
    {N : ℕ} {y : R}
    {E : Type uE} [CommRing E]
    [Algebra
      (iteratedRadical R 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E] :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → R := fun _ ↦ y
    let B₀ := iteratedRadical R 1 n a
    let A := AdicCompletion (maximalIdeal R) R
    let Bhat := iteratedRadical A 1 n
      (fun i ↦ algebraMap R A (a i))
    letI : Algebra R E := oneRootFiniteEtaleBaseAlgebra
      (R := R) (N := N) (y := y) (E := E)
    letI : Algebra B₀ Bhat := iteratedRadicalCompletionAlgebra n a
    (Bhat ⊗[B₀] E) ≃+* (A ⊗[R] E) := by
  dsimp only
  let n : Fin 1 → ℕ := fun _ ↦ N
  let a : Fin 1 → R := fun _ ↦ y
  let B₀ := iteratedRadical R 1 n a
  let A := AdicCompletion (maximalIdeal R) R
  let Bhat := iteratedRadical A 1 n
    (fun i ↦ algebraMap R A (a i))
  letI : Algebra R E := oneRootFiniteEtaleBaseAlgebra
    (R := R) (N := N) (y := y) (E := E)
  letI : IsScalarTower R B₀ E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra B₀ Bhat := iteratedRadicalCompletionAlgebra n a
  let rBhatAlgebra : Algebra R Bhat :=
    ((algebraMap A Bhat).comp (algebraMap R A)).toAlgebra
  letI : Algebra R Bhat := rBhatAlgebra
  letI : IsScalarTower R A Bhat :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R B₀ Bhat := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap A Bhat (algebraMap R A x) =
      algebraMap B₀ Bhat (algebraMap R B₀ x)
    exact (iteratedRadicalCompletion_algebraMap_comp_apply n a x).symm
  let tensor := A ⊗[R] B₀
  letI : Algebra B₀ tensor := Algebra.TensorProduct.rightAlgebra
  let ePush : tensor ≃ₐ[B₀] Bhat :=
    iteratedRadicalCompletionRightAlgEquiv n a
  letI : Algebra.IsPushout R B₀ A Bhat := by
    apply Algebra.IsPushout.of_equiv ePush
    ext x
    change (iteratedRadicalCompletionBaseChangeAlgEquiv n a)
        (algebraMap A tensor x) = algebraMap A Bhat x
    exact (iteratedRadicalCompletionBaseChangeAlgEquiv n a).commutes x
  letI : Algebra.IsPushout R A B₀ Bhat :=
    Algebra.IsPushout.symm
      (inferInstance : Algebra.IsPushout R B₀ A Bhat)
  exact
    (Algebra.IsPushout.cancelBaseChangeAlg R A B₀ Bhat E).toRingEquiv

/-- The `B̂`-algebra structure on the literal completion tensor transported
through the canonical cancelled-pushout equivalence. -/
@[reducible]
noncomputable def maximalAdicCompletionOneRootTensorAlgebra
    {R : Type uR} [CommRing R] [IsLocalRing R]
    {N : ℕ} {y : R}
    {E : Type uE} [CommRing E]
    [Algebra
      (iteratedRadical R 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E] :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → R := fun _ ↦ y
    let A := AdicCompletion (maximalIdeal R) R
    let Bhat := iteratedRadical A 1 n
      (fun i ↦ algebraMap R A (a i))
    letI : Algebra R E := oneRootFiniteEtaleBaseAlgebra
      (R := R) (N := N) (y := y) (E := E)
    Algebra Bhat (A ⊗[R] E) := by
  dsimp only
  let n : Fin 1 → ℕ := fun _ ↦ N
  let a : Fin 1 → R := fun _ ↦ y
  let B₀ := iteratedRadical R 1 n a
  let A := AdicCompletion (maximalIdeal R) R
  let Bhat := iteratedRadical A 1 n
    (fun i ↦ algebraMap R A (a i))
  letI : Algebra R E := oneRootFiniteEtaleBaseAlgebra
    (R := R) (N := N) (y := y) (E := E)
  letI : Algebra B₀ Bhat := iteratedRadicalCompletionAlgebra n a
  let Ehat := Bhat ⊗[B₀] E
  letI : Algebra Bhat Ehat := Algebra.TensorProduct.leftAlgebra
  let e : Ehat ≃+* (A ⊗[R] E) :=
    maximalAdicCompletionOneRootTensorRingEquiv
  exact (e.toRingHom.comp (algebraMap Bhat Ehat)).toAlgebra

/-- The cancelled-pushout comparison as an equivalence over the completed
one-root radical. -/
noncomputable def maximalAdicCompletionOneRootTensorAlgEquiv
    {R : Type uR} [CommRing R] [IsLocalRing R]
    {N : ℕ} {y : R}
    {E : Type uE} [CommRing E]
    [Algebra
      (iteratedRadical R 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E] :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → R := fun _ ↦ y
    let B₀ := iteratedRadical R 1 n a
    let A := AdicCompletion (maximalIdeal R) R
    let Bhat := iteratedRadical A 1 n
      (fun i ↦ algebraMap R A (a i))
    letI : Algebra R E := oneRootFiniteEtaleBaseAlgebra
      (R := R) (N := N) (y := y) (E := E)
    letI : Algebra B₀ Bhat := iteratedRadicalCompletionAlgebra n a
    letI : Algebra Bhat (A ⊗[R] E) :=
      maximalAdicCompletionOneRootTensorAlgebra
        (R := R) (N := N) (y := y) (E := E)
    (Bhat ⊗[B₀] E) ≃ₐ[Bhat] (A ⊗[R] E) := by
  dsimp only
  let n : Fin 1 → ℕ := fun _ ↦ N
  let a : Fin 1 → R := fun _ ↦ y
  let B₀ := iteratedRadical R 1 n a
  let A := AdicCompletion (maximalIdeal R) R
  let Bhat := iteratedRadical A 1 n
    (fun i ↦ algebraMap R A (a i))
  letI : Algebra R E := oneRootFiniteEtaleBaseAlgebra
    (R := R) (N := N) (y := y) (E := E)
  letI : Algebra B₀ Bhat := iteratedRadicalCompletionAlgebra n a
  let Ehat := Bhat ⊗[B₀] E
  letI : Algebra Bhat Ehat := Algebra.TensorProduct.leftAlgebra
  letI : Algebra Bhat (A ⊗[R] E) :=
    maximalAdicCompletionOneRootTensorAlgebra
      (R := R) (N := N) (y := y) (E := E)
  let e : Ehat ≃+* (A ⊗[R] E) :=
    maximalAdicCompletionOneRootTensorRingEquiv
  exact AlgEquiv.ofRingEquiv (f := e) (fun _ ↦ rfl)

/-- A global finite-etale factor over a one-root cover yields, after
maximal-adic completion, a literal finite-etale chosen local factor.

All instances and prime comparisons in the conclusion are generated from
the supplied regular pair, the canonical completion pushout, and the chosen
global closed prime.  In particular, no equality with another chosen prime
and no domain property of `A ⊗[R] E` is a public assumption. -/
theorem exists_maximalAdicCompletion_oneRoot_finiteEtaleChosenFactor
    {R : Type uR} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {N : ℕ} (hN : 0 < N) {y z : R}
    (hreg : IsRegular R [y, z])
    (hgen : Ideal.ofList [y, z] = maximalIdeal R)
    {E : Type uE} [CommRing E]
    [Algebra
      (iteratedRadical R 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E]
    [Module.Finite
      (iteratedRadical R 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E]
    [Algebra.Etale
      (iteratedRadical R 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E]
    (p : Ideal E) [p.IsMaximal] :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → R := fun _ ↦ y
    let B₀ := iteratedRadical R 1 n a
    let A := AdicCompletion (maximalIdeal R) R
    let aHat : Fin 1 → A := fun i ↦ algebraMap R A (a i)
    let Bhat := iteratedRadical A 1 n aHat
    let hy : y ∈ maximalIdeal R := by
      rw [← hgen]
      exact Ideal.subset_span (by simp)
    let ha : ∀ i, a i ∈ maximalIdeal R := fun _ ↦ hy
    let haHat : ∀ i, aHat i ∈ maximalIdeal A := fun i ↦ by
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap R A) (ha i)
    letI : IsLocalRing B₀ := isLocalRing_iteratedRadical n a
      (fun _ ↦ hN) ha
    letI : IsLocalRing Bhat := isLocalRing_iteratedRadical n aHat
      (fun _ ↦ hN) haHat
    letI : Algebra R E := oneRootFiniteEtaleBaseAlgebra
      (R := R) (N := N) (y := y) (E := E)
    let T := A ⊗[R] E
    letI : Algebra E T := Algebra.TensorProduct.rightAlgebra
    letI : Algebra Bhat T :=
      maximalAdicCompletionOneRootTensorAlgebra
        (R := R) (N := N) (y := y) (E := E)
    let P := p.map (algebraMap E T)
    ∃ hPMax : P.IsMaximal,
      letI : P.IsPrime := hPMax.isPrime
      ∃ hPOver : P.LiesOver (maximalIdeal Bhat),
        letI : P.LiesOver (maximalIdeal Bhat) := hPOver
        let Dp := Localization.AtPrime P
        letI : Algebra Bhat Dp := inferInstance
        Module.Finite Bhat Dp ∧
          Algebra.Etale Bhat Dp ∧
          IsLocalHom (algebraMap Bhat Dp) ∧
          (∀ Q : Ideal Dp, Q.IsPrime →
            Q.LiesOver (maximalIdeal Bhat) →
            Q = maximalIdeal Dp) := by
  dsimp only
  let n : Fin 1 → ℕ := fun _ ↦ N
  let a : Fin 1 → R := fun _ ↦ y
  let B₀ := iteratedRadical R 1 n a
  let A := AdicCompletion (maximalIdeal R) R
  let aHat : Fin 1 → A := fun i ↦ algebraMap R A (a i)
  let Bhat := iteratedRadical A 1 n aHat
  have hy : y ∈ maximalIdeal R := by
    rw [← hgen]
    exact Ideal.subset_span (by simp)
  have ha : ∀ i, a i ∈ maximalIdeal R := fun _ ↦ hy
  have haHat : ∀ i, aHat i ∈ maximalIdeal A := fun i ↦ by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem (algebraMap R A) (ha i)
  let : IsLocalRing B₀ :=
    isLocalRing_iteratedRadical n a (fun _ ↦ hN) ha
  let : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical n aHat (fun _ ↦ hN) haHat
  let : Algebra R E := oneRootFiniteEtaleBaseAlgebra
    (R := R) (N := N) (y := y) (E := E)
  let : IsScalarTower R B₀ E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsIntegral B₀ E := Algebra.IsIntegral.of_finite B₀ E
  let : Module.Finite R B₀ :=
    finite_iteratedRadical n a (fun _ ↦ hN)
  let : Algebra.IsIntegral R B₀ := Algebra.IsIntegral.of_finite R B₀
  have hB₀UnderMaximal : ((maximalIdeal B₀).under R).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R B₀)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) (maximalIdeal B₀)
  let : (maximalIdeal B₀).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.eq_maximalIdeal hB₀UnderMaximal).symm⟩
  have hpUnderMaximal : (p.under B₀).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap B₀ E)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) p
  let : p.LiesOver (maximalIdeal B₀) :=
    ⟨(IsLocalRing.eq_maximalIdeal hpUnderMaximal).symm⟩
  let : p.LiesOver (maximalIdeal R) :=
    Ideal.LiesOver.trans p (maximalIdeal B₀) (maximalIdeal R)
  let T := A ⊗[R] E
  let : Algebra A T := Algebra.TensorProduct.leftAlgebra
  let : Algebra E T := Algebra.TensorProduct.rightAlgebra
  let P := p.map (algebraMap E T)
  have hPGeometry :=
    adicCompletion_tensorProduct_map_liesOver_maximalIdeal
      (R := R) (S := E) p
  have hPMax : P.IsMaximal := by
    simpa only [A, T, P] using hPGeometry.1
  let : P.IsMaximal := hPMax
  let : P.IsPrime := hPMax.isPrime
  let : Algebra B₀ Bhat := iteratedRadicalCompletionAlgebra n a
  let : Algebra Bhat T :=
    maximalAdicCompletionOneRootTensorAlgebra
      (R := R) (N := N) (y := y) (E := E)
  let Ehat := Bhat ⊗[B₀] E
  let : Algebra Bhat Ehat := Algebra.TensorProduct.leftAlgebra
  let eTensor : Ehat ≃ₐ[Bhat] T :=
    maximalAdicCompletionOneRootTensorAlgEquiv
  let : Module.Finite Bhat Ehat := inferInstance
  let : Algebra.Etale Bhat Ehat := inferInstance
  let : Module.Finite Bhat T :=
    Module.Finite.of_surjective eTensor.toLinearMap eTensor.surjective
  let : Algebra.Etale Bhat T := Algebra.Etale.of_equiv eTensor
  let : Algebra.IsIntegral Bhat T := Algebra.IsIntegral.of_finite Bhat T
  have hPUnderMaximal : (P.under Bhat).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap Bhat T)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) P
  have hPOver : P.LiesOver (maximalIdeal Bhat) :=
    ⟨(IsLocalRing.eq_maximalIdeal hPUnderMaximal).symm⟩
  let : P.LiesOver (maximalIdeal Bhat) := hPOver
  let : IsNoetherianRing A :=
    maximalAdicCompletion_isNoetherianRing_of_regularPair hreg hgen
  let : HenselianLocalRing Bhat :=
    henselianLocalRing_iteratedRadical_of_isAdicComplete
      n aHat (fun _ ↦ hN) haHat
  let Dp := Localization.AtPrime P
  let : Algebra T Dp := inferInstance
  let : Algebra Bhat Dp := inferInstance
  let : IsScalarTower Bhat T Dp := inferInstance
  let : Module.Finite Bhat Dp :=
    moduleFinite_localizationAtPrime_of_henselian_of_etale
      (R := Bhat) (S := T) P
  let : Algebra.Etale Bhat Dp :=
    etale_localizationAtPrime_of_henselian_of_etale
      (R := Bhat) (S := T) P
  let : IsLocalHom (algebraMap Bhat Dp) :=
    isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal
      (R := Bhat) (S := T) P
  have hunique : ∀ Q : Ideal Dp, Q.IsPrime →
      Q.LiesOver (maximalIdeal Bhat) → Q = maximalIdeal Dp := by
    intro Q hQPrime hQOver
    let : Q.IsPrime := hQPrime
    let : Q.LiesOver (maximalIdeal Bhat) := hQOver
    let : Algebra.IsIntegral Bhat Dp :=
      Algebra.IsIntegral.of_finite Bhat Dp
    have hQMaximal : Q.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Bhat) (S := Dp) Q <| by
          rw [← Q.over_def (maximalIdeal Bhat)]
          exact maximalIdeal.isMaximal Bhat
    exact IsLocalRing.eq_maximalIdeal hQMaximal
  refine ⟨hPMax, ?_⟩
  refine ⟨hPOver, ?_⟩
  exact ⟨inferInstance, inferInstance, inferInstance, hunique⟩

end EtaleFundamentalGroups.Kummer

end
