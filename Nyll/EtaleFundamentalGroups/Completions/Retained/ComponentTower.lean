/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Nyll.EtaleFundamentalGroups.Completions.Retained.TensorPrimeContraction

/-!
# The retained generic component through a finite-model tower

A generic prime in an upper completed finite model contracts to a generic
prime in every lower finite model.  Localizing both models at the generic
point and then taking their literal field-tensor coordinates gives a
canonical embedding of the lower retained component into the upper one.

The construction below passes first through the two finite-model generic
fibres.  Thus it does not need a separately supplied map between their
chosen fraction fields, nor an equality between independently chosen tensor
components.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uR' uS₀ uS₁ uK uK' uL₀ uL₁

/-- The component selected in a lower completed finite model embeds into
the component selected by the same generic prime in an upper model.

Both literal tensor ideals are produced from `N` and its contraction.  The
map is obtained from the canonical map of localized finite models and is
therefore injective by construction. -/
theorem exists_retainedCompletedComponentTowerAlgHom
    {R : Type uR} {R' : Type uR'}
    {S₀ : Type uS₀} {S₁ : Type uS₁}
    {K : Type uK} {K' : Type uK'}
    {L₀ : Type uL₀} {L₁ : Type uL₁}
    [CommRing R] [IsDomain R]
    [CommRing R'] [IsDomain R'] [Algebra R R']
    [CommRing S₀] [IsDomain S₀] [Algebra R S₀] [Module.Finite R S₀]
    [CommRing S₁] [IsDomain S₁] [Algebra R S₁] [Module.Finite R S₁]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Field L₀] [Algebra S₀ L₀] [IsFractionRing S₀ L₀]
    [Algebra R L₀] [IsScalarTower R S₀ L₀]
    [Algebra K L₀] [IsScalarTower R K L₀]
    [Field L₁] [Algebra S₁ L₁] [IsFractionRing S₁ L₁]
    [Algebra R L₁] [IsScalarTower R S₁ L₁]
    [Algebra K L₁] [IsScalarTower R K L₁]
    [Algebra R K'] [IsScalarTower R R' K']
    [Algebra K K'] [IsScalarTower R K K']
    (g : S₀ →ₐ[R] S₁)
    (N : Ideal (R' ⊗[R] S₁))
    [hNPrime : N.IsPrime] [N.LiesOver (⊥ : Ideal R')] :
    let fT := completedFiniteModelTowerAlgHom
      (R := R) (R' := R') (S₀ := S₀) (S₁ := S₁) g
    let N₀ := N.comap fT.toRingHom
    letI : N₀.IsPrime := hNPrime.comap fT.toRingHom
    let hN₀Over : N₀.LiesOver (⊥ : Ideal R') := by
      refine ⟨?_⟩
      ext x
      change x ∈ (⊥ : Ideal R') ↔
        fT (algebraMap R' (R' ⊗[R] S₀) x) ∈ N
      have hleft :
          fT (algebraMap R' (R' ⊗[R] S₀) x) =
            algebraMap R' (R' ⊗[R] S₁) x := by
        exact fT.commutes x
      rw [hleft]
      exact N.mem_of_liesOver (⊥ : Ideal R') x
    letI : N₀.LiesOver (⊥ : Ideal R') := hN₀Over
    let m₀ := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S₀) (K := K) (L := L₀)
      (K' := K') N₀
    letI : m₀.IsMaximal :=
      retainedCompletedGenericTensorIdeal_isMaximal
        (R := R) (R' := R') (S := S₀) (K := K) (L := L₀)
        (K' := K') N₀
    let m₁ := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S₁) (K := K) (L := L₁)
      (K' := K') N
    letI : m₁.IsMaximal :=
      retainedCompletedGenericTensorIdeal_isMaximal
        (R := R) (R' := R') (S := S₁) (K := K) (L := L₁)
        (K' := K') N
    ∃ f : GenericTensorFieldComponent m₀ →ₐ[K']
        GenericTensorFieldComponent m₁,
      Function.Injective f := by
  classical
  dsimp only
  let T₀ := R' ⊗[R] S₀
  let T₁ := R' ⊗[R] S₁
  let fT := completedFiniteModelTowerAlgHom
    (R := R) (R' := R') (S₀ := S₀) (S₁ := S₁) g
  let N₀ := N.comap fT.toRingHom
  let : N₀.IsPrime := hNPrime.comap fT.toRingHom
  have hN₀Over : N₀.LiesOver (⊥ : Ideal R') := by
    refine ⟨?_⟩
    ext x
    change x ∈ (⊥ : Ideal R') ↔ fT (algebraMap R' T₀ x) ∈ N
    have hleft :
        fT (algebraMap R' T₀ x) = algebraMap R' T₁ x := by
      exact fT.commutes x
    rw [hleft]
    exact N.mem_of_liesOver (⊥ : Ideal R') x
  let : N₀.LiesOver (⊥ : Ideal R') := hN₀Over
  let G₀ := retainedCompletedFiniteBaseChangeGenericFiber
    (R := R) (R' := R') (S := S₀) (K' := K')
  let G₁ := retainedCompletedFiniteBaseChangeGenericFiber
    (R := R) (R' := R') (S := S₁) (K' := K')
  let : Algebra T₀ G₀ := Algebra.TensorProduct.rightAlgebra
  let : Algebra T₁ G₁ := Algebra.TensorProduct.rightAlgebra
  let fG : G₀ →ₐ[K'] G₁ :=
    Algebra.TensorProduct.map (AlgHom.id K' K') fT
  let n₀ := retainedCompletedGenericIdeal
    (R := R) (R' := R') (S := S₀) (K' := K') N₀
  let n₁ := retainedCompletedGenericIdeal
    (R := R) (R' := R') (S := S₁) (K' := K') N
  let hn₀Max : n₀.IsMaximal :=
    retainedCompletedGenericIdeal_isMaximal
      (R := R) (R' := R') (S := S₀) (K' := K') N₀
  let hn₁Max : n₁.IsMaximal :=
    retainedCompletedGenericIdeal_isMaximal
      (R := R) (R' := R') (S := S₁) (K' := K') N
  have hnle : n₀ ≤ n₁.comap fG.toRingHom := by
    change N₀.map (algebraMap T₀ G₀) ≤ n₁.comap fG.toRingHom
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change fG (algebraMap T₀ G₀ x) ∈ n₁
    have hxN : fT x ∈ N := hx
    have hxMap : algebraMap T₁ G₁ (fT x) ∈ n₁ :=
      Ideal.mem_map_of_mem (algebraMap T₁ G₁) hxN
    have hsquare :
        fG (algebraMap T₀ G₀ x) = algebraMap T₁ G₁ (fT x) := by
      change fG ((1 : K') ⊗ₜ[R'] x) =
        (1 : K') ⊗ₜ[R'] fT x
      exact Algebra.TensorProduct.map_tmul
        (AlgHom.id K' K') fT (1 : K') x
    rwa [hsquare]
  have hncomap : n₁.comap fG.toRingHom = n₀ := by
    have h := hn₀Max.eq_of_le
      (hn₁Max.isPrime.comap fG.toRingHom).ne_top
      hnle
    exact h.symm
  let qG : (G₀ ⧸ n₀) →ₐ[K'] (G₁ ⧸ n₁) :=
    Ideal.quotientMapₐ n₁ fG hnle
  have hqG : Function.Injective qG := by
    exact Ideal.quotientMap_injective' (H := hnle)
      (show n₁.comap fG.toRingHom ≤ n₀ by rw [hncomap])
  let e₀ := retainedCompletedGenericFiberEquiv
    (R := R) (R' := R') (S := S₀) (K := K) (L := L₀)
    (K' := K')
  let e₁ := retainedCompletedGenericFiberEquiv
    (R := R) (R' := R') (S := S₁) (K := K) (L := L₁)
    (K' := K')
  let m₀ := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S₀) (K := K) (L := L₀)
    (K' := K') N₀
  let m₁ := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S₁) (K := K) (L := L₁)
    (K' := K') N
  let : m₀.IsMaximal :=
    retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S₀) (K := K) (L := L₀)
      (K' := K') N₀
  let : m₁.IsMaximal :=
    retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S₁) (K := K) (L := L₁)
      (K' := K') N
  let eComp₀ : (G₀ ⧸ n₀) ≃ₐ[K'] GenericTensorFieldComponent m₀ :=
    Ideal.quotientEquivAlg n₀ m₀ e₀ rfl
  let eComp₁ : (G₁ ⧸ n₁) ≃ₐ[K'] GenericTensorFieldComponent m₁ :=
    Ideal.quotientEquivAlg n₁ m₁ e₁ rfl
  let f : GenericTensorFieldComponent m₀ →ₐ[K']
      GenericTensorFieldComponent m₁ :=
    eComp₁.toAlgHom.comp (qG.comp eComp₀.symm.toAlgHom)
  refine ⟨f, ?_⟩
  exact eComp₁.injective.comp (hqG.comp eComp₀.symm.injective)

end EtaleFundamentalGroups

end
