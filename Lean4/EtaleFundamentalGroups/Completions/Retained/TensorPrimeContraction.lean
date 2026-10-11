/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Completions.Retained.PrimeChain

/-!
# Contracting a retained completed prime chain through a finite-model tower

Suppose two finite models over the same local base are connected by an
algebra map.  After a common base change, the canonical tensor map contracts
any prime chain in the upper model to a prime chain in the lower model.

The point of this small leaf is coordinate retention: contractions to the
old finite models and to the new base are proved for the literal tensor map.
No generic component, independently selected prime, or comparison
equivalence occurs in the statement.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uR' uS₀ uS₁

/-- The right-coordinate algebra used to formulate literal contractions to
the upper and lower finite models. -/
noncomputable local instance completedFiniteModelTensorRightAlgebra
    {R : Type uR} {R' : Type uR'} {S : Type uS₀}
    [CommRing R] [CommRing R'] [CommRing S]
    [Algebra R R'] [Algebra R S] :
    Algebra S (R' ⊗[R] S) :=
  Algebra.TensorProduct.rightAlgebra

/-- The canonical map between two base-changed finite models. -/
noncomputable def completedFiniteModelTowerAlgHom
    {R : Type uR} {R' : Type uR'}
    {S₀ : Type uS₀} {S₁ : Type uS₁}
    [CommRing R] [CommRing R'] [CommRing S₀] [CommRing S₁]
    [Algebra R R'] [Algebra R S₀] [Algebra R S₁]
    (g : S₀ →ₐ[R] S₁) :
    (R' ⊗[R] S₀) →ₐ[R'] (R' ⊗[R] S₁) :=
  Algebra.TensorProduct.map (AlgHom.id R' R')
    g

@[simp]
theorem completedFiniteModelTowerAlgHom_tmul
    {R : Type uR} {R' : Type uR'}
    {S₀ : Type uS₀} {S₁ : Type uS₁}
    [CommRing R] [CommRing R'] [CommRing S₀] [CommRing S₁]
    [Algebra R R'] [Algebra R S₀] [Algebra R S₁]
    (g : S₀ →ₐ[R] S₁) (x : R') (s : S₀) :
    completedFiniteModelTowerAlgHom
        (R := R) (R' := R') (S₀ := S₀) (S₁ := S₁)
        g
        (x ⊗ₜ[R] s) =
      x ⊗ₜ[R] g s := by
  simp [completedFiniteModelTowerAlgHom]

/-- A retained generic/height-one chain in the upper completed model
contracts to the same literal chain in the lower completed model.

In particular, the lower completed prime lies over the specified lower
finite-model prime `q₀`, not merely over an unspecified contraction. -/
theorem completedFiniteModelTower_contract_primeChain
    {R : Type uR} {R' : Type uR'}
    {S₀ : Type uS₀} {S₁ : Type uS₁}
    [CommRing R] [CommRing R'] [CommRing S₀] [CommRing S₁]
    [Algebra R R'] [Algebra R S₀] [Algebra R S₁]
    (g : S₀ →ₐ[R] S₁)
    (q₀ : Ideal S₀) (q₁ : Ideal S₁)
    [q₀.IsPrime] [q₁.IsPrime]
    (hq₁q₀ : q₁.comap g.toRingHom = q₀)
    (N Q : Ideal (R' ⊗[R] S₁))
    [hNPrime : N.IsPrime] [N.LiesOver (⊥ : Ideal R')]
    [hQPrime : Q.IsPrime] [Q.LiesOver q₁]
    (hNQ : N ≤ Q) :
    let f := completedFiniteModelTowerAlgHom
      (R := R) (R' := R') (S₀ := S₀) (S₁ := S₁) g
    let N₀ := N.comap f.toRingHom
    let Q₀ := Q.comap f.toRingHom
    N₀ ≤ Q₀ ∧ N₀.IsPrime ∧ N₀.LiesOver (⊥ : Ideal R') ∧
      Q₀.IsPrime ∧ Q₀.LiesOver q₀ := by
  classical
  dsimp only
  let f := completedFiniteModelTowerAlgHom
    (R := R) (R' := R') (S₀ := S₀) (S₁ := S₁) g
  let N₀ := N.comap f.toRingHom
  let Q₀ := Q.comap f.toRingHom
  have hN₀Q₀ : N₀ ≤ Q₀ := Ideal.comap_mono hNQ
  have hN₀Prime : N₀.IsPrime :=
    hNPrime.comap f.toRingHom
  have hQ₀Prime : Q₀.IsPrime :=
    hQPrime.comap f.toRingHom
  let : N₀.IsPrime := hN₀Prime
  let : Q₀.IsPrime := hQ₀Prime
  have hN₀Over : N₀.LiesOver (⊥ : Ideal R') := by
    refine ⟨?_⟩
    ext x
    change x ∈ (⊥ : Ideal R') ↔
      f (algebraMap R' (R' ⊗[R] S₀) x) ∈ N
    have hleft :
        f (algebraMap R' (R' ⊗[R] S₀) x) =
          algebraMap R' (R' ⊗[R] S₁) x := by
      exact f.commutes x
    rw [hleft]
    exact N.mem_of_liesOver (⊥ : Ideal R') x
  have hQ₀Over : Q₀.LiesOver q₀ := by
    refine ⟨?_⟩
    ext s
    change s ∈ q₀ ↔ f (algebraMap S₀ (R' ⊗[R] S₀) s) ∈ Q
    have hright :
        f (algebraMap S₀ (R' ⊗[R] S₀) s) =
          algebraMap S₁ (R' ⊗[R] S₁) (g s) := by
      change f ((1 : R') ⊗ₜ[R] s) =
        (1 : R') ⊗ₜ[R] g s
      simp [f, completedFiniteModelTowerAlgHom]
    rw [hright]
    rw [← hq₁q₀]
    exact Q.mem_of_liesOver q₁ (g s)
  exact ⟨hN₀Q₀, hN₀Prime, hN₀Over, hQ₀Prime, hQ₀Over⟩

end EtaleFundamentalGroups

end
