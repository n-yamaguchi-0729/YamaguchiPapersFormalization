/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalActualFactor
import Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.Basic
import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.Support

/-!
# The selected one-root cover inside a full radical cover

The full height-two radical cover contains the selected one-root cover by
base change along the preceding iterated radical extension.  This file makes
that map canonical, proves that it is finite faithfully flat, and identifies
the contraction of the selected height-one root prime.  The contraction is
the input needed to compare the fixed generic tensor component over the
simple selected-root DVR with the same component over the full cover.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- The canonical algebra structure from the selected one-root cover to the
full cover obtained after the preceding iterated radicals. -/
@[reducible]
noncomputable def fullRootCoverSelectedRootAlgebra
    {R : Type u} [CommRing R]
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → R)
    (N : ℕ) (y : R) :
    let B := iteratedRadical R d n a
    let g : R[X] := X ^ N - C y
    let S := AdjoinRoot g
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let D := AdjoinRoot F
    Algebra S D := by
  dsimp only
  let B := iteratedRadical R d n a
  let g : R[X] := X ^ N - C y
  let S := AdjoinRoot g
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  have hg : g.map (algebraMap R B) = F := by
    simp [g, F]
  let e : (B ⊗[R] S) ≃ₐ[B] D :=
    (adjoinRootBaseChangeAlgEquiv g).trans
      (AdjoinRoot.algEquivOfEq B _ _ hg)
  exact (e.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight : S →ₐ[R] B ⊗[R] S).toRingHom).toAlgebra

/-- The selected root maps to the selected root of the full cover. -/
@[simp]
theorem fullRootCoverSelectedRootAlgebra_map_root
    {R : Type u} [CommRing R]
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → R)
    (N : ℕ) (y : R) :
    let B := iteratedRadical R d n a
    let g : R[X] := X ^ N - C y
    let S := AdjoinRoot g
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let D := AdjoinRoot F
    letI : Algebra S D := fullRootCoverSelectedRootAlgebra n a N y
    algebraMap S D (AdjoinRoot.root g) = AdjoinRoot.root F := by
  dsimp only
  let B := iteratedRadical R d n a
  let g : R[X] := X ^ N - C y
  let S := AdjoinRoot g
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  have hg : g.map (algebraMap R B) = F := by
    simp [g, F]
  let : Algebra S D := fullRootCoverSelectedRootAlgebra n a N y
  change ((adjoinRootBaseChangeAlgEquiv g).trans
      (AdjoinRoot.algEquivOfEq B _ _ hg))
        ((1 : B) ⊗ₜ[R] AdjoinRoot.root g) = AdjoinRoot.root F
  rw [AlgEquiv.trans_apply, adjoinRootBaseChangeAlgEquiv_tmul_root,
    AdjoinRoot.algEquivOfEq_root]

/-- The full cover is finite over its selected one-root subcover. -/
theorem fullRootCoverSelectedRoot_moduleFinite
    {R : Type u} [CommRing R]
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → R)
    (hn : ∀ k, 0 < n k) (N : ℕ) (y : R) :
    let B := iteratedRadical R d n a
    let g : R[X] := X ^ N - C y
    let S := AdjoinRoot g
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let D := AdjoinRoot F
    letI : Algebra S D := fullRootCoverSelectedRootAlgebra n a N y
    Module.Finite S D := by
  dsimp only
  let B := iteratedRadical R d n a
  let g : R[X] := X ^ N - C y
  let S := AdjoinRoot g
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  have hg : g.map (algebraMap R B) = F := by
    simp [g, F]
  let : Module.Finite R B := finite_iteratedRadical n a hn
  let T := S ⊗[R] B
  let : Algebra S T := Algebra.TensorProduct.leftAlgebra
  let : Module.Finite S T := Module.Finite.base_change R S B
  let eBase : (B ⊗[R] S) ≃ₐ[B] D :=
    (adjoinRootBaseChangeAlgEquiv g).trans
      (AdjoinRoot.algEquivOfEq B _ _ hg)
  let eRing : T ≃+* D :=
    (Algebra.TensorProduct.comm R S B).toRingEquiv.trans eBase.toRingEquiv
  let : Algebra S D := fullRootCoverSelectedRootAlgebra n a N y
  let e : T ≃ₐ[S] D := AlgEquiv.ofRingEquiv (R := S) (f := eRing) (fun x ↦ by
    change eBase ((1 : B) ⊗ₜ[R] x) = algebraMap S D x
    rfl)
  exact Module.Finite.equiv e.toLinearEquiv

/-- The full cover is faithfully flat over its selected one-root subcover. -/
theorem fullRootCoverSelectedRoot_faithfullyFlat
    {R : Type u} [CommRing R] [Nontrivial R]
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → R)
    (hn : ∀ k, 0 < n k) (N : ℕ) (y : R) :
    let B := iteratedRadical R d n a
    let g : R[X] := X ^ N - C y
    let S := AdjoinRoot g
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let D := AdjoinRoot F
    letI : Algebra S D := fullRootCoverSelectedRootAlgebra n a N y
    Module.FaithfullyFlat S D := by
  dsimp only
  let B := iteratedRadical R d n a
  let g : R[X] := X ^ N - C y
  let S := AdjoinRoot g
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  have hg : g.map (algebraMap R B) = F := by
    simp [g, F]
  let : Module.FaithfullyFlat R B :=
    faithfullyFlat_iteratedRadical n a hn
  let T := S ⊗[R] B
  let : Algebra S T := Algebra.TensorProduct.leftAlgebra
  let : Module.FaithfullyFlat S T := inferInstance
  let eBase : (B ⊗[R] S) ≃ₐ[B] D :=
    (adjoinRootBaseChangeAlgEquiv g).trans
      (AdjoinRoot.algEquivOfEq B _ _ hg)
  let eRing : T ≃+* D :=
    (Algebra.TensorProduct.comm R S B).toRingEquiv.trans eBase.toRingEquiv
  let : Algebra S D := fullRootCoverSelectedRootAlgebra n a N y
  let e : T ≃ₐ[S] D := AlgEquiv.ofRingEquiv (R := S) (f := eRing) (fun x ↦ by
    change eBase ((1 : B) ⊗ₜ[R] x) = algebraMap S D x
    rfl)
  exact Module.FaithfullyFlat.of_linearEquiv S T e.symm.toLinearEquiv

/-- A selected height-one root prime of the full cover contracts to the
selected root prime of the simple one-root cover. -/
theorem fullRootCoverSelectedRoot_under_eq_span_root
    {R : Type u} [CommRing R] [IsDomain R]
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → R)
    (hn : ∀ k, 0 < n k) (N : ℕ) (y : R) :
    let B := iteratedRadical R d n a
    let g : R[X] := X ^ N - C y
    let S := AdjoinRoot g
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let D := AdjoinRoot F
    letI : Algebra S D := fullRootCoverSelectedRootAlgebra n a N y
    ∀ [IsDomain S] [IsIntegrallyClosed S] [IsDomain D]
      (_hroot : Prime (AdjoinRoot.root g))
      (q : Ideal D) [q.IsPrime], q.height = 1 →
      q = Ideal.span ({AdjoinRoot.root F} : Set D) →
      q.under S = Ideal.span ({AdjoinRoot.root g} : Set S) := by
  dsimp only
  intro _ _ _ hroot q _ hqHeight hq
  let B := iteratedRadical R d n a
  let g : R[X] := X ^ N - C y
  let S := AdjoinRoot g
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  let : Algebra S D := fullRootCoverSelectedRootAlgebra n a N y
  let : Module.Finite S D :=
    fullRootCoverSelectedRoot_moduleFinite n a hn N y
  let : Algebra.IsIntegral S D := Algebra.IsIntegral.of_finite S D
  let : Module.FaithfullyFlat S D :=
    fullRootCoverSelectedRoot_faithfullyFlat n a hn N y
  let : FaithfulSMul S D := Module.FaithfullyFlat.faithfulSMul
  have hUnderHeight : (q.under S).height = 1 := by
    rw [← SpecialLocalPurity.height_eq_height_under_of_faithfully_integral_over_integrallyClosed q]
    exact hqHeight
  have hrootMem : AdjoinRoot.root g ∈ q.under S := by
    change algebraMap S D (AdjoinRoot.root g) ∈ q
    rw [fullRootCoverSelectedRootAlgebra_map_root]
    rw [hq]
    exact Ideal.mem_span_singleton_self _
  exact (q.under S).eq_span_singleton_of_height_eq_one
    hUnderHeight hrootMem hroot

end EtaleFundamentalGroups.Kummer

end
