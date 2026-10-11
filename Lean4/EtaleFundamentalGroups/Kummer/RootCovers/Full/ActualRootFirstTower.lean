/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.RootCovers.Full.ActualRootFirst

/-!
# The base tower of the actual-root-first full cover

The actual-root-first algebra is defined by transporting the two-root cover
through an `R`-algebra equivalence.  This leaf records the resulting scalar
tower once, so downstream branch theorems do not repeatedly elaborate that
coordinate calculation inside a large dependent telescope.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- The canonical map from the simple actual-root cover to the original full
cover commutes with the map from the height-two base. -/
theorem fullRootCoverActualRootFirst_isScalarTower
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (N : ℕ) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let D := AdjoinRoot F
    let gx : R[X] := X ^ n k - C (a k)
    let Xroot := AdjoinRoot gx
    letI : Algebra Xroot D :=
      fullRootCoverActualRootFirstAlgebra n a k hother N y
    IsScalarTower R Xroot D := by
  dsimp only
  let B := iteratedRadical R (s + 1) n a
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  let gx : R[X] := X ^ n k - C (a k)
  let Xroot := AdjoinRoot gx
  let fy : Xroot[X] := X ^ N - C (algebraMap R Xroot y)
  let Dxy := AdjoinRoot fy
  let : Algebra Xroot D :=
    fullRootCoverActualRootFirstAlgebra n a k hother N y
  let eD : D ≃ₐ[R] Dxy :=
    fullRootCoverActualRootFirstAlgEquiv n a k hother N y
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap R D x =
    eD.symm (algebraMap Xroot Dxy (algebraMap R Xroot x))
  rw [← IsScalarTower.algebraMap_apply R Xroot Dxy]
  rw [← eD.commutes]
  exact (eD.symm_apply_apply _).symm

end EtaleFundamentalGroups.Kummer

end
