/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.GaloisFullRootCoverActualRoot

/-!
# A full root cover presented with an actual branch root first

When a height-one prime lies on a non-selected actual branch, the existing
reordering presents that branch root last.  Swapping the final two independent
roots instead presents the same full cover as a finite free extension of the
simple actual-root cover.  This file records that equivalence, its two root
coordinates, and the exact contraction of the actual root prime.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- The full cover with its specified actual root adjoined first and the
selected root adjoined afterwards. -/
def fullRootCoverActualRootFirstAlgEquiv
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (N : ℕ) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let px : R[X] := X ^ n k - C (a k)
    let Xroot := AdjoinRoot px
    let fy : Xroot[X] := X ^ N - C (algebraMap R Xroot y)
    AdjoinRoot F ≃ₐ[R] AdjoinRoot fy :=
  (fullRootCoverActualRootLastAlgEquiv n a k hother N y).trans
    (twoRootSwapAlgEquiv (n k) N (a k) y).symm

/-- In the actual-root-first presentation, the specified conditional root
is the root already lying in the coefficient algebra. -/
@[simp]
theorem fullRootCoverActualRootFirstAlgEquiv_algebraMap_actualRoot
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (N : ℕ) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let px : R[X] := X ^ n k - C (a k)
    let Xroot := AdjoinRoot px
    let fy : Xroot[X] := X ^ N - C (algebraMap R Xroot y)
    fullRootCoverActualRootFirstAlgEquiv n a k hother N y
        (algebraMap B (AdjoinRoot F)
          (iteratedRadicalRoot R n a k)) =
      algebraMap Xroot (AdjoinRoot fy) (AdjoinRoot.root px) := by
  dsimp only
  let eSwap := twoRootSwapAlgEquiv (n k) N (a k) y
  change eSwap.symm
      (fullRootCoverActualRootLastAlgEquiv n a k hother N y
        (algebraMap (iteratedRadical R (s + 1) n a)
          (AdjoinRoot
            (X ^ N - C (algebraMap R
              (iteratedRadical R (s + 1) n a) y)))
          (iteratedRadicalRoot R n a k))) = _
  rw [fullRootCoverActualRootLastAlgEquiv_algebraMap_root]
  rw [← twoRootSwapAlgEquiv_algebraMap_root]
  exact eSwap.symm_apply_apply _

/-- In the actual-root-first presentation, the selected root is the final
adjoined root. -/
@[simp]
theorem fullRootCoverActualRootFirstAlgEquiv_selectedRoot
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (N : ℕ) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let px : R[X] := X ^ n k - C (a k)
    let Xroot := AdjoinRoot px
    let fy : Xroot[X] := X ^ N - C (algebraMap R Xroot y)
    fullRootCoverActualRootFirstAlgEquiv n a k hother N y
        (AdjoinRoot.root F) = AdjoinRoot.root fy := by
  dsimp only
  let eSwap := twoRootSwapAlgEquiv (n k) N (a k) y
  change eSwap.symm
      (fullRootCoverActualRootLastAlgEquiv n a k hother N y
        (AdjoinRoot.root
          (X ^ N - C (algebraMap R
            (iteratedRadical R (s + 1) n a) y)))) = _
  rw [fullRootCoverActualRootLastAlgEquiv_root]
  rw [← twoRootSwapAlgEquiv_root]
  exact eSwap.symm_apply_apply _

/-- The actual-root-first equivalence defines the canonical algebra structure
from the simple actual-root cover to the original full cover. -/
@[reducible]
noncomputable def fullRootCoverActualRootFirstAlgebra
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (N : ℕ) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let px : R[X] := X ^ n k - C (a k)
    let Xroot := AdjoinRoot px
    Algebra Xroot (AdjoinRoot F) := by
  dsimp only
  let B := iteratedRadical R (s + 1) n a
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let px : R[X] := X ^ n k - C (a k)
  let Xroot := AdjoinRoot px
  let fy : Xroot[X] := X ^ N - C (algebraMap R Xroot y)
  let e := fullRootCoverActualRootFirstAlgEquiv n a k hother N y
  exact (e.symm.toRingHom.comp (algebraMap Xroot (AdjoinRoot fy))).toAlgebra

/-- The canonical simple-actual-root algebra sends its root to the original
conditional root. -/
@[simp]
theorem fullRootCoverActualRootFirstAlgebra_map_root
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (N : ℕ) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let px : R[X] := X ^ n k - C (a k)
    let Xroot := AdjoinRoot px
    letI : Algebra Xroot (AdjoinRoot F) :=
      fullRootCoverActualRootFirstAlgebra n a k hother N y
    algebraMap Xroot (AdjoinRoot F) (AdjoinRoot.root px) =
      algebraMap B (AdjoinRoot F) (iteratedRadicalRoot R n a k) := by
  dsimp only
  let B := iteratedRadical R (s + 1) n a
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let px : R[X] := X ^ n k - C (a k)
  let Xroot := AdjoinRoot px
  let fy : Xroot[X] := X ^ N - C (algebraMap R Xroot y)
  let e := fullRootCoverActualRootFirstAlgEquiv n a k hother N y
  let : Algebra Xroot (AdjoinRoot F) :=
    fullRootCoverActualRootFirstAlgebra n a k hother N y
  apply e.injective
  change e (e.symm (algebraMap Xroot (AdjoinRoot fy)
      (AdjoinRoot.root px))) =
    e (algebraMap B (AdjoinRoot F) (iteratedRadicalRoot R n a k))
  rw [e.apply_symm_apply,
    fullRootCoverActualRootFirstAlgEquiv_algebraMap_actualRoot]

/-- The actual-root prime in the original full cover contracts exactly to
the root prime of the simple actual-root cover. -/
theorem fullRootCoverActualRootFirst_under_eq_span_root
    {R : Type u} [CommRing R] [IsDomain R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (hnk : 0 < n k) (N : ℕ) (hN : 0 < N) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let D := AdjoinRoot F
    let px : R[X] := X ^ n k - C (a k)
    let Xroot := AdjoinRoot px
    let qx := Ideal.span ({AdjoinRoot.root px} : Set Xroot)
    let qD := Ideal.span
      ({algebraMap B D (iteratedRadicalRoot R n a k)} : Set D)
    letI : Algebra Xroot D :=
      fullRootCoverActualRootFirstAlgebra n a k hother N y
    qD.under Xroot = qx := by
  dsimp only
  let B := iteratedRadical R (s + 1) n a
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  let px : R[X] := X ^ n k - C (a k)
  let Xroot := AdjoinRoot px
  let fy : Xroot[X] := X ^ N - C (algebraMap R Xroot y)
  let Dxy := AdjoinRoot fy
  let : Module.FaithfullyFlat R Xroot :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hnk (a k)
  let : FaithfulSMul R Xroot :=
    Module.FaithfullyFlat.faithfulSMul
  let : Nontrivial Xroot :=
    (FaithfulSMul.algebraMap_injective R Xroot).nontrivial
  let : Algebra Xroot D :=
    fullRootCoverActualRootFirstAlgebra n a k hother N y
  let : Module.FaithfullyFlat Xroot Dxy :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hN (algebraMap R Xroot y)
  let eRing := fullRootCoverActualRootFirstAlgEquiv n a k hother N y
  let e : D ≃ₐ[Xroot] Dxy :=
    AlgEquiv.ofRingEquiv (f := eRing.toRingEquiv) (fun x ↦ by
      change eRing (eRing.symm (algebraMap Xroot Dxy x)) =
        algebraMap Xroot Dxy x
      exact eRing.apply_symm_apply _)
  let : Module.FaithfullyFlat Xroot D :=
    Module.FaithfullyFlat.of_linearEquiv Xroot Dxy e.toLinearEquiv
  let qx := Ideal.span ({AdjoinRoot.root px} : Set Xroot)
  have hmap : qx.map (algebraMap Xroot D) =
      Ideal.span
        ({algebraMap B D (iteratedRadicalRoot R n a k)} : Set D) := by
    simp only [qx, Ideal.map_span, Set.image_singleton]
    rw [fullRootCoverActualRootFirstAlgebra_map_root]
  rw [← hmap]
  exact Ideal.comap_map_eq_self_of_faithfullyFlat (B := D) qx

end EtaleFundamentalGroups.Kummer

end
