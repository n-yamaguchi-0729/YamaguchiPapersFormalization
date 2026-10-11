/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Full.ActualRootFirst

/-!
# Finite faithful structure from an actual root to the full cover

The actual-root-first presentation identifies a full conditional root cover
with one further monic root extension of the simple actual-root cover.  This
file transports finiteness and faithful flatness through that equivalence.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- The full cover is finite over the simple actual-root cover in the
actual-root-first presentation. -/
theorem fullRootCoverActualRootFirst_moduleFinite
    {R : Type u} [CommRing R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (N : ℕ) (hN : 0 < N) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let D := AdjoinRoot F
    let px : R[X] := X ^ n k - C (a k)
    let Xroot := AdjoinRoot px
    letI : Algebra Xroot D :=
      fullRootCoverActualRootFirstAlgebra n a k hother N y
    Module.Finite Xroot D := by
  dsimp only
  let B := iteratedRadical R (s + 1) n a
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  let px : R[X] := X ^ n k - C (a k)
  let Xroot := AdjoinRoot px
  let fy : Xroot[X] := X ^ N - C (algebraMap R Xroot y)
  let Dxy := AdjoinRoot fy
  let : Algebra Xroot D :=
    fullRootCoverActualRootFirstAlgebra n a k hother N y
  let : Module.Finite Xroot Dxy := by
    simpa only [Dxy, fy] using
      (Polynomial.monic_X_pow_sub_C
        (algebraMap R Xroot y) hN.ne').finite_adjoinRoot
  let eRing : D ≃ₐ[R] Dxy :=
    fullRootCoverActualRootFirstAlgEquiv n a k hother N y
  let e : D ≃ₐ[Xroot] Dxy :=
    AlgEquiv.ofRingEquiv (f := eRing.toRingEquiv) (fun x ↦ by
      change eRing (eRing.symm (algebraMap Xroot Dxy x)) =
        algebraMap Xroot Dxy x
      exact eRing.apply_symm_apply _)
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- The full cover is faithfully flat over the simple actual-root cover in
the actual-root-first presentation. -/
theorem fullRootCoverActualRootFirst_faithfullyFlat
    {R : Type u} [CommRing R] [Nontrivial R]
    {s : ℕ} (n : Fin (s + 1) → ℕ) (a : Fin (s + 1) → R)
    (k : Fin (s + 1)) (hother : ∀ l, l ≠ k → n l = 1)
    (hnk : 0 < n k) (N : ℕ) (hN : 0 < N) (y : R) :
    let B := iteratedRadical R (s + 1) n a
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let D := AdjoinRoot F
    let px : R[X] := X ^ n k - C (a k)
    let Xroot := AdjoinRoot px
    letI : Algebra Xroot D :=
      fullRootCoverActualRootFirstAlgebra n a k hother N y
    Module.FaithfullyFlat Xroot D := by
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
  let eRing : D ≃ₐ[R] Dxy :=
    fullRootCoverActualRootFirstAlgEquiv n a k hother N y
  let e : D ≃ₐ[Xroot] Dxy :=
    AlgEquiv.ofRingEquiv (f := eRing.toRingEquiv) (fun x ↦ by
      change eRing (eRing.symm (algebraMap Xroot Dxy x)) =
        algebraMap Xroot Dxy x
      exact eRing.apply_symm_apply _)
  exact Module.FaithfullyFlat.of_linearEquiv
    Xroot Dxy e.toLinearEquiv

end EtaleFundamentalGroups.Kummer

end
