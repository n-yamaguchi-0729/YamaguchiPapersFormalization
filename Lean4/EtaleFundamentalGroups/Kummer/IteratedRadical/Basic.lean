/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import EtaleFundamentalGroups.Kummer.Radicals.Relative
import EtaleFundamentalGroups.Kummer.Descent.RelativeRadical

/-!
# Finite iterated Kummer radicals

This file adjoins finitely many roots of equations `X ^ n i - a i`, in the
order indexed by `Fin r`.  Every radicand comes from the original base ring;
this is the diagonal presentation used after decomposing a finite abelian
Kummer group into cyclic factors.

The intermediate rings are bundled only in the existing `CommAlgCat A`.
Their algebra structures and all scalar towers are the canonical structures
provided by `CommAlgCat` and `AdjoinRoot`.  No recursive instances are
installed globally.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/--
The algebra obtained by successively adjoining roots of
`X ^ n i - algebraMap A _ (a i)`.
-/
def iteratedRadical (A : Type u) [CommRing A] :
    (r : ℕ) → (Fin r → ℕ) → (Fin r → A) → CommAlgCat.{u} A
  | 0, _, _ => CommAlgCat.of A A
  | r + 1, n, a =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      CommAlgCat.of A
        (AdjoinRoot
          (X ^ n (Fin.last r) -
            C (algebraMap A T (a (Fin.last r)))))

/-- A finite positive iterated radical is finite over its original base.
The finite-module structures are installed only along the induction, so
consumers do not ask typeclass search to unfold the recursive presentation. -/
theorem finite_iteratedRadical
    {A : Type u} [CommRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i) :
    Module.Finite A (iteratedRadical A r n a) := by
  induction r with
  | zero =>
      change Module.Finite A A
      infer_instance
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      let : Module.Finite A T :=
        ih (Fin.init n) (Fin.init a) (fun i ↦ hn i.castSucc)
      let : Module.Finite T (AdjoinRoot f) :=
        (Polynomial.monic_X_pow_sub_C
          (algebraMap A T (a (Fin.last r)))
          (hn (Fin.last r)).ne').finite_adjoinRoot
      change Module.Finite A (AdjoinRoot f)
      exact Module.Finite.trans T (AdjoinRoot f)

/-- A positive iterated radical is free over its original base.

The proof composes the canonical monic `AdjoinRoot` bases one stage at a
time.  Keeping this as a named producer prevents completion consumers from
asking typeclass search to unfold the recursive ring presentation. -/
theorem free_iteratedRadical
    {A : Type u} [CommRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i) :
    Module.Free A (iteratedRadical A r n a) := by
  induction r with
  | zero =>
      change Module.Free A A
      infer_instance
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      let : Module.Free A T :=
        ih (Fin.init n) (Fin.init a) (fun i ↦ hn i.castSucc)
      let : Module.Free T (AdjoinRoot f) :=
        (Polynomial.monic_X_pow_sub_C
          (algebraMap A T (a (Fin.last r)))
          (hn (Fin.last r)).ne').free_adjoinRoot
      change Module.Free A (AdjoinRoot f)
      exact Module.Free.trans (R := A) (S := T) (M := AdjoinRoot f)

/--
A positive-degree finite iterated radical is faithfully flat over its
original base.  At each step, monicity gives a free extension; faithful
flatness is then composed through the canonical scalar tower.
-/
theorem faithfullyFlat_iteratedRadical
    {A : Type u} [CommRing A] [Nontrivial A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i) :
    Module.FaithfullyFlat A (iteratedRadical A r n a) := by
  induction r with
  | zero =>
      change Module.FaithfullyFlat A A
      infer_instance
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      let : Module.FaithfullyFlat A T :=
        ih (Fin.init n) (Fin.init a) (fun i => hn i.castSucc)
      let : Nontrivial T :=
        (FaithfulSMul.algebraMap_injective A T).nontrivial
      let : Module.FaithfullyFlat T (AdjoinRoot f) :=
        faithfullyFlat_adjoinRoot_X_pow_sub_C
          (hn (Fin.last r)) (algebraMap A T (a (Fin.last r)))
      change Module.FaithfullyFlat A (AdjoinRoot f)
      exact Module.FaithfullyFlat.trans A T (AdjoinRoot f)

/--
If a finite diagonal iterated Kummer radical is formally unramified over its
base, then every exponent is a unit in that base.
-/
theorem all_exponents_isUnit_of_formallyUnramified_iteratedRadical
    {A : Type u} [CommRing A] [Nontrivial A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    [hFU : Algebra.FormallyUnramified A (iteratedRadical A r n a)] :
    ∀ i, IsUnit (n i : A) := by
  induction r with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      change Algebra.FormallyUnramified A (AdjoinRoot f) at hFU
      let : Module.FaithfullyFlat A T :=
        faithfullyFlat_iteratedRadical
          (Fin.init n) (Fin.init a) (fun i => hn i.castSucc)
      let : Nontrivial T :=
        (FaithfulSMul.algebraMap_injective A T).nontrivial
      have hnLast : IsUnit (n (Fin.last r) : A) :=
        isUnit_natCast_of_formallyUnramified_relativeRadical
          (A := A) (T := T) (a := algebraMap A T (a (Fin.last r)))
          (n := n (Fin.last r)) (hn (Fin.last r))
      have hPrefix : Algebra.FormallyUnramified A T :=
        formallyUnramified_prefix_of_formallyUnramified_relativeRadical
          (A := A) (T := T) (a := algebraMap A T (a (Fin.last r)))
          (n := n (Fin.last r)) (hn (Fin.last r))
      let : Algebra.FormallyUnramified A T := hPrefix
      have hInit : ∀ i : Fin r, IsUnit (n i.castSucc : A) :=
        ih (Fin.init n) (Fin.init a)
          (fun i => hn i.castSucc)
      intro i
      exact Fin.lastCases hnLast hInit i

end EtaleFundamentalGroups.Kummer
