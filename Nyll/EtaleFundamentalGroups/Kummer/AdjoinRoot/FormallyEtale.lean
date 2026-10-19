/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.StandardEtale
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit

/-!
# Formal etaleness of an explicit adjoined root

A monic equation whose derivative is a unit at its adjoined root is formally
etale.  Choosing the derivative itself as the denominator in a standard
etale presentation makes the Bezout condition tautological; localization at
that denominator then disappears because it is already a unit.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/--
If a monic polynomial has unit derivative at its adjoined root, then its
adjoined-root algebra is formally etale.
-/
theorem formallyEtale_adjoinRoot_of_monic_of_isUnit_aeval_derivative
    {A : Type u} [CommRing A] {f : A[X]} (hf : f.Monic)
    (hDerivative : IsUnit (aeval (AdjoinRoot.root f) f.derivative)) :
    Algebra.FormallyEtale A (AdjoinRoot f) := by
  have hmk : IsUnit (AdjoinRoot.mk f f.derivative) := by
    simpa only [AdjoinRoot.aeval_eq] using hDerivative
  let P : StandardEtalePair A :=
    { f := f
      monic_f := hf
      g := f.derivative
      cond := ⟨1, 0, 1, by rw [mul_one, mul_zero, add_zero, pow_one]⟩ }
  have hP : IsUnit (AdjoinRoot.mk P.f P.g) := by
    change IsUnit (AdjoinRoot.mk f f.derivative)
    exact hmk
  let eUnit :
      AdjoinRoot P.f ≃ₐ[AdjoinRoot P.f]
        Localization.Away (AdjoinRoot.mk P.f P.g) :=
    IsLocalization.atUnit
      (AdjoinRoot P.f)
      (Localization.Away (AdjoinRoot.mk P.f P.g))
      (AdjoinRoot.mk P.f P.g) hP
  let e : P.Ring ≃ₐ[A] AdjoinRoot P.f :=
    P.equivAwayAdjoinRoot.trans (eUnit.symm.restrictScalars A)
  change Algebra.FormallyEtale A (AdjoinRoot P.f)
  exact Algebra.FormallyEtale.of_equiv e

/--
The Kummer algebra `A[X]/(X ^ n - a)` is formally etale when the positive
exponent and the constant term are units.
-/
theorem formallyEtale_adjoinRoot_X_pow_sub_C
    {A : Type u} [CommRing A] {n : ℕ} (hn : 0 < n) {a : A}
    (hnUnit : IsUnit (n : A)) (ha : IsUnit a) :
    Algebra.FormallyEtale A (AdjoinRoot (X ^ n - C a)) := by
  refine formallyEtale_adjoinRoot_of_monic_of_isUnit_aeval_derivative
    (Polynomial.monic_X_pow_sub_C a hn.ne') ?_
  rw [aeval_derivative_X_pow_sub_C]
  exact
    (hnUnit.map (algebraMap A (AdjoinRoot (X ^ n - C a)))).mul
      ((isUnit_adjoinRoot_root_of_isUnit hn ha).pow (n - 1))

end EtaleFundamentalGroups.Kummer
