/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.AdjoinRoot.FormallyEtale
import EtaleFundamentalGroups.Kummer.Obstructions.EtaleDerivative
import EtaleFundamentalGroups.Kummer.Descent.FormallyUnramifiedDescent

/-!
# Descent through a relative Kummer radical

For the final stage of a relative Kummer construction, formal
unramifiedness over the prefix makes the derivative a unit.  Monicity then
makes the final stage formally etale.  Its positive-degree monic
presentation is faithfully flat, so formal unramifiedness descends to the
prefix.

All algebra structures and scalar towers below are the canonical instances
provided by `AdjoinRoot`.
-/

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u v

/--
If the total relative Kummer algebra is formally unramified over the
original base, then its prefix is formally unramified too.
-/
theorem formallyUnramified_prefix_of_formallyUnramified_relativeRadical
    {A : Type u} {T : Type v}
    [CommRing A] [CommRing T] [Algebra A T]
    [Nontrivial T]
    {a : T} {n : ℕ} (hn : 0 < n)
    [Algebra.FormallyUnramified A
      (AdjoinRoot (X ^ n - C a))] :
    Algebra.FormallyUnramified A T := by
  let f : T[X] := X ^ n - C a
  have hDerivative :
      IsUnit (aeval (AdjoinRoot.root f) f.derivative) := by
    let : Algebra.FormallyUnramified T (AdjoinRoot f) :=
      Algebra.FormallyUnramified.of_restrictScalars A T (AdjoinRoot f)
    exact isUnit_aeval_derivative_of_formallyUnramified f
  let : Algebra.FormallyEtale T (AdjoinRoot f) :=
    formallyEtale_adjoinRoot_of_monic_of_isUnit_aeval_derivative
      (Polynomial.monic_X_pow_sub_C a hn.ne') hDerivative
  let : Module.FaithfullyFlat T (AdjoinRoot f) :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hn a
  exact
    formallyUnramified_of_formallyEtale_faithfullyFlat
      (R := A) (S := T) (T := AdjoinRoot f)

end EtaleFundamentalGroups.Kummer
