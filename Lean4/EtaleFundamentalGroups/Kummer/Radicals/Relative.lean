/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Obstructions.EtaleDerivative
import EtaleFundamentalGroups.Kummer.Radicals.Explicit

/-!
# A Kummer radical relative to a faithfully flat prefix

This file treats the final stage of an iterated radical construction.  If
`T` is faithfully flat over `A`, formal unramifiedness of the radical over
`A` restricts to formal unramifiedness over `T`.  The explicit derivative
calculation then makes the exponent a unit in `T`, and faithful flatness
reflects that unit back to `A`.

`AdjoinRoot` already supplies the direct `A`-algebra structure and the scalar
tower through `T`, so no competing local algebra instances are installed.
-/

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u v

/--
For a Kummer radical over a faithfully flat `A`-algebra `T`, formal
unramifiedness over `A` forces its positive exponent to be a unit in `A`.
The radicand may be any element of `T`; no unit or descent hypothesis on it
is needed for this direction.

Taking `T` to be the algebra obtained from all preceding radicals gives the
last-exponent step for an iterated Kummer construction.
-/
theorem isUnit_natCast_of_formallyUnramified_relativeRadical
    {A : Type u} {T : Type v}
    [CommRing A] [CommRing T] [Algebra A T]
    [Nontrivial T] [Module.FaithfullyFlat A T]
    {a : T} {n : ℕ} (hn : 0 < n)
    [Algebra.FormallyUnramified A
      (AdjoinRoot (X ^ n - C a))] :
    IsUnit (n : A) := by
  let f : T[X] := X ^ n - C a
  have hDerivative :
      IsUnit (aeval (AdjoinRoot.root f) f.derivative) := by
    let : Algebra.FormallyUnramified T (AdjoinRoot f) :=
      Algebra.FormallyUnramified.of_restrictScalars A T (AdjoinRoot f)
    exact isUnit_aeval_derivative_of_formallyUnramified f
  have hnT : IsUnit (n : T) := by
    rw [aeval_derivative_X_pow_sub_C] at hDerivative
    have hMap :
        IsUnit (algebraMap T (AdjoinRoot f) (n : T)) :=
      ((Commute.all _ _).isUnit_mul_iff.mp hDerivative).1
    exact
      (isUnit_algebraMap_adjoinRoot_X_pow_sub_C_iff
        (A := T) (a := a) hn (n : T)).mp hMap
  exact (isUnit_map_iff (algebraMap A T) (n : A)).mp (by
    simpa using hnT)

end EtaleFundamentalGroups.Kummer
