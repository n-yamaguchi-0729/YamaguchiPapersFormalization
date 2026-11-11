/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.ArithmeticBoundary
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Components of an effective Cartier boundary

The reduced prime components and their original ambient generic points are
shared by strict-local inertia and arithmetic boundary arguments.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Yamaguchi26SolvableCoverings

/-- The prime components of the divisor (their schemes have reduced structure). -/
abbrev Component {X : Scheme.{u}} (D : X.EffectiveCartierDivisor) :=
  { Z : Set D.1.subscheme // Z ∈ irreducibleComponents D.1.subscheme }

/-- The generic point of a prime component, regarded as a point of `X`. -/
def componentPoint {X : Scheme.{u}} (D : X.EffectiveCartierDivisor)
    (E : Component D) : X :=
  D.1.subschemeι E.property.1.genericPoint

end Yamaguchi26SolvableCoverings
