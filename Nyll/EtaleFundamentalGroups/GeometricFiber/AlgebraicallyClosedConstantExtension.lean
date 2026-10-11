/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.ConnectedFiberFullyFaithful
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleOverAlgebraicallyClosed
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleConnected

/-!
# Full faithfulness under algebraically closed constant extension

For any scheme over an algebraically closed field, every extension
of constants induces a fully faithful functor on finite etale covers. The
extension may be transcendental and its target need not be algebraically
closed. No properness or finite-type assumption is needed for this part of
the comparison.

The field extension is geometrically irreducible and universally open.
Actual descent of finite etale sections along its base change supplies
fullness, without a connectedness assumption or a chosen geometric point.

This supplies full faithfulness in Stacks 0A49. Essential surjectivity for
proper schemes is separate.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Finite etale covers and their morphisms are fully faithfully preserved
by any extension of an algebraically closed constant field. -/
def pullbackFullyFaithful_of_isAlgClosed_constant_extension
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    (pullback (Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).FullyFaithful := by
  let i : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hIrreducible : GeometricallyIrreducible i :=
    GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed i
  have hConnected : GeometricallyConnected i :=
    GeometricallyIrreducible.geometricallyConnected i
  let p : Limits.pullback f i ⟶ X := Limits.pullback.fst f i
  exact pullbackFullyFaithful_of_universallyOpen_geometricallyConnected p

end AlgebraicGeometry.FiniteEtale
