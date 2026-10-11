/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ChosenFactorCoordinates
import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.FiniteDiagonal
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SelectedBranch.ExponentUnitCompletion

/-!
# The canonical diagonal factor of a complete chosen factor

The residue-lift description of a complete chosen finite-etale factor has
two independent pieces of structure.

* a chosen-factor equivalence `B ⊗[A] C ≃ D`;
* the canonical separability idempotent in `C ⊗[A] C`.

The second piece really does select a canonical factor after any further
`C`-base change.  This file records the strongest comparison supplied by
that observation: after localizing at the separability idempotent, the
self-base change of the residue lift is canonically the original chosen
factor.

This is deliberately not stated as a comparison with a generic-fibre
component of a ramified radical cover.  The diagonal idempotent controls the
finite-etale residue-lift direction only; an action of the full radical
fraction field (or an equivalent normalization-local comparison) is still
needed to identify such a generic component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

/-- The canonical diagonal Away factor remains trivial after arbitrary
base change along the finite formally-unramified algebra.

For `E = C` this is the usual diagonal factor of `C ⊗[A] C`.  The
formulation with an arbitrary `C`-algebra `E` is the application-shaped form
needed for a complete chosen factor. -/
noncomputable def finiteUnramifiedDiagonalAwayBaseChangeEquiv
    {A C E : Type u}
    [CommRing A] [CommRing C] [CommRing E]
    [Algebra A C] [Algebra C E]
    [Module.Finite A C] [Algebra.FormallyUnramified A C] :
    E ⊗[C]
        Localization.Away (Algebra.FormallyUnramified.elem A C) ≃ₐ[E] E :=
  (Algebra.TensorProduct.congr
      (AlgEquiv.refl : E ≃ₐ[E] E)
      (finiteUnramifiedDiagonalAwayEquiv
        (R := A) (S := C))).trans
    (Algebra.TensorProduct.rid C E E)

/-- Install on a complete chosen factor the `C`-algebra structure transported
from `B ⊗[A] C ≃ D`.  Its canonical diagonal Away factor is then
literally trivial over `D`.

No component equality, tensor-coordinate bijectivity, or strict-Henselian
splitting hypothesis is used. -/
noncomputable def chosenFactorFiniteUnramifiedDiagonalAwayEquiv
    {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra B D]
    [Module.Finite A C] [Algebra.FormallyUnramified A C]
    (e : (B ⊗[A] C) ≃ₐ[B] D) :
    letI : Algebra C D := tensorChosenFactorRightAlgebra e
    D ⊗[C]
        Localization.Away (Algebra.FormallyUnramified.elem A C) ≃ₐ[D] D := by
  letI : Algebra C D := tensorChosenFactorRightAlgebra e
  exact finiteUnramifiedDiagonalAwayBaseChangeEquiv
    (A := A) (C := C) (E := D)

/-- The same diagonal trivialization before transporting the chosen factor
through `B ⊗[A] C ≃ D`.

This version makes explicit that the base of the trivial factor is the
tensor presentation `B ⊗[A] C` itself. -/
noncomputable def tensorChosenFactorFiniteUnramifiedDiagonalAwayEquiv
    {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [Module.Finite A C] [Algebra.FormallyUnramified A C] :
    let E := B ⊗[A] C
    letI : Algebra C E := Algebra.TensorProduct.rightAlgebra
    E ⊗[C]
        Localization.Away (Algebra.FormallyUnramified.elem A C) ≃ₐ[E] E := by
  dsimp only
  let E := B ⊗[A] C
  letI : Algebra C E := Algebra.TensorProduct.rightAlgebra
  exact finiteUnramifiedDiagonalAwayBaseChangeEquiv
    (A := A) (C := C) (E := E)

end EtaleFundamentalGroups

end
