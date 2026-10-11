/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Integral closedness of finite lattice Laurent algebras

A one-variable Laurent algebra is the localization of a polynomial ring away
from `X`.  Polynomial rings over integrally closed domains are integrally
closed, and integral closedness survives this localization.  Iterating this
construction and transporting along the explicit finite-coordinate Laurent
equivalence gives the result for the lattice target in the Smith presentation.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u

open Polynomial

private theorem isIntegrallyClosed_addMonoidAlgebra_int
    {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] :
    IsIntegrallyClosed (AddMonoidAlgebra A ℤ) := by
  let : IsIntegrallyClosed A[X] := inferInstance
  apply isIntegrallyClosed_of_isLocalization
    (R := A[X]) (S := AddMonoidAlgebra A ℤ)
    (Submonoid.powers (X : A[X]))
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n X_ne_zero)

private def finLastInitAddEquiv (r : ℕ) :
    (Fin (r + 1) → ℤ) ≃+ (ℤ × (Fin r → ℤ)) :=
  { (Fin.snocEquiv (fun _ : Fin (r + 1) ↦ ℤ)).symm with
    map_add' := by
      intro x y
      ext <;> rfl }

/-- A Laurent algebra on finitely many independent integer coordinates is integrally closed. -/
theorem isIntegrallyClosed_finLaurent
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (r : ℕ) : IsIntegrallyClosed (AddMonoidAlgebra R (Fin r → ℤ)) := by
  induction r with
  | zero =>
      exact IsIntegrallyClosed.of_equiv
        (AddMonoidAlgebra.uniqueAlgEquiv R (Fin 0 → ℤ)).symm.toRingEquiv
  | succ r ih =>
      let A := AddMonoidAlgebra R (Fin r → ℤ)
      let : IsIntegrallyClosed A := ih
      let e : AddMonoidAlgebra R (Fin (r + 1) → ℤ) ≃+* AddMonoidAlgebra A ℤ :=
        (((AddMonoidAlgebra.domCongr R R (finLastInitAddEquiv r)).trans
          (AddMonoidAlgebra.curryAlgEquiv R)).toRingEquiv)
      let : IsIntegrallyClosed (AddMonoidAlgebra A ℤ) :=
        isIntegrallyClosed_addMonoidAlgebra_int
      exact IsIntegrallyClosed.of_equiv e.symm

/-- The Laurent algebra of a finite free integer lattice is integrally closed. -/
theorem latticeMonoidAlgebra_isIntegrallyClosed
    {R L : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] :
    IsIntegrallyClosed (AddMonoidAlgebra R L) := by
  let r := Module.finrank ℤ L
  let e : L ≃+ (Fin r → ℤ) := (Module.finBasis ℤ L).equivFun.toAddEquiv
  let : IsIntegrallyClosed
      (AddMonoidAlgebra R (Fin r → ℤ)) :=
    isIntegrallyClosed_finLaurent r
  exact IsIntegrallyClosed.of_equiv
    (AddMonoidAlgebra.domCongr R R e).symm.toRingEquiv

end EtaleFundamentalGroups.Kummer
