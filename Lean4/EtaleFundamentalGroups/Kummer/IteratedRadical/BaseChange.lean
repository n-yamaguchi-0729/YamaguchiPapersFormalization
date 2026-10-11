/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdjoinRoot
import EtaleFundamentalGroups.Kummer.IteratedRadical.Basic

/-!
# Base change of finite iterated radicals

The diagonal iterated radical construction commutes with arbitrary base
change.  The proof follows the recursive presentation and uses mathlib's
canonical base-change equivalence for `AdjoinRoot` at each step.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct

universe u

/--
Base change of a finite diagonal iterated radical is the corresponding
iterated radical after mapping all radicands to the new base.
-/
noncomputable def iteratedRadicalBaseChangeAlgEquiv
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) :
    C ⊗[A] iteratedRadical A r n a ≃ₐ[C]
      iteratedRadical C r n (fun i ↦ algebraMap A C (a i)) := by
  induction r with
  | zero =>
      change C ⊗[A] A ≃ₐ[C] C
      exact AlgEquiv.ofAlgHom
        ((Algebra.ofId A C).liftEquiv A C A C)
        (Algebra.TensorProduct.includeLeft : C →ₐ[C] C ⊗[A] A)
        (by ext)
        (by ext)
  | succ r ih =>
      let aBase : Fin (r + 1) → C := fun i ↦ algebraMap A C (a i)
      let Tₐ : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let Tbase : CommAlgCat.{u} C :=
        iteratedRadical C r (Fin.init n) (Fin.init aBase)
      let pₐ : Tₐ[X] :=
        X ^ n (Fin.last r) -
          Polynomial.C (algebraMap A Tₐ (a (Fin.last r)))
      let pBase : Tbase[X] :=
        X ^ n (Fin.last r) -
          Polynomial.C (algebraMap C Tbase (aBase (Fin.last r)))
      let ePrefix : C ⊗[A] Tₐ ≃ₐ[C] Tbase :=
        ih (Fin.init n) (Fin.init a)
      let q : (C ⊗[A] Tₐ)[X] :=
        pₐ.map Algebra.TensorProduct.includeRight.toRingHom
      change C ⊗[A] AdjoinRoot pₐ ≃ₐ[C] AdjoinRoot pBase
      have hcomm :
          ePrefix
              (algebraMap A C (a (Fin.last r)) ⊗ₜ[A] (1 : Tₐ)) =
            algebraMap C Tbase (algebraMap A C (a (Fin.last r))) := by
        simpa using ePrefix.commutes (algebraMap A C (a (Fin.last r)))
      exact
        (AdjoinRoot.tensorAlgEquiv pₐ q rfl).trans
          (AdjoinRoot.mapAlgEquiv ePrefix q pBase <| by
            apply Associated.of_eq
            simp [q, pₐ, pBase, aBase, hcomm])

end EtaleFundamentalGroups.Kummer
