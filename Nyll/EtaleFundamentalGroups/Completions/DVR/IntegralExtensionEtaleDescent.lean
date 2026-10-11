/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.Chosen.DVRProductCoordinate
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Pi

/-!
# Etale descent from all completed DVR factors

For a finite integral Dedekind extension of a DVR, completion at the closed
point splits canonically as the product of the completed local factors.  If
every factor is etale over the completed base DVR, the completed tensor
product is etale; faithful flatness of DVR completion then descends etaleness
to the original extension.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uV uC uK uL

/-- Etaleness of every canonical completed local factor descends to the
original finite integral extension.  The product decomposition and the
faithfully-flat completion comparison are constructed internally. -/
theorem etale_of_completedPrimeValuationSubring_etale
    {V : Type uV} {C : Type uC}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsDedekindDomain C]
    [Algebra V C] [Algebra.IsIntegral V C]
    [Module.IsTorsionFree V C] [Module.Finite V C]
    {K : Type uK} [Field K] [Algebra V K] [IsFractionRing V K]
    {L : Type uL} [Field L] [Algebra C L] [IsFractionRing C L]
    (hlocal :
      let p := IsLocalRing.maximalIdeal V
      let H := standardDVFCompletionCompleteDVF V K
      let Vhat := H.valuationSubring
      let A := fun Q : p.primesOver C =>
        completedPrimeValuationSubring (L := L) Q
      letI : Algebra V Vhat :=
        standardDVFCompletionValuationSubringAlgebra V K
      letI : ∀ Q, Algebra Vhat (A Q) := fun Q =>
        completedPrimeValuationSubringCompletionAlgebra
          (V := V) (C := C) (K := K) (L := L) Q
      ∀ Q, Algebra.Etale Vhat (A Q)) :
    Algebra.Etale V C := by
  let p := IsLocalRing.maximalIdeal V
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  let A := fun Q : p.primesOver C =>
    completedPrimeValuationSubring (L := L) Q
  let : Algebra V Vhat :=
    standardDVFCompletionValuationSubringAlgebra V K
  let : Module.FaithfullyFlat V Vhat :=
    standardDVRCompletionValuationSubring_faithfullyFlat
      (V := V) (K := K)
  let U := Vhat ⊗[V] C
  let : Algebra Vhat U := Algebra.TensorProduct.leftAlgebra
  let : ∀ Q, Algebra Vhat (A Q) := fun Q =>
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q
  let : ∀ Q, Algebra.Etale Vhat (A Q) := hlocal
  let E : U ≃ₐ[Vhat] ∀ Q, A Q :=
    completedDVRIntegralExtensionLocalFactorsCompletionAlgEquiv
      (V := V) (C := C) (K := K) (L := L)
  let : Algebra.Etale Vhat (∀ Q, A Q) := inferInstance
  let : Algebra.Etale Vhat U := Algebra.Etale.of_equiv E.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Vhat

end EtaleFundamentalGroups

end
