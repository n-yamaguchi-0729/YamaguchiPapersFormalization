/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-!
# Smith coordinates for a finite-index lattice cover

Smith normal form gives coordinates in which a finite-index inclusion of free
integer lattices is diagonal.  The same Smith choice identifies the quotient
with a product of cyclic groups, while functoriality of additive monoid
algebras turns the inclusion into a commutative square of algebra maps.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u v

/--
A finite-index sublattice admits Smith coordinates.  The induced map of
additive monoid algebras is conjugate, through the coordinate equivalences, to
the coordinatewise diagonal map, and the same coefficients give cyclic
coordinates on the quotient lattice.
-/
theorem exists_smithDiagonal_monoidAlgebra
    {R : Type u} {L : Type v} [CommSemiring R] [AddCommGroup L]
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)] :
    ∃ (ι : Type v) (_ : Fintype ι) (a : ι → ℤ),
      (∀ i, a i ≠ 0) ∧
        ∃ (eH : H ≃+ (ι → ℤ)) (eL : L ≃+ (ι → ℤ))
          (d : (ι → ℤ) →+ (ι → ℤ))
          (_eQ : (L ⧸ H) ≃+ ∀ i, ZMod (Int.natAbs (a i))),
          (∀ x i, d x i = a i * x i) ∧
            (AddMonoidAlgebra.domCongr R R eL).toAlgHom.comp
                (AddMonoidAlgebra.mapDomainAlgHom R R H.subtype.toAddMonoidHom) =
              (AddMonoidAlgebra.mapDomainAlgHom R R d).comp
                (AddMonoidAlgebra.domCongr R R eH).toAlgHom := by
  let ι : Type v := Module.Free.ChooseBasisIndex ℤ L
  let : Fintype ι := Module.Free.ChooseBasisIndex.fintype ℤ L
  let b : Module.Basis ι ℤ L := Module.Free.chooseBasis ℤ L
  have hrank : Module.finrank ℤ H = Module.finrank ℤ L :=
    (Submodule.finiteQuotient_iff H).mp inferInstance
  let bL : Module.Basis ι ℤ L := H.smithNormalFormTopBasis b hrank
  let a : ι → ℤ := H.smithNormalFormCoeffs b hrank
  let bH : Module.Basis ι ℤ H := H.smithNormalFormBotBasis b hrank
  have hbasis : ∀ i, (bH i : L) = a i • bL i := by
    exact H.smithNormalFormBotBasis_def b hrank
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    exact H.smithNormalFormCoeffs_ne_zero b hrank i
  let eH : H ≃+ (ι → ℤ) := bH.equivFun.toAddEquiv
  let eL : L ≃+ (ι → ℤ) := bL.equivFun.toAddEquiv
  let d : (ι → ℤ) →+ (ι → ℤ) :=
    eL.toAddMonoidHom.comp
      (H.subtype.toAddMonoidHom.comp eH.symm.toAddMonoidHom)
  let eQ : (L ⧸ H) ≃+ ∀ i, ZMod (Int.natAbs (a i)) :=
    H.quotientEquivPiZMod b hrank
  have hcoordinate (x : ι → ℤ) :
      eL (H.subtype (eH.symm x)) = fun i ↦ a i * x i := by
    have hsubtype :
        H.subtype (bH.equivFun.symm x) =
          bL.equivFun.symm (fun i ↦ a i * x i) := by
      rw [bH.equivFun_symm_apply, bL.equivFun_symm_apply]
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro i _
      change x i • (bH i : L) = (a i * x i) • bL i
      rw [hbasis i, smul_smul, mul_comm]
    change bL.equivFun (H.subtype (bH.equivFun.symm x)) = _
    rw [hsubtype, bL.equivFun.apply_symm_apply]
  have hd : ∀ x i, d x i = a i * x i := by
    intro x i
    change eL (H.subtype (eH.symm x)) i = a i * x i
    exact congrFun (hcoordinate x) i
  have hsquare :
      (AddMonoidAlgebra.domCongr R R eL).toAlgHom.comp
          (AddMonoidAlgebra.mapDomainAlgHom R R H.subtype.toAddMonoidHom) =
        (AddMonoidAlgebra.mapDomainAlgHom R R d).comp
          (AddMonoidAlgebra.domCongr R R eH).toAlgHom := by
    rw [AddMonoidAlgebra.domCongr_toAlgHom,
      AddMonoidAlgebra.domCongr_toAlgHom,
      ← AddMonoidAlgebra.mapDomainAlgHom_comp,
      ← AddMonoidAlgebra.mapDomainAlgHom_comp]
    congr 1
    ext h
    simp [d]
  exact ⟨ι, inferInstance, a, ha, eH, eL, d, eQ, hd, hsquare⟩

end EtaleFundamentalGroups.Kummer
