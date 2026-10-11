/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import EtaleFundamentalGroups.Completions.FiniteEtale.ResidueClassification
import EtaleFundamentalGroups.Kummer.AdjoinRoot.FormallyEtale

/-!
# Lifting a finite separable residue extension

Let `R` be a local ring and let `l / κ(R)` be finite separable.  We choose a
power-basis generator of `l`, lift its minimal polynomial coefficientwise to a
monic polynomial over `R`, and adjoin a root.  The resulting algebra is local,
finite, and étale over `R`, and its residue extension is `l / κ(R)`.

The local structure is not registered globally.  It is produced from the
explicit special fibre: quotienting the adjoined-root algebra by the extended
maximal ideal gives the adjoined root of the residue minimal polynomial, hence
a field.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Polynomial

universe u

variable (R l : Type u) [CommRing R] [IsLocalRing R]
  [Field l] [Algebra (IsLocalRing.ResidueField R) l]
  [FiniteDimensional (IsLocalRing.ResidueField R) l]
  [Algebra.IsSeparable (IsLocalRing.ResidueField R) l]

/-- A chosen power basis for a finite separable residue extension. -/
noncomputable def finiteEtaleResidueLiftPowerBasis :
    PowerBasis (IsLocalRing.ResidueField R) l :=
  Field.powerBasisOfFiniteOfSeparable _ _

private theorem exists_monic_residue_polynomial_lift :
    ∃ f : R[X],
      f.map (IsLocalRing.residue R) =
          minpoly (IsLocalRing.ResidueField R)
            (finiteEtaleResidueLiftPowerBasis R l).gen ∧
        f.natDegree =
          (minpoly (IsLocalRing.ResidueField R)
            (finiteEtaleResidueLiftPowerBasis R l).gen).natDegree ∧
        f.Monic := by
  let p := minpoly (IsLocalRing.ResidueField R)
    (finiteEtaleResidueLiftPowerBasis R l).gen
  have hp : p.Monic :=
    minpoly.monic (finiteEtaleResidueLiftPowerBasis R l).isIntegral_gen
  apply Polynomial.lifts_and_natDegree_eq_and_monic
  · rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective _ IsLocalRing.residue_surjective p
  · exact hp

/-- A monic lift of the minimal polynomial of a chosen residue generator. -/
noncomputable def finiteEtaleResidueLiftPolynomial : R[X] :=
  Classical.choose (exists_monic_residue_polynomial_lift R l)

theorem finiteEtaleResidueLiftPolynomial_map :
    (finiteEtaleResidueLiftPolynomial R l).map (IsLocalRing.residue R) =
      minpoly (IsLocalRing.ResidueField R)
        (finiteEtaleResidueLiftPowerBasis R l).gen :=
  (Classical.choose_spec (exists_monic_residue_polynomial_lift R l)).1

theorem finiteEtaleResidueLiftPolynomial_natDegree :
    (finiteEtaleResidueLiftPolynomial R l).natDegree =
      (minpoly (IsLocalRing.ResidueField R)
        (finiteEtaleResidueLiftPowerBasis R l).gen).natDegree :=
  (Classical.choose_spec (exists_monic_residue_polynomial_lift R l)).2.1

theorem finiteEtaleResidueLiftPolynomial_monic :
    (finiteEtaleResidueLiftPolynomial R l).Monic :=
  (Classical.choose_spec (exists_monic_residue_polynomial_lift R l)).2.2

/-- The explicit local lift of a finite separable residue extension. -/
abbrev FiniteEtaleResidueLift :=
  AdjoinRoot (finiteEtaleResidueLiftPolynomial R l)

/-- The extended closed-point ideal in the explicit residue lift. -/
def finiteEtaleResidueLiftClosedIdeal :
    Ideal (FiniteEtaleResidueLift R l) :=
  (IsLocalRing.maximalIdeal R).map
    (AdjoinRoot.of (finiteEtaleResidueLiftPolynomial R l))

/-- The special fibre of the explicit lift is the adjoined-root presentation
of the given residue extension. -/
noncomputable def finiteEtaleResidueLiftSpecialFiberRingEquiv :
    FiniteEtaleResidueLift R l ⧸ finiteEtaleResidueLiftClosedIdeal R l ≃+*
      AdjoinRoot
        ((finiteEtaleResidueLiftPolynomial R l).map
          (IsLocalRing.residue R)) :=
  AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot
    (IsLocalRing.maximalIdeal R)
    (finiteEtaleResidueLiftPolynomial R l)

@[simp]
theorem finiteEtaleResidueLiftSpecialFiberRingEquiv_mk (g : R[X]) :
    finiteEtaleResidueLiftSpecialFiberRingEquiv R l
        (Ideal.Quotient.mk (finiteEtaleResidueLiftClosedIdeal R l)
          (AdjoinRoot.mk (finiteEtaleResidueLiftPolynomial R l) g)) =
      AdjoinRoot.mk
        ((finiteEtaleResidueLiftPolynomial R l).map
          (IsLocalRing.residue R))
        (g.map (IsLocalRing.residue R)) :=
  AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of
    (IsLocalRing.maximalIdeal R)
    (finiteEtaleResidueLiftPolynomial R l) g

/-- The extended closed point in the explicit lift is maximal. -/
theorem finiteEtaleResidueLiftClosedIdeal_isMaximal :
    (finiteEtaleResidueLiftClosedIdeal R l).IsMaximal := by
  let q := (finiteEtaleResidueLiftPolynomial R l).map
    (IsLocalRing.residue R)
  let : Fact (Irreducible q) := ⟨by
    change Irreducible
      ((finiteEtaleResidueLiftPolynomial R l).map
        (IsLocalRing.residue R))
    rw [finiteEtaleResidueLiftPolynomial_map]
    exact minpoly.irreducible
      (finiteEtaleResidueLiftPowerBasis R l).isIntegral_gen⟩
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact
    (finiteEtaleResidueLiftSpecialFiberRingEquiv R l).toMulEquiv.isField
      (Field.toIsField (AdjoinRoot q))

/-- The explicit lift of a finite separable residue extension is local. -/
theorem isLocalRing_finiteEtaleResidueLift :
    IsLocalRing (FiniteEtaleResidueLift R l) := by
  let C := FiniteEtaleResidueLift R l
  let I := finiteEtaleResidueLiftClosedIdeal R l
  let : Module.Finite R C :=
    (finiteEtaleResidueLiftPolynomial_monic R l).finite_adjoinRoot
  let : Algebra.IsIntegral R C := Algebra.IsIntegral.of_finite R C
  refine IsLocalRing.of_unique_max_ideal
    ⟨I, finiteEtaleResidueLiftClosedIdeal_isMaximal R l, ?_⟩
  intro M hM
  let : M.IsMaximal := hM
  have hcomapMaximal :
      (M.comap (algebraMap R C)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R C)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) M
  have hcomap :
      M.comap (algebraMap R C) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal hcomapMaximal
  have hI_le : I ≤ M := by
    change finiteEtaleResidueLiftClosedIdeal R l ≤ M
    rw [finiteEtaleResidueLiftClosedIdeal, Ideal.map_le_iff_le_comap]
    simpa [C, AdjoinRoot.algebraMap_eq] using hcomap.ge
  exact
    ((finiteEtaleResidueLiftClosedIdeal_isMaximal R l).eq_of_le
      hM.ne_top hI_le).symm

/-- The maximal ideal of the explicit lift is the extended base maximal ideal. -/
theorem maximalIdeal_finiteEtaleResidueLift
    [IsLocalRing (FiniteEtaleResidueLift R l)] :
    IsLocalRing.maximalIdeal (FiniteEtaleResidueLift R l) =
      finiteEtaleResidueLiftClosedIdeal R l :=
  (IsLocalRing.eq_maximalIdeal
    (finiteEtaleResidueLiftClosedIdeal_isMaximal R l)).symm

/-- The reduction of the lifted derivative is nonzero, so the derivative at
the adjoined root is a unit. -/
theorem isUnit_aeval_derivative_finiteEtaleResidueLift :
    let C := FiniteEtaleResidueLift R l
    letI : IsLocalRing C := isLocalRing_finiteEtaleResidueLift R l
    IsUnit (aeval
      (AdjoinRoot.root (finiteEtaleResidueLiftPolynomial R l))
      (finiteEtaleResidueLiftPolynomial R l).derivative) := by
  dsimp only
  let f := finiteEtaleResidueLiftPolynomial R l
  let p := minpoly (IsLocalRing.ResidueField R)
    (finiteEtaleResidueLiftPowerBasis R l).gen
  let : IsLocalRing (FiniteEtaleResidueLift R l) :=
    isLocalRing_finiteEtaleResidueLift R l
  have hp_irreducible : Irreducible p :=
    minpoly.irreducible
      (finiteEtaleResidueLiftPowerBasis R l).isIntegral_gen
  have hp_separable : p.Separable :=
    Algebra.IsSeparable.isSeparable _
      (finiteEtaleResidueLiftPowerBasis R l).gen
  have hp_derivative_ne : p.derivative ≠ 0 :=
    (Polynomial.separable_iff_derivative_ne_zero hp_irreducible).1
      hp_separable
  let q := f.map (IsLocalRing.residue R)
  have hq_monic : q.Monic :=
    (finiteEtaleResidueLiftPolynomial_monic R l).map _
  have hq_derivative_ne : q.derivative ≠ 0 := by
    have hqp : q = p := by
      simpa [q, p, f] using finiteEtaleResidueLiftPolynomial_map R l
    rw [hqp]
    exact hp_derivative_ne
  have hqmk_ne : AdjoinRoot.mk q q.derivative ≠ 0 :=
    AdjoinRoot.mk_ne_zero_of_degree_lt hq_monic hq_derivative_ne
      (Polynomial.degree_derivative_lt hq_monic.ne_zero)
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
  intro hzero
  have hxmax :
      aeval (AdjoinRoot.root f) f.derivative ∈
        IsLocalRing.maximalIdeal (FiniteEtaleResidueLift R l) :=
    (IsLocalRing.residue_eq_zero_iff _).1 hzero
  have hxclosed :
      aeval (AdjoinRoot.root f) f.derivative ∈
        finiteEtaleResidueLiftClosedIdeal R l := by
    rw [← maximalIdeal_finiteEtaleResidueLift R l]
    exact hxmax
  have hquot :
      Ideal.Quotient.mk (finiteEtaleResidueLiftClosedIdeal R l)
          (aeval (AdjoinRoot.root f) f.derivative) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 hxclosed
  have hmap := congrArg
    (finiteEtaleResidueLiftSpecialFiberRingEquiv R l) hquot
  apply hqmk_ne
  dsimp only [f] at hmap
  simp only [AdjoinRoot.aeval_eq,
    finiteEtaleResidueLiftSpecialFiberRingEquiv_mk, map_zero] at hmap
  dsimp only [q, f]
  rw [Polynomial.derivative_map]
  exact hmap

/-- The explicit residue lift is finite as a module. -/
theorem moduleFinite_finiteEtaleResidueLift :
    Module.Finite R (FiniteEtaleResidueLift R l) :=
  (finiteEtaleResidueLiftPolynomial_monic R l).finite_adjoinRoot

/-- The explicit residue lift is faithfully acted on by the base. -/
theorem faithfulSMul_finiteEtaleResidueLift :
    FaithfulSMul R (FiniteEtaleResidueLift R l) := by
  let : IsLocalRing (FiniteEtaleResidueLift R l) :=
    isLocalRing_finiteEtaleResidueLift R l
  let : Module.Free R (FiniteEtaleResidueLift R l) :=
    (finiteEtaleResidueLiftPolynomial_monic R l).free_adjoinRoot
  infer_instance

/-- The explicit lift of a finite separable residue extension is finite étale. -/
theorem etale_finiteEtaleResidueLift :
    Algebra.Etale R (FiniteEtaleResidueLift R l) := by
  let : IsLocalRing (FiniteEtaleResidueLift R l) :=
    isLocalRing_finiteEtaleResidueLift R l
  let : Algebra.FormallyEtale R (FiniteEtaleResidueLift R l) :=
    Kummer.formallyEtale_adjoinRoot_of_monic_of_isUnit_aeval_derivative
      (finiteEtaleResidueLiftPolynomial_monic R l)
      (isUnit_aeval_derivative_finiteEtaleResidueLift R l)
  exact { }

/-- The residue extension of the explicit finite étale lift is the prescribed
finite separable extension. -/
noncomputable def finiteEtaleResidueLiftResidueAlgEquiv :
    let C := FiniteEtaleResidueLift R l
    letI : IsLocalRing C := isLocalRing_finiteEtaleResidueLift R l
    letI : Module.Finite R C := moduleFinite_finiteEtaleResidueLift R l
    letI : FaithfulSMul R C := faithfulSMul_finiteEtaleResidueLift R l
    letI : Algebra.IsIntegral R C := Algebra.IsIntegral.of_finite R C
    letI : IsLocalHom (algebraMap R C) :=
      Algebra.IsIntegral.isLocalHom R C
    IsLocalRing.ResidueField C ≃ₐ[IsLocalRing.ResidueField R] l := by
  dsimp only
  letI : IsLocalRing (FiniteEtaleResidueLift R l) :=
    isLocalRing_finiteEtaleResidueLift R l
  letI : Module.Finite R (FiniteEtaleResidueLift R l) :=
    moduleFinite_finiteEtaleResidueLift R l
  letI : FaithfulSMul R (FiniteEtaleResidueLift R l) :=
    faithfulSMul_finiteEtaleResidueLift R l
  letI : Algebra.IsIntegral R (FiniteEtaleResidueLift R l) :=
    Algebra.IsIntegral.of_finite R (FiniteEtaleResidueLift R l)
  letI : IsLocalHom (algebraMap R (FiniteEtaleResidueLift R l)) :=
    Algebra.IsIntegral.isLocalHom R (FiniteEtaleResidueLift R l)
  let f := finiteEtaleResidueLiftPolynomial R l
  let q := f.map (IsLocalRing.residue R)
  let p := minpoly (IsLocalRing.ResidueField R)
    (finiteEtaleResidueLiftPowerBasis R l).gen
  let hL : IsAdjoinRootMonic l p :=
    IsAdjoinRootMonic.mkOfAdjoinEqTop'
      (finiteEtaleResidueLiftPowerBasis R l).adjoin_gen_eq_top
  letI : Algebra R l :=
    ((algebraMap (IsLocalRing.ResidueField R) l).comp
      (IsLocalRing.residue R)).toAlgebra
  letI : IsScalarTower R (IsLocalRing.ResidueField R) l :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eR : IsLocalRing.ResidueField (FiniteEtaleResidueLift R l) ≃ₐ[R] l :=
    (Ideal.quotientEquivAlgOfEq R
      (maximalIdeal_finiteEtaleResidueLift R l)).trans <|
      (AdjoinRoot.quotEquivQuotMap f
        (IsLocalRing.maximalIdeal R)).trans <|
        (((AdjoinRoot.algEquivOfEq (IsLocalRing.ResidueField R) q p <| by
            simpa [q, p, f] using finiteEtaleResidueLiftPolynomial_map R l).trans
          hL.adjoinRootAlgEquiv).restrictScalars R)
  exact eR.extendScalarsOfSurjective IsLocalRing.residue_surjective

end EtaleFundamentalGroups

end
