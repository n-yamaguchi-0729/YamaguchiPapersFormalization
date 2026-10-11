/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Boundary.Lattice.RamificationUnit
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.LatticeInertiaCoprimality

/-!
# Lattice ramification units on a strict-normal-crossings chart

This file specializes the boundary lattice-cover ramification theorem to a
split strict-normal-crossings chart.  The chart supplies the prime boundary
parameters, while association with their product transports the given away
localization to the boundary product.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators

universe uR uS uA

/-- The ramification index of a height-one normalization prime in an étale
lattice cover of a split strict-normal-crossings complement is a unit in the
original boundary ring. -/
theorem isUnit_ramificationIdx_of_etale_splitStrictNormalCrossingsLatticeCover
    {R : Type uR} {S L : Type uS}
    [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing S] [Algebra R S]
    {d r : ℕ} (f : R) (t : Fin d → R)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    [IsLocalization.Away f S]
    (hBoundaryCharZero :
      ∀ i : Fin d, i.1 < r → CharZero (R ⧸ Ideal.span {t i}))
    [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)]
    [HasEnoughRootsOfUnity S
      (Monoid.exponent (Multiplicative (L ⧸ H)))]
    (hEtale : (AddMonoidAlgebra.mapDomainRingHom S
      H.subtype.toAddMonoidHom).Etale) :
    letI : IsLocalization.Away
        (∏ i ∈ boundaryIndices d r, t i) S := by
      change IsLocalization.Away (boundaryProduct t r) S
      exact IsLocalization.Away.of_associated hNC.2.2.2.2.1
    let hBoundary_ne :
        (∏ i ∈ boundaryIndices d r, t i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi ↦
        (hNC.2.2.2.1 i (Finset.mem_filter.mp hi).2).ne_zero
    letI : IsDomain S :=
      IsLocalization.Away.isDomain S hBoundary_ne
    let A₀ := AddMonoidAlgebra S H
    let B := AddMonoidAlgebra S L
    letI : UniqueSums L := latticeUniqueSums_of_freeIntModule L
    letI : UniqueSums H :=
      latticeSubgroupUniqueSums H.toAddSubgroup
    letI : IsDomain A₀ := inferInstance
    letI : IsDomain B := inferInstance
    letI : Algebra A₀ B :=
      latticeMapDomainAlgebra H.toAddSubgroup
    letI : FaithfulSMul A₀ B :=
      latticeMapDomainFaithfulSMul H.toAddSubgroup
    let K := FractionRing A₀
    let E := FractionRing B
    letI : Algebra K E := FractionRing.liftAlgebra A₀ E
    ∀ (A : Type uA) [CommRing A] [IsDomain A] [IsRegularRing A]
      [Algebra A K] [IsFractionRing A K]
      [Algebra A E] [IsScalarTower A K E]
      (P : Ideal A) [P.IsPrime] (_hP : P.height = 1)
      (Q : Ideal (integralClosure A E)) [Q.IsPrime] [Q.LiesOver P]
      [CharZero (A ⧸ P)],
      IsUnit (Q.ramificationIdx A : R) := by
  dsimp only
  have ht : ∀ i ∈ boundaryIndices d r, Prime (t i) := by
    intro i hi
    exact hNC.2.2.2.1 i (Finset.mem_filter.mp hi).2
  have hCharZero :
      ∀ i ∈ boundaryIndices d r,
        CharZero (R ⧸ Ideal.span {t i}) := by
    intro i hi
    exact hBoundaryCharZero i (Finset.mem_filter.mp hi).2
  let : IsLocalization.Away
      (∏ i ∈ boundaryIndices d r, t i) S := by
    change IsLocalization.Away (boundaryProduct t r) S
    exact IsLocalization.Away.of_associated hNC.2.2.2.2.1
  exact
    isUnit_ramificationIdx_of_etale_boundaryLatticeCover
      (R := R) (S := S) (L := L)
      (boundaryIndices d r) t ht hCharZero H hEtale

end EtaleFundamentalGroups.Kummer

end
