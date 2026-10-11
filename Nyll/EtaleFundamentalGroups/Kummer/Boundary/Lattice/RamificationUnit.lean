/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Boundary.Lattice.InertiaCoprimality
import Nyll.EtaleFundamentalGroups.Inertia.Localized.Cardinality

/-!
# Ramification-index units for an explicit boundary lattice cover

The explicit lattice-cover action supplies a finite Galois extension of
fraction fields.  At a height-one prime of a regular model, production
inertia cardinality then identifies the already-produced unit inertia order
with the ramification index.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators

universe uR uS uA

/-- The ramification index of a height-one normalization prime in an étale
boundary lattice cover is a unit in the original boundary coefficient ring.
The finite-dimensional and Galois field-extension instances are constructed
proof-locally from the quotient-character action. -/
theorem isUnit_ramificationIdx_of_etale_boundaryLatticeCover
    {R : Type uR} {S L : Type uS}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    {ι : Type*} (s : Finset ι) (t : ι → R)
    [IsLocalization.Away (∏ i ∈ s, t i) S]
    (ht : ∀ i ∈ s, Prime (t i))
    (hBoundaryCharZero :
      ∀ i ∈ s, CharZero (R ⧸ Ideal.span {t i}))
    [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)]
    [HasEnoughRootsOfUnity S
      (Monoid.exponent (Multiplicative (L ⧸ H)))]
    (hEtale : (AddMonoidAlgebra.mapDomainRingHom S
      H.subtype.toAddMonoidHom).Etale) :
    let hBoundary_ne : (∏ i ∈ s, t i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi ↦ (ht i hi).ne_zero
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
  have hBoundary_ne : (∏ i ∈ s, t i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi ↦ (ht i hi).ne_zero
  let : IsDomain S :=
    IsLocalization.Away.isDomain S hBoundary_ne
  let A₀ := AddMonoidAlgebra S H
  let B := AddMonoidAlgebra S L
  let : Finite (L ⧸ H.toAddSubgroup) := by
    change Finite (L ⧸ H)
    infer_instance
  let : HasEnoughRootsOfUnity S
      (Monoid.exponent (Multiplicative (L ⧸ H.toAddSubgroup))) := by
    change HasEnoughRootsOfUnity S
      (Monoid.exponent (Multiplicative (L ⧸ H)))
    infer_instance
  let G := Multiplicative (L ⧸ H.toAddSubgroup) →* Sˣ
  let K := FractionRing A₀
  let E := FractionRing B
  let : UniqueSums L := latticeUniqueSums_of_freeIntModule L
  let : UniqueSums H :=
    latticeSubgroupUniqueSums H.toAddSubgroup
  let : IsDomain A₀ := inferInstance
  let : IsDomain B := inferInstance
  let : Algebra A₀ B :=
    latticeMapDomainAlgebra H.toAddSubgroup
  let : FaithfulSMul A₀ B :=
    latticeMapDomainFaithfulSMul H.toAddSubgroup
  let : Algebra K E := FractionRing.liftAlgebra A₀ E
  let : MulSemiringAction G B :=
    latticeCharacterMulSemiringAction H.toAddSubgroup
  let : MulSemiringAction G E :=
    IsFractionRing.mulSemiringAction G B E
  intro A _ _ _ _ _ _ _ P _ hP Q _ _ _
  let : Finite G :=
    latticeCharacterGroupFinite H.toAddSubgroup
  have : IsGaloisGroup G K E :=
    latticeCharacter_isGaloisGroup_fractionRing H.toAddSubgroup
  let : FiniteDimensional K E :=
    IsGaloisGroup.finiteDimensional G K E
  let : IsGalois K E := IsGaloisGroup.isGalois G K E
  have hCardUnit :
      IsUnit
        (Nat.card
          (localizedNormalizationInertia (K := K) (L := E) P Q) : R) :=
    isUnit_natCard_localizedNormalizationInertia_of_etale_boundaryLatticeCover
      (R := R) (S := S) (L := L)
      s t ht hBoundaryCharZero H hEtale A P Q
  have hCardEq :
      Nat.card
          (localizedNormalizationInertia (K := K) (L := E) P Q) =
        Q.ramificationIdx A :=
    localizedNormalizationInertia_card_eq_ramificationIdx
      (K := K) (L := E) P hP Q
  rw [hCardEq] at hCardUnit
  exact hCardUnit

end EtaleFundamentalGroups.Kummer

end
