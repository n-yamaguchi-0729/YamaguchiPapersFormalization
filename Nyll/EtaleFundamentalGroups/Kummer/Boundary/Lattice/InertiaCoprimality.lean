/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Boundary.Lattice.Coprimality
import Nyll.EtaleFundamentalGroups.Kummer.Lattices.FractionFieldGalois
import Nyll.EtaleFundamentalGroups.Inertia.Localized.Basic

/-!
# Coprimality of localized inertia for a boundary lattice cover

The fraction-field Galois group of a finite lattice cover is its quotient
character group.  This file sends localized normalization inertia through
that Galois equivalence and finite-character duality to an actual subgroup of
the quotient lattice.  Étaleness on the boundary complement then makes the
order of this subgroup, hence the order of inertia, prime to every residue
characteristic of the original boundary ring.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators

universe uR uS uA uk

/-- Localized normalization inertia in an étale finite lattice cover has unit
order in the original boundary ring.  The subgroup of the quotient lattice
and the equality of cardinalities are constructed inside the proof. -/
theorem isUnit_natCard_localizedNormalizationInertia_of_etale_boundaryLatticeCover
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
    ∀ (A : Type uA) [CommRing A] [IsDomain A]
      [Algebra A K] [IsFractionRing A K]
      [Algebra A E] [IsScalarTower A K E]
      (P : Ideal A) [P.IsPrime]
      (Q : Ideal (integralClosure A E)),
      IsUnit
        (Nat.card
          (localizedNormalizationInertia (K := K) (L := E) P Q) : R) := by
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
  intro A _ _ _ _ _ _ P _ Q
  let : Finite G :=
    latticeCharacterGroupFinite H.toAddSubgroup
  let : FaithfulSMul K E :=
    (faithfulSMul_iff_algebraMap_injective K E).mpr
      (RingHom.injective (algebraMap K E))
  have : IsGaloisGroup G K E :=
    latticeCharacter_isGaloisGroup_fractionRing H.toAddSubgroup
  let I := localizedNormalizationInertia (K := K) (L := E) P Q
  let galoisEquiv : G ≃* Gal(E/K) :=
    IsGaloisGroup.mulEquivAlgEquiv G K E
  let characterDuality : G ≃* Multiplicative (L ⧸ H) :=
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
      (Multiplicative (L ⧸ H)) S).some
  let galToQuotientMul : Gal(E/K) ≃* Multiplicative (L ⧸ H) :=
    galoisEquiv.symm.trans characterDuality
  let galToQuotientAdd : Additive Gal(E/K) ≃+ (L ⧸ H) :=
    galToQuotientMul.toAdditive.trans
      (AddEquiv.additiveMultiplicative (L ⧸ H))
  let N : AddSubgroup (L ⧸ H) :=
    I.toAddSubgroup.map galToQuotientAdd.toAddMonoidHom
  let eI : Additive I ≃+ N :=
    galToQuotientAdd.addSubgroupMap I.toAddSubgroup
  have hN : IsUnit (Nat.card N : R) :=
    isUnit_natCard_subgroup_of_formallyUnramified_boundaryLatticeCover
      (R := R) (S := S) (L := L)
      s t ht hBoundaryCharZero H hEtale.formallyUnramified N
  have hcard : Nat.card I = Nat.card N :=
    Nat.card_congr eI.toEquiv
  rw [hcard]
  exact hN

/-- Localized normalization inertia in an étale finite lattice cover has
order prime to every residue characteristic detected on the original
boundary ring. -/
theorem natCoprime_natCard_localizedNormalizationInertia_of_etale_boundaryLatticeCover
    {R : Type uR} {S L : Type uS} {k : Type uk}
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
      H.subtype.toAddMonoidHom).Etale)
    [CommRing k] [Nontrivial k]
    (φ : R →+* k) (p : ℕ) [CharP k p] (hp : p.Prime) :
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
    ∀ (A : Type uA) [CommRing A] [IsDomain A]
      [Algebra A K] [IsFractionRing A K]
      [Algebra A E] [IsScalarTower A K E]
      (P : Ideal A) [P.IsPrime]
      (Q : Ideal (integralClosure A E)),
      Nat.Coprime
        (Nat.card
          (localizedNormalizationInertia (K := K) (L := E) P Q)) p := by
  dsimp only
  intro A _ _ _ _ _ _ P _ Q
  have hcardR :=
    isUnit_natCard_localizedNormalizationInertia_of_etale_boundaryLatticeCover
      (R := R) (S := S) (L := L)
      s t ht hBoundaryCharZero H hEtale A P Q
  have hcardk := by
    simpa using hcardR.map φ
  exact natCoprime_of_isUnit_natCast_of_charP p _ hp hcardk

end EtaleFundamentalGroups.Kummer

end
