/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Lattices.UnramifiedCoprimality
import Nyll.EtaleFundamentalGroups.Kummer.Descent.MultiAwayUnitDescent

/-!
# Coprimality for a lattice cover on a boundary complement

For a finite lattice cover over the complement of a prime normal-crossings
boundary, formal unramifiedness makes every quotient subgroup order a unit on
the complement.  Componentwise characteristic zero then reflects that unit
to the original ring, where any characteristic-`p` specialization detects
coprimality.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators

universe uR uS uk

/-- Every subgroup of a formally unramified lattice cover on a full prime
boundary complement has unit order in the original ring. -/
theorem isUnit_natCard_subgroup_of_formallyUnramified_boundaryLatticeCover
    {R : Type uR} {S L : Type uS}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    {ι : Type*} (s : Finset ι) (t : ι → R)
    [IsLocalization.Away (∏ i ∈ s, t i) S]
    (ht : ∀ i ∈ s, Prime (t i))
    (hCharZero : ∀ i ∈ s, CharZero (R ⧸ Ideal.span {t i}))
    [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)]
    (hFU : (AddMonoidAlgebra.mapDomainRingHom S
      H.subtype.toAddMonoidHom).FormallyUnramified)
    (N : AddSubgroup (L ⧸ H)) :
    IsUnit (Nat.card N : R) := by
  have hBoundary_ne : (∏ i ∈ s, t i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi ↦ (ht i hi).ne_zero
  let : IsDomain S :=
    IsLocalization.Away.isDomain S hBoundary_ne
  have hcardS : IsUnit (Nat.card N : S) :=
    isUnit_natCard_subgroup_of_formallyUnramified_latticeCover
      (R := S) H hFU N
  exact isUnit_natCast_of_isUnit_algebraMap_away_finsetProduct
    (R := R) (S := S) s t ht hCharZero
      Nat.card_pos (by simpa using hcardS)

/-- Every subgroup of a formally unramified lattice cover on a full prime
boundary complement has order prime to a residue characteristic of the
original ring.  No cyclic coordinates, subgroup injection, or cardinality
comparison is supplied as an input. -/
theorem natCoprime_natCard_subgroup_of_formallyUnramified_boundaryLatticeCover
    {R : Type uR} {S L : Type uS} {k : Type uk}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    {ι : Type*} (s : Finset ι) (t : ι → R)
    [IsLocalization.Away (∏ i ∈ s, t i) S]
    (ht : ∀ i ∈ s, Prime (t i))
    (hCharZero : ∀ i ∈ s, CharZero (R ⧸ Ideal.span {t i}))
    [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)]
    (hFU : (AddMonoidAlgebra.mapDomainRingHom S
      H.subtype.toAddMonoidHom).FormallyUnramified)
    (N : AddSubgroup (L ⧸ H))
    [CommRing k] [Nontrivial k]
    (φ : R →+* k) (p : ℕ) [CharP k p] (hp : p.Prime) :
    Nat.Coprime (Nat.card N) p := by
  have hcardR : IsUnit (Nat.card N : R) :=
    isUnit_natCard_subgroup_of_formallyUnramified_boundaryLatticeCover
      (R := R) (S := S) s t ht hCharZero H hFU N
  have hcardk : IsUnit (Nat.card N : k) := by
    simpa using hcardR.map φ
  exact natCoprime_of_isUnit_natCast_of_charP p (Nat.card N) hp hcardk

end EtaleFundamentalGroups.Kummer
