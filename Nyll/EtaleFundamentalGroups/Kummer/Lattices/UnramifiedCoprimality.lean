/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Lattices.Coprimality
import Nyll.EtaleFundamentalGroups.Kummer.Laurent.NestedDiagonalUnramified
import Nyll.EtaleFundamentalGroups.Inertia.Residue.Coprimality

/-!
# Coprimality for formally unramified finite lattice covers

A formally unramified finite-index lattice cover produces synchronized Smith
coordinates with unit exponents.  Every subgroup of the lattice quotient
therefore embeds in a product of cyclic groups of unit orders, so its order is
a unit in the coefficient ring and is prime to every residue characteristic.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u uk

/-- The order of every subgroup of the quotient lattice is a unit in the
coefficient ring when the associated lattice cover is formally unramified. -/
theorem isUnit_natCard_subgroup_of_formallyUnramified_latticeCover
    {R L : Type u} [CommRing R] [Nontrivial R]
    [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)]
    (hFU : (AddMonoidAlgebra.mapDomainRingHom R
      H.subtype.toAddMonoidHom).FormallyUnramified)
    (N : AddSubgroup (L ⧸ H)) :
    IsUnit (Nat.card N : R) := by
  obtain ⟨r, n, _hn, eQ, hnUnit⟩ :=
    exists_smithCyclicCoordinates_isUnit_of_formallyUnramified_latticeCover
      H hFU
  let χ : N →+ ∀ i, ZMod (n i) :=
    eQ.toAddMonoidHom.comp N.subtype
  have hχ : Function.Injective χ :=
    eQ.injective.comp N.subtype_injective
  exact isUnit_natCard_of_injective_pi_zmod n χ hχ hnUnit

/-- The order of every subgroup of the quotient lattice is prime to a residue
characteristic when the associated monoid-algebra cover is formally
unramified.  The cyclic coordinates and their unit orders are constructed
inside the proof; no character injection or cardinality comparison is an
input. -/
theorem natCoprime_natCard_subgroup_of_formallyUnramified_latticeCover
    {R L : Type u} {k : Type uk}
    [CommRing R] [Nontrivial R]
    [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)]
    (hFU : (AddMonoidAlgebra.mapDomainRingHom R
      H.subtype.toAddMonoidHom).FormallyUnramified)
    (N : AddSubgroup (L ⧸ H))
    [CommRing k] [Nontrivial k]
    (φ : R →+* k) (p : ℕ) [CharP k p] (hp : p.Prime) :
    Nat.Coprime (Nat.card N) p := by
  have hcardR : IsUnit (Nat.card N : R) :=
    isUnit_natCard_subgroup_of_formallyUnramified_latticeCover H hFU N
  have hcardk : IsUnit (Nat.card N : k) := by
    simpa using hcardR.map φ
  exact natCoprime_of_isUnit_natCast_of_charP p (Nat.card N) hp hcardk

end EtaleFundamentalGroups.Kummer
