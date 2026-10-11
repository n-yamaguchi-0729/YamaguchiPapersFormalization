/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Boundary.IteratedRadical
import EtaleFundamentalGroups.Kummer.Lattices.Coprimality
import EtaleFundamentalGroups.Inertia.Residue.Coprimality

/-!
# Character-group coprimality for an explicit boundary Kummer cover

A formally unramified finite iterated radical on the full boundary
complement makes every cyclic exponent a unit in the original ring.  Hence
the order of every concrete character subgroup of the corresponding product
of cyclic groups is a unit, and remains prime to any residue characteristic.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators

universe uR uS uk

/--
Every finite character subgroup of an explicit formally unramified boundary
Kummer cover has order prime to a residue characteristic of the base.

The character group is a concrete additive subgroup of the cyclic product;
no presentation, cardinality comparison, or inertia comparison is assumed.
-/
theorem natCoprime_natCard_characterSubgroup_of_formallyUnramified_boundaryIteratedRadical
    {R : Type uR} {S : Type uS} {k : Type uk}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [CommRing k] [Nontrivial k]
    {r : ℕ} (t : Fin r → R)
    [IsLocalization.Away
      (∏ i ∈ (Finset.univ : Finset (Fin r)), t i) S]
    (ht : ∀ i, Prime (t i))
    (hCharZero : ∀ i, CharZero (R ⧸ Ideal.span {t i}))
    (n : Fin r → ℕ) (hn : ∀ i, 0 < n i)
    [Algebra.FormallyUnramified S
      (iteratedRadical S r n (fun i ↦ algebraMap R S (t i)))]
    (N : AddSubgroup (∀ i, ZMod (n i)))
    (φ : R →+* k) (p : ℕ) [CharP k p] (hp : p.Prime) :
    Nat.Coprime (Nat.card N) p := by
  let (i : Fin r) : NeZero (n i) := ⟨(hn i).ne'⟩
  have hnR : ∀ i, IsUnit (n i : R) :=
    all_exponents_isUnit_of_formallyUnramified_boundaryIteratedRadical
      (R := R) (S := S) t ht hCharZero n hn
  have hcardR : IsUnit (Nat.card N : R) :=
    isUnit_natCard_of_injective_pi_zmod
      (R := R) n N.subtype N.subtype_injective hnR
  have hcardk : IsUnit (Nat.card N : k) := by
    simpa using hcardR.map φ
  exact
    natCoprime_of_isUnit_natCast_of_charP
      p (Nat.card N) hp hcardk

end EtaleFundamentalGroups.Kummer
