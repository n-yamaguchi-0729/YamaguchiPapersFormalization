/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FiniteEtale.Algebra.NilpotentBaseChange
import EtaleFundamentalGroups.Purity.FiniteEtaleQuotientBaseChange

/-!
# Finite-etale equivalence across a nilpotent quotient

Over a complete Noetherian local ring, finite-etale algebras lift from every
quotient by an ideal in the maximal ideal.  For a nilpotent ideal, formal
etaleness also lifts every morphism uniquely.  Together these statements make
finite-etale base change an equivalence of categories.
-/

noncomputable section

open CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups

universe u

/-- Finite-etale base change from a complete Noetherian local ring to a
nilpotent quotient is an equivalence of categories. -/
theorem finiteEtale_baseChange_isEquivalence_of_isNilpotent
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : IsNilpotent I) :
    (CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ I)).IsEquivalence := by
  let F := CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ I)
  have hIle : I ≤ maximalIdeal R :=
    ((Ideal.FG.isNilpotent_iff_le_nilradical
      (IsNoetherian.noetherian I)).mp hI).trans
        (nilradical_le_prime (maximalIdeal R))
  let hff : F.FullyFaithful :=
    finiteEtale_baseChange_fullyFaithful_of_isNilpotent I hI
  let hes : F.EssSurj := finiteEtale_baseChange_essSurj_of_quotient I hIle
  exact
    { faithful := hff.faithful
      full := hff.full
      essSurj := hes }

/-- The categorical equivalence underlying finite-etale base change to a
nilpotent quotient of a complete Noetherian local ring. -/
noncomputable def finiteEtale_baseChange_equivalence_of_isNilpotent
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : IsNilpotent I) :
    CommAlgCat.FiniteEtale.{u} R ≌ CommAlgCat.FiniteEtale.{u} (R ⧸ I) := by
  let F := CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ I)
  letI : F.IsEquivalence :=
    finiteEtale_baseChange_isEquivalence_of_isNilpotent I hI
  exact F.asEquivalence

end EtaleFundamentalGroups

end
