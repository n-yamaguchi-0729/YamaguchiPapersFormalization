/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.Local.RegularLocalCompletionDescent
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrum
import Nyll.EtaleFundamentalGroups.StrictHenselian.FundamentalGroup
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Nyll.SchemeTheory.RingTheory.RegularLocalTrace

/-!
# Simple connectedness of regular strictly Henselian punctures

The punctured spectrum of a regular strictly Henselian local ring of dimension
at least two has trivial étale fundamental group at every geometric point.
Local purity extends its finite étale covers over the full local spectrum;
strict Henselianity makes the fundamental group of that spectrum trivial.

The regular-local purity input is Stacks Project, Lemma 58.21.3 (tag `0BMA`).
The dimension bound is essential: punctured strictly Henselian discrete
valuation rings can have nontrivial ramified covers.
-/

namespace EtaleFundamentalGroups

open AlgebraicGeometry CategoryTheory

universe u

/-- Every geometric étale fundamental group of the punctured spectrum of a
regular strictly Henselian local ring of dimension at least two is trivial. -/
theorem subsingleton_fundamentalGroup_puncturedSpectrum_of_regular_strictHenselian
    (R : Type u) [CommRing R] [IsRegularLocalRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim R)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Scheme.puncturedSpectrum R) : Subsingleton π₁ᵉᵗ(s) := by
  let : IsDomain R := IsRegularLocalRing.isDomain R
  let : IsIntegrallyClosed R := SchemeTheory.isIntegrallyClosed_of_isRegularLocalRing R
  have hpositive : (1 : WithBot ℕ∞) ≤ ringKrullDim R :=
    le_trans (by norm_num : (1 : WithBot ℕ∞) ≤ 2) hdim
  have hpurity : FiniteEtale.HasPuncturedPurity R :=
    hasPuncturedPurity_of_isRegularLocalRing R hdim
  let : Subsingleton π₁ᵉᵗ(s ≫ Scheme.puncturedSpectrumInclusion R) :=
    StrictHenselian.subsingleton_fundamentalGroup_of_strictHenselian R
      (s ≫ Scheme.puncturedSpectrumInclusion R)
  exact (FiniteEtale.fundamentalGroupHom_bijective_puncturedSpectrum_of_hasPuncturedPurity
    R hpositive hpurity s).1.subsingleton

end EtaleFundamentalGroups
