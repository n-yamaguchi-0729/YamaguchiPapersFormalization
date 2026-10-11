/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.EtaleFundamentalGroups.Purity.LocalCohomologyRegularSequence

/-!
# Local cohomology at strict-normal-crossings points

The regular system of parameters supplied by a strict-normal-crossings chart
is a regular sequence generating the maximal ideal of the local ring.  This
file feeds that actual sequence into the regular-sequence vanishing theorem
for local cohomology.  The result is valid in every dimension represented by
the parameter family.
-/

noncomputable section

open CategoryTheory Limits
open RingTheory.Sequence

namespace EtaleFundamentalGroups

universe u

/-- A regular system of `d` parameters in a Noetherian local ring forces the
structure module's local cohomology supported at the maximal ideal to vanish
in every degree strictly below `d`. -/
theorem localCohomology_maximalIdeal_isZero_of_regularSystemOfParameters
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {d : ℕ} (t : Fin d → R)
    (ht : AlgebraicGeometry.Scheme.IsRegularSystemOfParameters t)
    (i : ℕ) (hi : i < d) :
    IsZero
      ((localCohomology (IsLocalRing.maximalIdeal R) i).obj
        (ModuleCat.of R R)) := by
  have hsmul :
      IsLocalRing.maximalIdeal R •
          (⊤ : Submodule R (ModuleCat.of R R)) < ⊤ := by
    have hne :
        IsLocalRing.maximalIdeal R •
            (⊤ : Submodule R (ModuleCat.of R R)) ≠ ⊤ := by
      exact Module.FaithfullyFlat.submodule_ne_top
        (IsLocalRing.maximalIdeal.isMaximal R)
    exact hne.lt_top
  apply localCohomology_isZero_of_isRegular
    (IsLocalRing.maximalIdeal R) (ModuleCat.of R R) hsmul
    (List.ofFn t)
  · intro r hr
    rw [← ht.2]
    exact Ideal.subset_span hr
  · exact ht.1
  · simpa only [List.length_ofFn] using hi

end EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}

/-- A strict-normal-crossings point supplies, without a dimension-two
restriction, a regular parameter chart whose full range of low-degree local
cohomology groups at the stalk's maximal ideal vanishes. -/
theorem IsStrictNormalCrossingsAt.exists_parameterChart_localCohomology_isZero
    (hI : I.IsStrictNormalCrossingsAt x) :
    let R := X.presheaf.stalk x
    ∃ (d r : ℕ) (t : Fin d → R),
      0 < r ∧ ∃ (hr : r ≤ d),
        AlgebraicGeometry.Scheme.IsRegularSystemOfParameters t ∧
          I.stalkIdeal x =
            Ideal.span
              {AlgebraicGeometry.Scheme.initialParameterProduct t r hr} ∧
          ∀ i : ℕ, i < d →
            IsZero
              ((localCohomology (IsLocalRing.maximalIdeal R) i).obj
                (ModuleCat.of R R)) := by
  dsimp only
  let R := X.presheaf.stalk x
  let hregular : IsRegularLocalRing R := hI.1
  let : IsLocalRing R := hregular.toIsLocalRing
  let : IsNoetherianRing R := hregular.toIsNoetherian
  obtain ⟨d, r, t, hrpos, hr, ht, hideal⟩ := hI.2
  refine ⟨d, r, t, hrpos, hr, ht, hideal, ?_⟩
  intro i hi
  exact
    EtaleFundamentalGroups.localCohomology_maximalIdeal_isZero_of_regularSystemOfParameters
      t ht i hi

end AlgebraicGeometry.Scheme.IdealSheafData
