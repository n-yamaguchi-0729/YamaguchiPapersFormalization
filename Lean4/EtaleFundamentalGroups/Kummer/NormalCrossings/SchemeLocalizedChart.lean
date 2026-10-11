/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.Scheme
import SchemeTheory.Divisors.NormalCrossings.Transport

/-!
# Localized strict-normal-crossings charts

A height-two point in a local scheme carries a split strict-normal-crossings
chart after prime localization.  This file retains the equality between the
localized boundary ideal and the product of the active parameters; later
arithmetic arguments need that equality for every branch, not only for one
preselected branch.
-/

noncomputable section

open EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}

/-- A height-two prime containing the boundary produces a split chart in its
prime localization, together with the exact localized boundary ideal. -/
theorem IsStrictNormalCrossings.exists_localSplitChart_with_boundaryIdeal
    (hI : I.IsStrictNormalCrossings)
    (P : AlgebraicGeometry.Spec (X.presheaf.stalk x))
    (hPheight : P.asIdeal.height = 2)
    (hIP : I.stalkIdeal x ≤ P.asIdeal) :
    letI : P.asIdeal.IsPrime := P.isPrime
    let A := X.presheaf.stalk x
    let V := Localization.AtPrime P.asIdeal
    ∃ (r : ℕ) (t : Fin 2 → V),
      IsDomain V ∧ IsRegularRing V ∧
        (I.stalkIdeal x).map (algebraMap A V) =
          Ideal.span {boundaryProduct t r} ∧
        IsSplitStrictNormalCrossingsAt (boundaryProduct t r) t r := by
  let : P.asIdeal.IsPrime := P.isPrime
  dsimp only
  let A := X.presheaf.stalk x
  let V := Localization.AtPrime P.asIdeal
  obtain ⟨r, s, hdomainY, hregularY, hideal, hNC⟩ :=
    hI.localSplitChart_at_fromSpecStalk_of_height_two_of_stalkIdeal_le
      P hPheight hIP
  let e := X.stalkFromSpecStalkEquivLocalization x P
  let t : Fin 2 → V :=
    (e : X.presheaf.stalk (X.fromSpecStalk x P) → V) ∘ s
  let : IsDomain
      (X.presheaf.stalk (X.fromSpecStalk x P)) := hdomainY
  let : IsRegularRing
      (X.presheaf.stalk (X.fromSpecStalk x P)) := hregularY
  have hdomainV : IsDomain V :=
    e.symm.toMulEquiv.isDomain
      (X.presheaf.stalk (X.fromSpecStalk x P))
  let : IsDomain V := hdomainV
  have hregularV : IsRegularRing V := IsRegularRing.of_ringEquiv e
  have hboundary :
      (I.stalkIdeal x).map (algebraMap A V) =
        Ideal.span {boundaryProduct t r} := by
    rw [← I.map_stalkIdeal_stalkFromSpecStalkEquivLocalization x P,
      hideal, Ideal.map_span]
    simp only [Set.image_singleton, boundaryProduct, map_prod]
    change Ideal.span (Set.singleton (boundaryProduct
      ((e : X.presheaf.stalk (X.fromSpecStalk x P) → V) ∘ s) r)) =
      Ideal.span {boundaryProduct t r}
    rfl
  have hNCV :
      IsSplitStrictNormalCrossingsAt (boundaryProduct t r) t r := by
    simpa only [t, Function.comp_apply, boundaryProduct, map_prod] using
      hNC.map_ringEquiv e
  exact ⟨r, t, hdomainV, hregularV, hboundary, hNCV⟩

end AlgebraicGeometry.Scheme.IdealSheafData

end
