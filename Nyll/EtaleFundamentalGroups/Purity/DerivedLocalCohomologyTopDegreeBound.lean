/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyGeneratorCountDomain
import Nyll.EtaleFundamentalGroups.Purity.HartshorneLichtenbaumReduction

/-!
# Upper degree bound for maximal-support derived local cohomology

In a Noetherian local domain of finite Krull dimension `d`, choose `d`
parameters whose generated ideal has maximal radical.  Generator-count
vanishing for that ideal, followed by radical invariance, gives vanishing of
maximal-support derived local cohomology in every degree strictly above `d`.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing

namespace EtaleFundamentalGroups

universe u

/-- Maximal-support derived local cohomology of a Noetherian local domain
vanishes strictly above its finite Krull dimension. -/
theorem derivedLocalCohomology_maximalIdeal_isZero_of_ringKrullDim_lt
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    (d i : ℕ) (hdim : ringKrullDim R = (d : WithBot ℕ∞)) (hi : d < i) :
    IsZero
      (derivedLocalCohomology (maximalIdeal R) (ModuleCat.of R R) i) := by
  obtain ⟨xs, hlength, hradical⟩ :=
    exists_ofList_radical_eq_maximalIdeal_of_ringKrullDim_eq d hdim
  have hOfList :
      IsZero
        (derivedLocalCohomology (Ideal.ofList xs) (ModuleCat.of R R) i) :=
    derivedLocalCohomology_ofList_isZero_of_isDomain
      xs (ModuleCat.of R R) i (by omega)
  have hRadical :
      IsZero
        (derivedLocalCohomology (Ideal.ofList xs).radical
          (ModuleCat.of R R) i) :=
    (derivedLocalCohomology_isZero_iff_radical
      (Ideal.ofList xs) (ModuleCat.of R R) i).mp hOfList
  simpa only [hradical] using hRadical

/-- The first degree above the finite Krull dimension is zero. -/
theorem derivedLocalCohomology_maximalIdeal_isZero_succ_of_ringKrullDim_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = (d : WithBot ℕ∞)) :
    IsZero
      (derivedLocalCohomology (maximalIdeal R) (ModuleCat.of R R) (d + 1)) :=
  derivedLocalCohomology_maximalIdeal_isZero_of_ringKrullDim_lt
    d (d + 1) hdim (by omega)

end EtaleFundamentalGroups

end
