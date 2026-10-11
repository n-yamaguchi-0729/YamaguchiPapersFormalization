/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.ClosedPushforward
import Nyll.EtaleCohomology.Classical.Etale
import Nyll.EtaleCohomology.Classical.ExactSequence
import Nyll.EtaleCohomology.Classical.ModuleCohomology
import Nyll.EtaleCohomology.Sites.Localization
import Nyll.EtaleCohomology.Sites.ExtensionByZero
import Nyll.EtaleCohomology.Sites.OpenAdjunction
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Mathlib.Algebra.Exact.Basic

/-!
# The classical open-closed cohomology sequence

For a closed immersion and its open complement, the localization short exact
sequence gives a coefficient-linear long exact sequence

`Hⁿ(X, j_!j*F) → Hⁿ(X, F) → Hⁿ(Z, i*F) → Hⁿ⁺¹(X, j_!j*F)`.

The closed term is the actual classical cohomology of `Z`, using the proved
closed direct-image comparison. All three consecutive pairs are exact.
No ground field, noetherian, constructibility, or torsion assumption is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

variable {X Z U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i] (R : Type u) [CommRing R]
  (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))

/-- The map induced by the counit for extension by zero. -/
def etaleOpenExtensionCohomologyMap (n : ℕ) :
    etaleCohomology X R
        ((etaleExtensionByZero j R).obj ((etalePullback j R).obj F)) n →ₗ[R]
      etaleCohomology X R F n :=
  Classical.cohomologyMap.{u + 1, u, u, u, u}
    ((etaleExtensionByZeroAdjunction j R).counit.app F) n

/-- Restriction to the closed subscheme, expressed in its own classical cohomology. -/
def etaleClosedRestrictionCohomologyMap (n : ℕ) :
    etaleCohomology X R F n →ₗ[R]
      etaleCohomology Z R ((etalePullback i R).obj F) n :=
  (etaleCohomologyClosedPushforwardEquiv i R ((etalePullback i R).obj F) n).toLinearMap.comp
    (Classical.cohomologyMap.{u + 1, u, u, u, u}
      ((etalePullbackPushforwardAdjunction i R).unit.app F) n)

variable (hcompl : Set.range j = (Set.range i)ᶜ)

/-- The boundary map of open-closed localization, with the closed cohomology
term transported along the canonical direct-image comparison. -/
def etaleLocalizationConnecting (n : ℕ) :
    etaleCohomology Z R ((etalePullback i R).obj F) n →ₗ[R]
      etaleCohomology X R
        ((etaleExtensionByZero j R).obj ((etalePullback j R).obj F)) (n + 1) :=
  (Classical.connecting.{u + 1, u, u, u, u}
    (openClosedLocalization_shortExact j i hcompl R F) n).comp
      (etaleCohomologyClosedPushforwardEquiv i R
        ((etalePullback i R).obj F) n).symm.toLinearMap

include hcompl in
/-- Exactness at `Hⁿ(X,F)` in the localization sequence. -/
lemma etaleLocalization_exact (n : ℕ) :
    Function.Exact (etaleOpenExtensionCohomologyMap j R F n)
      (etaleClosedRestrictionCohomologyMap i R F n) := by
  let S := openClosedLocalizationComplex j i hcompl R F
  exact (LinearEquiv.postcomp_exact_iff_exact
    (f := Classical.cohomologyMap.{u + 1, u, u, u, u} S.f n)
    (g := Classical.cohomologyMap.{u + 1, u, u, u, u} S.g n)
    (e := etaleCohomologyClosedPushforwardEquiv i R ((etalePullback i R).obj F) n)).mpr
      (Classical.cohomology_exact.{u + 1, u, u, u, u}
        (openClosedLocalization_shortExact j i hcompl R F) n)

/-- Exactness at `Hⁿ(Z,i*F)` in the localization sequence. -/
lemma etaleLocalization_exact_connecting (n : ℕ) :
    Function.Exact (etaleClosedRestrictionCohomologyMap i R F n)
      (etaleLocalizationConnecting j i R F hcompl n) := by
  let S := openClosedLocalizationComplex j i hcompl R F
  let hS := openClosedLocalization_shortExact j i hcompl R F
  exact (LinearEquiv.conj_exact_iff_exact
    (Classical.cohomologyMap.{u + 1, u, u, u, u} S.g n)
    (Classical.connecting.{u + 1, u, u, u, u} hS n)
    (etaleCohomologyClosedPushforwardEquiv i R ((etalePullback i R).obj F) n)).mpr
      (Classical.cohomology_exact_connecting.{u + 1, u, u, u, u} hS n)

/-- Exactness at `Hⁿ⁺¹(X,j_!j*F)` in the localization sequence. -/
lemma etaleLocalization_connecting_exact (n : ℕ) :
    Function.Exact (etaleLocalizationConnecting j i R F hcompl n)
      (etaleOpenExtensionCohomologyMap j R F (n + 1)) := by
  let S := openClosedLocalizationComplex j i hcompl R F
  let hS := openClosedLocalization_shortExact j i hcompl R F
  exact (LinearEquiv.precomp_exact_iff_exact
    (f := Classical.connecting.{u + 1, u, u, u, u} hS n)
    (g := Classical.cohomologyMap.{u + 1, u, u, u, u} S.f (n + 1))
    (e := (etaleCohomologyClosedPushforwardEquiv i R
      ((etalePullback i R).obj F) n).symm)).mpr
      (Classical.connecting_exact_cohomology.{u + 1, u, u, u, u} hS n)

end EtaleCohomology
