/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.RegularBoundaryPurity
import Nyll.SchemeTheory.Affine.StalkLocalization
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.RingTheory.RegularLocalTrace
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain

/-!
# Normalization over a regular boundary stalk

Regularity along the original boundary supplies regularity at precisely the
boundary primes of the spectrum of a stalk. The canonical stalk-localization
isomorphism makes this transfer without assuming regularity of the entire
scheme or of every localization of an arbitrary regular local ring.
-/

noncomputable section

open AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

/-- Over the stalk of any regular boundary point, a finite separable
normalization that is étale off the boundary and at height-one primes is
étale everywhere. All domain and normality hypotheses on the stalk are
produced from the original boundary regularity assumption. -/
theorem integralClosure_stalk_etale_of_regular_boundary
    {X : Scheme.{u}} (I : X.IdealSheafData)
    (hregular : I.IsAmbientRegularAlongSupport)
    (x : X) (hx : x ∈ I.support)
    {K L : Type u} [Field K] [Algebra (X.presheaf.stalk x) K]
    [IsFractionRing (X.presheaf.stalk x) K]
    [Field L] [Algebra (X.presheaf.stalk x) L] [Algebra K L]
    [IsScalarTower (X.presheaf.stalk x) K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (haway : ∀ P : PrimeSpectrum (integralClosure (X.presheaf.stalk x) L),
      X.fromSpecStalk x
          (PrimeSpectrum.comap
            (algebraMap (X.presheaf.stalk x) (integralClosure (X.presheaf.stalk x) L)) P)
          ∉ I.support →
        Algebra.IsEtaleAt (X.presheaf.stalk x) P.asIdeal)
    (hheightOne : ∀ (p : Ideal (X.presheaf.stalk x)) [p.IsPrime], p.height = 1 →
      ∀ (P : Ideal (integralClosure (X.presheaf.stalk x) L)) [P.IsPrime] [P.LiesOver p],
        Algebra.IsEtaleAt (X.presheaf.stalk x) P) :
    Algebra.Etale (X.presheaf.stalk x) (integralClosure (X.presheaf.stalk x) L) := by
  let : IsRegularLocalRing (X.presheaf.stalk x) := hregular x hx
  let : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  let : IsIntegrallyClosed (X.presheaf.stalk x) :=
    SchemeTheory.isIntegrallyClosed_of_isRegularLocalRing (X.presheaf.stalk x)
  let Z : Set (PrimeSpectrum (X.presheaf.stalk x)) :=
    (X.fromSpecStalk x) ⁻¹' (I.support : Set X)
  have hZ : ∀ p ∈ Z, IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
    intro p hp
    let : IsRegularLocalRing (X.presheaf.stalk (X.fromSpecStalk x p)) :=
      hregular (X.fromSpecStalk x p) hp
    exact IsRegularLocalRing.of_ringEquiv (X.stalkFromSpecStalkEquivLocalization x p)
  exact SpecialLocalPurity.integralClosure_etale_of_regular_boundary
    (K := K) Z hZ haway hheightOne

end EtaleFundamentalGroups
