/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentEtaleGenericGalois
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentNormalizationRamification
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.Connected
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Automorphisms of actual connected finite etale Laurent algebras

Connectedness of the spectrum supplies domain and normality from the finite-etale hypotheses.
Thus the original algebra is its base ring's integral closure in its actual fraction field.
Restriction of automorphisms identifies its automorphism group with the proved cyclic generic
Galois group. Normality and a generic-field comparison are not additional assumptions.
-/

noncomputable section

open EtaleFundamentalGroups

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- Every connected finite etale Laurent algebra over an algebraically closed field of
characteristic zero has cyclic automorphism group. Domain and normality are consequences. -/
theorem isCyclic_algEquiv_of_connected_finite_etale_laurent
    {K T : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [CommRing T] [Algebra (LaurentPolynomial K) T]
    [Module.Finite (LaurentPolynomial K) T] [Algebra.Etale (LaurentPolynomial K) T]
    [ConnectedSpace (PrimeSpectrum T)] : IsCyclic (T ≃ₐ[LaurentPolynomial K] T) := by
  let rationalAlgebra : Algebra (LaurentPolynomial K) (RatFunc K) := laurentRatFuncAlgebra K
  have fractionField : IsFractionRing (LaurentPolynomial K) (RatFunc K) :=
    laurentRatFunc_isFractionRing K
  have dedekind : IsDedekindDomain (LaurentPolynomial K) := laurentPolynomial_isDedekindDomain K
  have domain : IsDomain T := finiteEtale_isDomain_of_connectedSpace_primeSpectrum
    (R := LaurentPolynomial K) (T := T) (K := RatFunc K)
  have normal : IsIntegrallyClosed T :=
    finiteEtale_isIntegrallyClosed_of_connectedSpace_primeSpectrum
      (R := LaurentPolynomial K) (T := T) (K := RatFunc K)
  obtain ⟨extensionAlgebra, h⟩ :=
    exists_cyclic_galois_fractionField_of_finite_etale_laurent (K := K) (T := T)
  let E := FractionRing T
  let sharedExtension : Algebra (RatFunc K) E := extensionAlgebra
  let constantAlgebra : Algebra K E :=
    ((algebraMap (RatFunc K) E).comp (algebraMap K (RatFunc K))).toAlgebra
  obtain ⟨extensionTower, finiteE, _, cyclicE, _⟩ := h
  let restriction : (E ≃ₐ[RatFunc K] E) ≃* (T ≃ₐ[LaurentPolynomial K] T) :=
    galRestrict (LaurentPolynomial K) (RatFunc K) E T
  exact isCyclic_of_surjective restriction.toMonoidHom restriction.surjective

end AnabelianGeometry.GeometricFundamentalGroup
