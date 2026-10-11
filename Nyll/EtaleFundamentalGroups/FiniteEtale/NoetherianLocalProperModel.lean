/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
import Mathlib.Algebra.Ring.ULift
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# An actual Noetherian local model of a proper flat finitely presented family

The existing finite-presentation approximation gives a proper flat model
over a finitely generated integer algebra. The existing local-subalgebra
construction makes its base Noetherian local inside the original local
ring. Pullback cancellation gives the actual original family back.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicCurves.Geometry.Schemes.Proofs.ProperFlatFinitePresentationDescent.ApproxAux

namespace AlgebraicGeometry

universe u

/-- A proper flat finitely presented family over an arbitrary local ring
comes from a proper flat family over an actual Noetherian local ring,
along a local ring homomorphism. -/
theorem exists_noetherian_local_proper_flat_model
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsNoetherianRing S) (_ : IsLocalRing S)
      (_ : Algebra S R) (_ : IsLocalHom (algebraMap S R)),
      ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of S)) (p : X ⟶ Y),
        IsProper g ∧ Flat g ∧
          IsPullback p f g (Spec.map (CommRingCat.ofHom (algebraMap S R))) := by
  let : Algebra (ULift.{u} ℤ) R :=
    ((algebraMap ℤ R).comp (ULift.ringEquiv (R := ℤ)).toRingHom).toAlgebra
  have hIntegers : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv (R := ℤ)).symm
  obtain ⟨T, hT, _, X₀, f₀, p₀, hProper₀, hFlat₀, hSquare₀⟩ :=
    ProperFlatFinitePresentationDescent (A₀ := ULift.{u} ℤ) f ∅
  have hFiniteTypeT : Algebra.FiniteType (ULift.{u} ℤ) T :=
    (Subalgebra.fg_iff_finiteType T).mp hT
  have hNoetherianT : IsNoetherianRing T :=
    Algebra.FiniteType.isNoetherianRing (ULift.{u} ℤ) T
  have hFiniteTypeBot : Algebra.FiniteType T (⊥ : Subalgebra T R) :=
    (Subalgebra.fg_iff_finiteType (⊥ : Subalgebra T R)).mp Subalgebra.fg_bot
  have hNoetherianBot : IsNoetherianRing (⊥ : Subalgebra T R) :=
    Algebra.FiniteType.isNoetherianRing T (⊥ : Subalgebra T R)
  obtain ⟨S, _, hNoetherianS, hLocalS, hUnits⟩ :=
    IsLocalRing.exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
      (⊥ : Subalgebra T R)
  have hLocalMap : IsLocalHom (algebraMap S R) := ⟨fun s => (hUnits s).mpr⟩
  let a : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (algebraMap T S))
  let g := pullback.snd f₀ a
  obtain ⟨p, hSquare⟩ := exists_isPullback_of_fac hSquare₀ a
    (Spec.map (CommRingCat.ofHom (algebraMap S R))) (specMap_algebraMap_comp S)
  exact ⟨S, inferInstance, hNoetherianS, hLocalS, inferInstance, hLocalMap,
    pullback f₀ a, g, p, inferInstance, inferInstance, hSquare⟩

end AlgebraicGeometry
