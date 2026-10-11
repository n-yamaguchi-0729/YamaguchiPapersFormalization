/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import SchemeTheory.FiniteEtale.Away.AtUnit

/-!
# Boundary Away maps for finite towers with an integral etale target

An integral etale algebra is finite.  Over a Noetherian base, a preceding
finite tower therefore makes the literal composite map finitely presented.
Combining this with target-prime local Away etaleness gives etaleness of the
literal composite Away map.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uD uC

/-- Globalize target-prime local Away maps for a literal composite through a
finite algebra and an integral etale algebra. -/
theorem finiteTower_integralEtaleTarget_boundaryAway_of_local_awayMapsAtPrime
    {R : Type uR} {D : Type uD} {C : Type uC}
    [CommRing R] [CommRing D] [CommRing C]
    [IsNoetherianRing R]
    [Algebra D C] [Algebra.IsIntegral D C]
    (mapRD : R →+* D)
    (hfiniteRD :
      letI : Algebra R D := mapRD.toAlgebra
      Module.Finite R D)
    (hEtale : Algebra.Etale D C)
    (f : R)
    (hlocal :
      let mapRC : R →+* C :=
        (algebraMap D C).comp mapRD
      letI : Algebra R C := mapRC.toAlgebra
      ∀ (Q : Ideal C), [Q.IsPrime] →
        mapRC f ∉ Q →
        let p := Q.under R
        letI : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
          Localization.AtPrime.algebraOfLiesOver p Q
        let fp : Localization.AtPrime p :=
          algebraMap R (Localization.AtPrime p) f
        (Localization.awayMap
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q))
          fp).Etale) :
    (Localization.awayMap
      ((algebraMap D C).comp mapRD) f).Etale := by
  let : Algebra R D := mapRD.toAlgebra
  let : Module.Finite R D := hfiniteRD
  let mapRC : R →+* C :=
    (algebraMap D C).comp mapRD
  let : Algebra R C := mapRC.toAlgebra
  let : IsScalarTower R D C := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Etale D C := hEtale
  let : Module.Finite D C := Algebra.IsIntegral.finite
  let : Module.Finite R C := Module.Finite.trans D C
  let : Module.FinitePresentation R C :=
    Module.finitePresentation_of_finite R C
  let : Algebra.FinitePresentation R C :=
    Algebra.FinitePresentation.of_finitePresentation R C
  exact ringHom_localization_awayMap_etale_of_local_awayMapsAtPrime
    mapRC (by
      change Algebra.FinitePresentation R C
      infer_instance) f hlocal

end EtaleFundamentalGroups

end
