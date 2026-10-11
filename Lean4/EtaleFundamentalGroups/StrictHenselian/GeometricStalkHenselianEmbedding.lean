/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianMap
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkGenericIntegral
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionTensor
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.TensorProduct.Basic


/-!
# Injectivity of the actual stalk map into a Henselian target

The previously constructed generic tensor is integral over the base fraction
field and is a fraction ring of the actual stalk. Native algebraicity
transfer therefore makes the stalk algebraic over the base. The native
algebraic-domain injection theorem then uses the already proved literal
base square to lift injectivity of the base map to the constructed stalk map.
No tensor equivalence or comparison injection is assumed or reconstructed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

private theorem algebraic_of_genericFractionRing
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A]
    (hIntegral : Algebra.IsIntegral (FractionRing R) (FractionRing R ⊗[R] A))
    (hFraction :
      let : Algebra A (FractionRing R ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
      IsFractionRing A (FractionRing R ⊗[R] A)) :
    Algebra.IsAlgebraic R A := by
  let K := FractionRing R
  let T := K ⊗[R] A
  let : Algebra A T := Algebra.TensorProduct.rightAlgebra
  have : IsFractionRing A T := hFraction
  have : Algebra.IsIntegral K T := hIntegral
  have : Algebra.IsAlgebraic R T :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := K) (C := T)).mpr inferInstance
  exact Algebra.IsAlgebraic.of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[R] T) (IsFractionRing.injective A T)

/-- The actual geometric stalk of a normal local domain is algebraic over
that domain, by the already constructed generic integral fraction ring. -/
theorem geometricStalk_isAlgebraic
    {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
    [Field Ω] (φ : R →+* Ω) [IsLocalHom φ] :
    let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    Algebra.IsAlgebraic R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  let G := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let : Algebra R G := (geometricStalkStructureMap φ).toAlgebra
  exact algebraic_of_genericFractionRing R G
    (geometricStalk_tensor_isIntegral φ (FractionRing R))
    (geometricStalk_genericTensor_isFractionRing φ)

/-- An injective local map from a normal local domain to a
Henselian target induces an injective map from its actual geometric stalk.
Injectivity is deduced from algebraicity and the literal base square. -/
theorem geometricStalkToHenselian_injective
    {R S : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
    [CommRing S] [HenselianLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Injective f) :
    Function.Injective (geometricStalkToHenselian f) := by
  let φ : R →+* IsLocalRing.ResidueField S := (IsLocalRing.residue S).comp f
  let G := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let : Algebra R G := (geometricStalkStructureMap φ).toAlgebra
  let : Algebra R S := f.toAlgebra
  let : Algebra G S := (geometricStalkToHenselian f).toAlgebra
  have : IsScalarTower R G S :=
    IsScalarTower.of_algebraMap_eq' (geometricStalkToHenselian_comp_structure f).symm
  have : Algebra.IsAlgebraic R G := geometricStalk_isAlgebraic φ
  exact Algebra.IsAlgebraic.injective_tower_top G hf

end EtaleFundamentalGroups.StrictHenselian
