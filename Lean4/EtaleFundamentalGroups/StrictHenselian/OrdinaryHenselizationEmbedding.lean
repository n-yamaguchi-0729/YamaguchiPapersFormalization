/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.OrdinaryHenselizationUniversal
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianEmbedding
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Embedding the actual ordinary henselization

For a normal local domain, the original geometric-stalk algebraicity and
domain proofs apply at its ordinary residue-field point. An injective local
base map into a Henselian target therefore induces an injective universal
map. Every local target endomorphism fixing the base fixes this image, by
the already proved ordinary universal property.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {A S : Type u} [CommRing A] [IsLocalRing A]
  [CommRing S] [HenselianLocalRing S] (f : A →+* S) [IsLocalHom f]

/-- The actual universal map is fixed by every local endomorphism of the
target fixing the original base ring. No condition on the target residue
field action is required for the ordinary henselization. -/
theorem ordinaryHenselizationLift_comp_endomorphism
    (τ : S →+* S) [IsLocalHom τ] (hbase : τ.comp f = f) :
    τ.comp (ordinaryHenselizationLift f) = ordinaryHenselizationLift f := by
  apply ordinaryHenselizationLift_unique f
  rw [RingHom.comp_assoc, ordinaryHenselizationLift_comp_map, hbase]

/-- An injective local base map from a normal local domain gives an actual
embedding of its constructed ordinary henselization into the target. -/
theorem ordinaryHenselizationLift_injective [IsDomain A] [IsIntegrallyClosed A]
    (hf : Function.Injective f) : Function.Injective (ordinaryHenselizationLift f) := by
  let H := ordinaryHenselization A
  have : IsDomain H := inferInstanceAs (IsDomain
    (geometricStalk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))))
  let : Algebra A S := f.toAlgebra
  let : Algebra H S := (ordinaryHenselizationLift f).toAlgebra
  have : IsScalarTower A H S :=
    IsScalarTower.of_algebraMap_eq' (ordinaryHenselizationLift_comp_map f).symm
  have : Algebra.IsAlgebraic A H := geometricStalk_isAlgebraic (IsLocalRing.residue A)
  exact Algebra.IsAlgebraic.injective_tower_top H hf

end EtaleFundamentalGroups.StrictHenselian
