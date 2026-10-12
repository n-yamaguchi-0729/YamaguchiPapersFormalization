/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.CohomologyPullbackCharacters
import Nyll.JacobianVarieties.Kummer.CohomologyPullback
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.Algebra.Group.IsCommutative
import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Actual H¹ pullback on the topological abelianization

When the target fundamental group is commutative, the actual scheme-induced
map factors through the source's quotient by its closed commutator subgroup.
The existing finite H¹ comparisons identify pullback with precomposition by
this actual factorization. Commutativity refers to the original group
operation; neither fundamental group is replaced by another group structure.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open EtaleFundamentalGroups.Cohomology
open scoped IsMulCommutative

namespace JacobianVarieties.Kummer

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
  (j : X ⟶ Y) (A : AddCommGrpCat.{u}) [Finite A]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
  [IsMulCommutative (Aut (FiniteEtale.fiber (ξ ≫ j)))]

/-- Finite H¹ pullback is precomposition by the actual map from the source
abelianization to the original, commutative target fundamental group. -/
theorem finiteH1AbelianCharacterEquiv_schemePullback
    (a : Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : CommGroup (Aut (FiniteEtale.fiber (ξ ≫ j))) := inferInstance
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    (finiteH1AbelianCharacterEquiv A ξ (constantCohomologyPullback j A 1 a)).toMul =
      (finiteH1CharacterEquiv A (ξ ≫ j) a).toMul.comp
        (ProCGroups.Abelian.TopologicalAbelianization.lift
          (FiniteEtale.fundamentalGroupHom j ξ)) := by
  intro targetComm coefficientTopology coefficientDiscrete
  apply ProCGroups.Abelian.TopologicalAbelianization.hom_ext
  intro g
  change h1AbelianCharacter A ξ (constantCohomologyPullback j A 1 a)
      (ProCGroups.Abelian.TopologicalAbelianization.mk _ g) =
    (finiteH1CharacterEquiv A (ξ ≫ j) a).toMul
      (ProCGroups.Abelian.TopologicalAbelianization.lift
        (FiniteEtale.fundamentalGroupHom j ξ)
        (ProCGroups.Abelian.TopologicalAbelianization.mk _ g))
  rw [h1AbelianCharacter_apply_mk,
    ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk]
  exact congrArg (fun χ => χ g) (h1Character_constantCohomologyPullback j A ξ a)

/-- Bijectivity of actual finite H¹ pullback is equivalent to bijectivity of
character precomposition by the same abelianized fundamental-group map. -/
theorem bijective_constantH1Pullback_iff_abelianCharacterPullback :
    let : CommGroup (Aut (FiniteEtale.fiber (ξ ≫ j))) := inferInstance
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    Function.Bijective (constantCohomologyPullback j A 1) ↔
      Function.Bijective
        ((ProCGroups.Abelian.TopologicalAbelianization.lift
          (FiniteEtale.fundamentalGroupHom j ξ)).compLeft (Multiplicative A)) := by
  intro targetComm coefficientTopology coefficientDiscrete
  let eX := (finiteH1AbelianCharacterEquiv A ξ).toEquiv.trans Additive.toMul
  let eY := (finiteH1CharacterEquiv A (ξ ≫ j)).toEquiv.trans Additive.toMul
  let f := ProCGroups.Abelian.TopologicalAbelianization.lift
    (FiniteEtale.fundamentalGroupHom j ξ)
  let q := f.compLeft (Multiplicative A)
  have hsquare : eX ∘ constantCohomologyPullback j A 1 = q ∘ eY := by
    funext a
    exact finiteH1AbelianCharacterEquiv_schemePullback j A ξ a
  calc
    Function.Bijective (constantCohomologyPullback j A 1) ↔
        Function.Bijective (eX ∘ constantCohomologyPullback j A 1) :=
      (Function.Bijective.of_comp_iff' eX.bijective _).symm
    _ ↔ Function.Bijective (q ∘ eY) := by rw [hsquare]
    _ ↔ Function.Bijective q := Function.Bijective.of_comp_iff q eY.bijective

end JacobianVarieties.Kummer
