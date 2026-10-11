/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NativeRamificationDiagram
import Nyll.ProCGroups.ProC.InverseLimits.Predicates
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Every conclusion of the DVR ramification theorem

This is an output certificate on a concrete native diagram. It is never an
input to the original-input theorem. Both exact sequences, the independent
wild subgroup, the actual invertible degrees, the canonical continuous
character, decomposition equivariance and its induced quotient isomorphism
are stated explicitly. The roots group is definitionally the inverse limit
with the literal power transitions on the displayed degrees.
-/

namespace EtaleFundamentalGroups.Inertia

universe u w

attribute [local instance] NativeRamificationResidues.baseResidueField
  NativeRamificationResidues.residueField NativeRamificationDiagram.inertiaTopology
  NativeRamificationDiagram.tameQuotientTopology

/-- All conclusions of Stacks Project Tag 0BUA on the displayed native data. -/
structure NativeRamificationConclusions
    (R : NativeRamificationResidues.{u, w}) (D : NativeRamificationDiagram R) : Prop where
  /-- The first sequence starts with the literal injective inclusion. -/
  inertia_inclusion_injective : Function.Injective D.inertiaInclusion.hom'.toFun
  /-- The image of inertia is precisely the residue-action kernel. -/
  residue_kernel : D.residueMorphism.hom'.ker = D.inertiaInclusion.hom'.range
  /-- The residue action is onto. -/
  residue_surjective : Function.Surjective D.residueMorphism.hom'.toFun
  /-- Wild inertia is normal in the original decomposition group. -/
  wild_normal_in_decomposition : (D.wild.map D.inertiaInclusion.hom').Normal
  /-- Wild inertia is pro-p in positive residue characteristic. -/
  wild_pro_p : ∀ (p : ℕ) [Fact p.Prime] [CharP R.baseResidue p],
    let : Group (Subtype D.wild.carrier) := Subgroup.toGroup D.wild
    let : TopologicalSpace (Subtype D.wild.carrier) :=
      TopologicalSpace.induced
        (fun σ : Subtype D.wild.carrier => (show D.inertia.carrier from σ.val))
        D.inertiaTopology
    CompactSpace (Subtype D.wild.carrier) ∧
      T2Space (Subtype D.wild.carrier) ∧
      TotallyDisconnectedSpace (Subtype D.wild.carrier) ∧
      IsTopologicalGroup (Subtype D.wild.carrier) ∧
      ProCGroups.ProC.HasPGroupOpenNormalBasis p (Subtype D.wild.carrier)
  /-- Wild inertia is trivial in residue characteristic zero. -/
  wild_char_zero : ∀ [CharZero R.baseResidue], D.wild = ⊥
  /-- The actual set of tame degrees is nonempty. -/
  degrees_nonempty : R.degrees.Nonempty
  /-- The actual degrees are multiplicatively directed. -/
  degrees_directed : Directed (· ≤ ·)
    (id : {n : InvertibleExponent R.baseResidue // R.degrees n} →
      {n : InvertibleExponent R.baseResidue // R.degrees n})
  /-- The encoding consists of positive residue-invertible natural integers. -/
  degrees_positive_invertible : ∀ n : {n : InvertibleExponent R.baseResidue // R.degrees n},
    0 < n.val.val ∧ IsUnit (n.val.val : R.baseResidue)
  /-- Thus every degree is prime to the positive residue characteristic. -/
  degrees_coprime : ∀ (p : ℕ) [Fact p.Prime] [CharP R.baseResidue p]
    (n : {n : InvertibleExponent R.baseResidue // R.degrees n}), Nat.Coprime n.val.val p
  /-- Every actual degree has a primitive root in the literal residue field. -/
  degrees_primitive_roots : ∀ n : {n : InvertibleExponent R.baseResidue // R.degrees n},
    ∃ ζ : R.residue, IsPrimitiveRoot ζ n.val.val
  /-- The same canonical tame character is continuous. -/
  character_continuous : Continuous D.character.hom'.toFun
  /-- It is onto the full displayed root limit. -/
  character_surjective : Function.Surjective D.character.hom'.toFun
  /-- Its kernel is the independently specified wild subgroup. -/
  character_kernel : D.character.hom'.ker = D.wild
  /-- It intertwines original conjugation with the original residue action. -/
  character_equivariant : ∀ (d : D.decomposition.carrier) (σ : D.inertia.carrier),
    D.character.hom'.toFun (D.conjugate d σ) =
      D.rootsAction d (D.character.hom'.toFun σ)
  /-- The second exact sequence ends in the literal onto quotient map. -/
  quotient_surjective : Function.Surjective D.quotientProjection.hom'.toFun
  /-- The literal quotient has precisely the independent wild kernel. -/
  quotient_kernel : D.quotientProjection.hom'.ker = D.wild
  /-- The same character induces an isomorphism from the literal tame quotient. -/
  quotient_isomorphism :
    ∃ e : D.tameQuotient.carrier ≃ₜ* R.rootsGroup.carrier,
      ∀ σ : D.inertia.carrier,
        e.toMulEquiv.toFun (D.quotientProjection.hom'.toFun σ) =
          D.character.hom'.toFun σ

end EtaleFundamentalGroups.Inertia
