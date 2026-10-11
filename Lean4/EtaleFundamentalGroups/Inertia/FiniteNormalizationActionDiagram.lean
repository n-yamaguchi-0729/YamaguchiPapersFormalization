/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Ramification.ProfiniteRingActionRestriction
import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.FiniteGaloisRestrictionGroupMap
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationInclusionSquare
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import EtaleFundamentalGroups.Inertia.NativeNormalizationOriginalAction
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Actual finite-normalization ring-action diagrams

The field constructors are finished before the ordinary ring/group image
argument. All groups, rings, actions, maps, and primes are the existing
literal objects. Every non-data input to the ordinary image theorem is
proved below; no inertia-image theorem is used as a supplier.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] normalizationInertiaImageAction

section FieldOnly

variable (K : Type v) (L : Type w) [Field K] [Field L] [Algebra K L]

/-- The actual finite level is a field, proved before coefficient algebras
and normalization rings enter the scope. -/
theorem finiteGaloisIntermediateField_isField (E : FiniteGaloisIntermediateField K L) :
    IsField E := Field.toIsField E

/-- The prescribed Krull subspace topology on the actual fixing subgroup. -/
@[instance_reducible]
def finiteGaloisFixingTopology (E : FiniteGaloisIntermediateField K L) :
    TopologicalSpace E.toIntermediateField.fixingSubgroup := inferInstance

/-- Original field restriction is surjective, in a scope without normalization data. -/
theorem finiteGaloisRestrictionGroupMap_surjective [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) :
    Function.Surjective (finiteGaloisRestrictionGroupMap K L E).hom'.toFun :=
  AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) L

/-- The actual fixing subgroup is killed by the actual field restriction. -/
theorem finiteGaloisRestrictionGroupMap_fixes_kernel
    (E : FiniteGaloisIntermediateField K L) :
    ∀ g : (galoisGroupObject K L).carrier,
      E.toIntermediateField.fixingSubgroup.carrier g →
      (finiteGaloisRestrictionGroupMap K L E).hom'.toFun g = 1 := by
  intro g hg
  exact (IntermediateField.restrictNormalHom_ker E.toIntermediateField).ge hg

/-- Compactness of the actual kernel, proved before ring actions occur. -/
theorem finiteGaloisFixingTopology_compact [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) :
    let : TopologicalSpace E.toIntermediateField.fixingSubgroup := finiteGaloisFixingTopology K L E
    CompactSpace E.toIntermediateField.fixingSubgroup := by
  intro kernelTopology
  exact isCompact_iff_compactSpace.mp
    (IntermediateField.fixingSubgroup_isClosed E.toIntermediateField).isCompact

/-- The actual kernel inherits total disconnectedness from the Krull topology. -/
theorem finiteGaloisFixingTopology_totallyDisconnected [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) :
    let : TopologicalSpace E.toIntermediateField.fixingSubgroup := finiteGaloisFixingTopology K L E
    TotallyDisconnectedSpace E.toIntermediateField.fixingSubgroup := by
  intro kernelTopology
  infer_instance

/-- The actual kernel inherits its topological group structure. -/
theorem finiteGaloisFixingTopology_isTopologicalGroup
    (E : FiniteGaloisIntermediateField K L) :
    let : TopologicalSpace E.toIntermediateField.fixingSubgroup := finiteGaloisFixingTopology K L E
    IsTopologicalGroup E.toIntermediateField.fixingSubgroup := by
  intro kernelTopology
  infer_instance

/-- The infinite Galois correspondence detects membership in the literal
intermediate field, before any integral closure is introduced. -/
private theorem finiteField_mem_of_fixed [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) (x : L)
    (h : ∀ g : Gal(L/K), E.toIntermediateField.fixingSubgroup.carrier g →
      g.toRingHom.toFun x = x) : x ∈ E.toIntermediateField := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup E.toIntermediateField]
  exact (IntermediateField.mem_fixedField_iff E.toIntermediateField.fixingSubgroup x).mpr h

end FieldOnly

section RingOnly

variable {A : Type u} {L : Type w} [CommRing A] [CommRing L] [Algebra A L]

/-- A coefficient already in the literal subalgebra has an integral
preimage in its literal normalization. No fraction field is involved. -/
private theorem subalgebraNormalization_preimage_of_mem
    (S : Subalgebra A L) (b : integralClosure A L) (hb : S.carrier b.val) :
    ∃ c : (subalgebraNormalizationCommAlgCat S).carrier,
      (subalgebraNormalizationRingMap S).toFun c = b := by
  let x : S := ⟨b.val, hb⟩
  have hx : IsIntegral A x :=
    (isIntegral_algHom_iff S.val Subtype.val_injective).mp b.property
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  rfl

end RingOnly

section ActualData

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- The original finite normalization action, retained on the already
constructed native finite group and normalization carriers. -/
@[instance_reducible]
def finiteNormalizationOriginalAction (E : FiniteGaloisIntermediateField K L) :
    MulSemiringAction (finiteGaloisGroupObject K L E).carrier
      (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
  nativeNormalizationOriginalAction A K (finiteLevelFieldAlgebra A K L E)
    (finiteGaloisIntermediateField_isField K L E)

/-- The original ordinary ring-action data, with no theorem or comparison fields. -/
def finiteNormalizationActionDiagram (E : FiniteGaloisIntermediateField K L) :
    RingActionRestriction.{w, w, w, w} where
  lowerRing := CommRingCat.of (finiteAbsoluteNormalizationAlgebra A K L E).carrier
  upperRing := CommRingCat.of (normalizationCommAlgCat A L).carrier
  upperGroup := galoisGroupObject K L
  lowerGroup := finiteGaloisGroupObject K L E
  upperAction := normalizationInertiaImageAction A K L
  lowerAction := finiteNormalizationOriginalAction A K L E
  ringMap := finiteAbsoluteNormalizationRingMap A K L E
  groupMap := (finiteGaloisRestrictionGroupMap K L E).hom'
  kernelGroup := E.toIntermediateField.fixingSubgroup
  kernelTopology := finiteGaloisFixingTopology K L E

/-- Fixedness for the original action is detected on the literal coefficient.
The action square is the already proved actual normalization square. -/
private theorem originalNormalization_fixed_coefficient
    (g : Gal(L/K)) (b : integralClosure A L) (hb : g • b = b) :
    g.toRingHom.toFun b.val = b.val := by
  have hsquare := normalizationInertiaImageAction_comp_inclusion A K L g
  have hcoeff := congrArg
    (fun f : integralClosure A L →+* L => f.toFun b) hsquare
  exact hcoeff.trans (congrArg Subtype.val hb)

omit [IsGalois K L] in
/-- The original finite-action ring map agrees with the existing finite
normalization automorphism map, in a scope without the upper normalization. -/
theorem finiteNormalizationOriginalAction_ringHom
    (E : FiniteGaloisIntermediateField K L)
    (g : (finiteGaloisGroupObject K L E).carrier) :
    let : MulSemiringAction (finiteGaloisGroupObject K L E).carrier
        (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
      finiteNormalizationOriginalAction A K L E
    MulSemiringAction.toRingHom (finiteGaloisGroupObject K L E).carrier
        (finiteAbsoluteNormalizationAlgebra A K L E).carrier g =
      commAlgAutomorphismRingHom A (finiteAbsoluteNormalizationAlgebra A K L E)
        ((finiteNormalizationGaloisGroupMap A K L E).hom'.toFun g) := by
  intro finiteAction
  exact nativeNormalizationOriginalAction_ringHom A K (finiteLevelFieldAlgebra A K L E)
    (tAKC := finiteLevelFieldAlgebra_tower A K L E)
    (finiteGaloisIntermediateField_isField K L E) g

/-- The literal prime contraction supplies the ordinary contraction premise. -/
theorem finiteNormalizationActionDiagram_contraction
    (E : FiniteGaloisIntermediateField K L) (Q : Ideal (integralClosure A L)) :
    ∀ a : (finiteNormalizationActionDiagram A K L E).lowerRing.carrier,
      (finiteAbsoluteNormalizationPrime A K L Q E).carrier a ↔
        Q.carrier ((finiteNormalizationActionDiagram A K L E).ringMap.toFun a) := by
  intro a
  rfl

/-- Actual fixed-element lifting is obtained from the infinite Galois
correspondence followed by the ring-only integral preimage construction. -/
theorem finiteNormalizationActionDiagram_fixedPreimages
    (E : FiniteGaloisIntermediateField K L) :
    (finiteNormalizationActionDiagram A K L E).HasFixedPreimages := by
  unfold RingActionRestriction.HasFixedPreimages
  intro upperAction b hb
  have hbE : b.val ∈ E.toIntermediateField :=
    finiteField_mem_of_fixed K L E b.val
      (fun g hg => originalNormalization_fixed_coefficient A K L g b (hb g hg))
  exact subalgebraNormalization_preimage_of_mem
    (finiteLevelNormalizationSubalgebra A K L E) b hbE

/-- The inherited kernel action has open fixed sets, by the already proved
openness of the original normalization stabilizers and subtype continuity. -/
theorem finiteNormalizationActionDiagram_openFixedSets
    (E : FiniteGaloisIntermediateField K L) :
    (finiteNormalizationActionDiagram A K L E).HasOpenFixedSets := by
  unfold RingActionRestriction.HasOpenFixedSets
  intro upperAction kernelTopology b
  exact (integralClosure_fixedSet_isOpen_krull A K L b).preimage
    (f := fun g : E.toIntermediateField.fixingSubgroup => g.val) continuous_subtype_val

/-- The actual finite coefficient square proves diagram equivariance;
no field-extension scalar structures are opened in this proof. -/
theorem finiteNormalizationActionDiagram_equivariant
    (E : FiniteGaloisIntermediateField K L) :
    (finiteNormalizationActionDiagram A K L E).IsEquivariant := by
  unfold RingActionRestriction.IsEquivariant
  intro upperAction lowerAction g
  have hfinite := finiteNormalizationOriginalAction_ringHom A K L E
    ((finiteGaloisRestrictionGroupMap K L E).hom'.toFun g)
  have hupper := (normalizationGaloisRingHom_eq_original A K L g).symm
  exact (congrArg (fun f => (finiteAbsoluteNormalizationRingMap A K L E).comp f) hfinite).trans
    ((actualFiniteNormalizationRestrictionRingHom_inclusion A K L E g).trans
      (congrArg (fun f => f.comp (finiteAbsoluteNormalizationRingMap A K L E)) hupper.symm))

/-- Both actual decomposition and inertia images are obtained by the
ordinary ring/group theorem after all concrete suppliers are established. -/
theorem finiteNormalizationActionDiagram_images
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsPrime]
    (E : FiniteGaloisIntermediateField K L) :
    let D := finiteNormalizationActionDiagram A K L E
    (D.upperDecomposition Q).map D.groupMap =
        D.lowerDecomposition (finiteAbsoluteNormalizationPrime A K L Q E) ∧
      (D.upperInertia Q).map D.groupMap =
        D.lowerInertia (finiteAbsoluteNormalizationPrime A K L Q E) := by
  intro D
  exact RingActionRestriction.images_of_profinite D
    (finiteAbsoluteNormalizationPrime A K L Q E) Q (hq := hQ)
    (finiteGaloisFixingTopology_compact K L E)
    (finiteGaloisFixingTopology_totallyDisconnected K L E)
    (finiteGaloisFixingTopology_isTopologicalGroup K L E)
    (finiteNormalizationActionDiagram_contraction A K L E Q)
    (finiteNormalizationActionDiagram_fixedPreimages A K L E)
    (finiteNormalizationActionDiagram_openFixedSets A K L E)
    (finiteGaloisRestrictionGroupMap_surjective K L E)
    (finiteGaloisRestrictionGroupMap_fixes_kernel K L E)
    (finiteNormalizationActionDiagram_equivariant A K L E)

/-- A finite native field-inertia element has an original inertia lift
under the existing finite group restriction. The statement never opens
the finite field's scalar or field dictionaries. -/
theorem actualNormalizationInertia_exists_finiteNative_restriction
    (Q : Ideal (integralClosure A L)) [hQ : Q.IsPrime]
    (E : FiniteGaloisIntermediateField K L)
    (τ : { g : (finiteGaloisGroupObject K L E).carrier //
      ((finiteNormalizationActionDiagram A K L E).lowerInertia
        (finiteAbsoluteNormalizationPrime A K L Q E)).carrier g }) :
    ∃ σ : (actualNormalizationInertiaGroup A K L Q).carrier,
      (finiteGaloisRestrictionGroupMap K L E).hom'.toFun
          (actualNormalizationInertiaElement A K L Q σ) = τ.val := by
  have hmap := (finiteNormalizationActionDiagram_images A K L Q E (hQ := hQ)).2
  have hτ : (((finiteNormalizationActionDiagram A K L E).upperInertia Q).map
      (finiteNormalizationActionDiagram A K L E).groupMap).carrier τ.val := by
    rw [hmap]
    exact τ.property
  obtain ⟨g, hg, hrestrict⟩ := hτ
  exact ⟨⟨g, hg⟩, hrestrict⟩

end ActualData

end EtaleFundamentalGroups.Inertia
