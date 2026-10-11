/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NativeSeparableRootsRestriction
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationAbsoluteResidueGroup

/-!
# The full separable roots target of the original normalization

The residue field, its algebra, and the relative separable closure are
constructed once in the existing field owner. This layer contains no
fraction-field or original decomposition-group data.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory SchemeTheory ProCGroups.InverseSystems

universe u w

variable (A : Type u) (Ω : Type w) [CommRing A] [IsLocalRing A]
  [CommRing Ω] [Algebra A Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]

/-- The full invertible-exponent roots limit in the actual relative separable closure. -/
def normalizationSeparableRootsGroup : GrpCat.{w} :=
  nativeSeparableRootsGroup (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)

instance normalizationSeparableRootsGroup_topology :
    TopologicalSpace (normalizationSeparableRootsGroup A Ω Q).carrier :=
  nativeSeparableRootsGroup_topology (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)

/-- A full separable-root coordinate viewed in the literal normalization quotient. -/
def normalizationSeparableRootsScalar
    (n : InvertibleExponent (IsLocalRing.ResidueField A))
    (x : (normalizationSeparableRootsGroup A Ω Q).carrier) :
    (normalizationCommAlgCat A Ω).carrier ⧸ Q :=
  nativeSeparableRootsScalar (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q) n x

/-- The same separable residue group acts through its actual coefficient action. -/
def normalizationSeparableRootsAction :
    (normalizationResidueSeparableGroup A Ω Q).carrier →*
      Equiv.Perm (normalizationSeparableRootsGroup A Ω Q).carrier :=
  nativeSeparableRootsAction (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)

/-- Plain application closes the action's permutation data in this owner. -/
def normalizationSeparableRootsAction_apply
    (σ : (normalizationResidueSeparableGroup A Ω Q).carrier)
    (x : (normalizationSeparableRootsGroup A Ω Q).carrier) :
    (normalizationSeparableRootsGroup A Ω Q).carrier :=
  ((normalizationSeparableRootsAction A Ω Q).toFun σ).toFun x

/-- Comparison with any cofinal subsystem of the literal quotient roots. -/
def normalizationSeparableRootsRestrictionEquiv
    (T : Set (InvertibleExponent (IsLocalRing.ResidueField A)))
    (hT : ∀ n : InvertibleExponent (IsLocalRing.ResidueField A),
      ∃ t : T, n ≤ t.val) :
    (normalizationSeparableRootsGroup A Ω Q).carrier ≃ₜ*
      (nativeRestrictedRootsGroup (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A Ω Q) T).carrier :=
  nativeSeparableRootsRestrictionEquiv (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) T hT (normalizationResidueFieldAlgebra A Ω Q)

/-- The comparison is specified by the actual inclusion on retained scalar coordinates. -/
theorem normalizationSeparableRootsRestrictionEquiv_scalar
    (T : Set (InvertibleExponent (IsLocalRing.ResidueField A)))
    (hT : ∀ n : InvertibleExponent (IsLocalRing.ResidueField A),
      ∃ t : T, n ≤ t.val) (t : T)
    (x : (normalizationSeparableRootsGroup A Ω Q).carrier) :
    nativeRestrictedRootsScalar (IsLocalRing.ResidueField A)
      (normalizationResidueFieldObject A Ω Q) T t
        ((normalizationSeparableRootsRestrictionEquiv A Ω Q T hT).toFun x) =
      normalizationSeparableRootsScalar A Ω Q t.val x :=
  nativeSeparableRootsRestrictionEquiv_scalar (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) T hT (normalizationResidueFieldAlgebra A Ω Q) t x

/-- The literal forward comparison, with group and topology dictionaries closed in this owner. -/
def normalizationSeparableRootsRestrictionMap
    (T : Set (InvertibleExponent (IsLocalRing.ResidueField A)))
    (hT : ∀ n : InvertibleExponent (IsLocalRing.ResidueField A),
      ∃ t : T, n ≤ t.val) :
    (normalizationSeparableRootsGroup A Ω Q).carrier →
      (nativeRestrictedRootsGroup (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A Ω Q) T).carrier :=
  (normalizationSeparableRootsRestrictionEquiv A Ω Q T hT).toFun

/-- Scalar computation for the plain forward map requires no topology at the consumer. -/
theorem normalizationSeparableRootsRestrictionMap_scalar
    (T : Set (InvertibleExponent (IsLocalRing.ResidueField A)))
    (hT : ∀ n : InvertibleExponent (IsLocalRing.ResidueField A),
      ∃ t : T, n ≤ t.val) (t : T)
    (x : (normalizationSeparableRootsGroup A Ω Q).carrier) :
    nativeRestrictedRootsScalar (IsLocalRing.ResidueField A)
      (normalizationResidueFieldObject A Ω Q) T t
        (normalizationSeparableRootsRestrictionMap A Ω Q T hT x) =
      normalizationSeparableRootsScalar A Ω Q t.val x :=
  normalizationSeparableRootsRestrictionEquiv_scalar A Ω Q T hT t x

/-- The actual comparison's homeomorphism, before the original degree data is supplied. -/
def normalizationSeparableRootsRestrictionHomeomorph
    (T : Set (InvertibleExponent (IsLocalRing.ResidueField A)))
    (hT : ∀ n : InvertibleExponent (IsLocalRing.ResidueField A),
      ∃ t : T, n ≤ t.val) :
    (normalizationSeparableRootsGroup A Ω Q).carrier ≃ₜ
      (nativeRestrictedRootsGroup (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A Ω Q) T).carrier :=
  (normalizationSeparableRootsRestrictionEquiv A Ω Q T hT).toHomeomorph

/-- The homeomorphism and plain compatible-family comparison share the exact forward function. -/
theorem normalizationSeparableRootsRestrictionHomeomorph_toFun
    (T : Set (InvertibleExponent (IsLocalRing.ResidueField A)))
    (hT : ∀ n : InvertibleExponent (IsLocalRing.ResidueField A),
      ∃ t : T, n ≤ t.val) :
    (normalizationSeparableRootsRestrictionHomeomorph A Ω Q T hT).toFun =
      normalizationSeparableRootsRestrictionMap A Ω Q T hT := rfl

/-- The actual comparison's multiplicative equivalence, independently of its topology. -/
def normalizationSeparableRootsRestrictionMulEquiv
    (T : Set (InvertibleExponent (IsLocalRing.ResidueField A)))
    (hT : ∀ n : InvertibleExponent (IsLocalRing.ResidueField A),
      ∃ t : T, n ≤ t.val) :
    (normalizationSeparableRootsGroup A Ω Q).carrier ≃*
      (nativeRestrictedRootsGroup (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A Ω Q) T).carrier :=
  (normalizationSeparableRootsRestrictionEquiv A Ω Q T hT).toMulEquiv

/-- The topology-only comparison still retains precisely the same included scalar. -/
theorem normalizationSeparableRootsRestrictionHomeomorph_scalar
    (T : Set (InvertibleExponent (IsLocalRing.ResidueField A)))
    (hT : ∀ n : InvertibleExponent (IsLocalRing.ResidueField A),
      ∃ t : T, n ≤ t.val) (t : T)
    (x : (normalizationSeparableRootsGroup A Ω Q).carrier) :
    nativeRestrictedRootsScalar (IsLocalRing.ResidueField A)
      (normalizationResidueFieldObject A Ω Q) T t
        ((normalizationSeparableRootsRestrictionHomeomorph A Ω Q T hT).toFun x) =
      normalizationSeparableRootsScalar A Ω Q t.val x :=
  normalizationSeparableRootsRestrictionEquiv_scalar A Ω Q T hT t x

end EtaleFundamentalGroups.Inertia

end
