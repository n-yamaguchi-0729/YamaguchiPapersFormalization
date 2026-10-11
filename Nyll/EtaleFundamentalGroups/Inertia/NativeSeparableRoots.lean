/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NativeSeparableResidueGroup
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsSeparableCoordinates
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsResidueAction

/-!
# Full roots limits of the stored residue fields

These group objects store exactly the existing compatible-family limits.
The stored coefficient algebra is installed in this field-only owner,
before any original fraction field or tame-degree subset is introduced.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory

universe u v

variable (k : Type u) [Field k] (E : Bundled Field.{v})

/-- The full roots limit over the stored field, with its existing group. -/
def nativeFullRootsGroup : GrpCat.{v} :=
  GrpCat.of (primeToRootsSystem k E.α).inverseLimit

instance nativeFullRootsGroup_topology :
    TopologicalSpace (nativeFullRootsGroup k E).carrier :=
  inferInstanceAs (TopologicalSpace (primeToRootsSystem k E.α).inverseLimit)

/-- A coordinate of the full roots group as a literal field element. -/
def nativeFullRootsScalar (n : InvertibleExponent k)
    (x : (nativeFullRootsGroup k E).carrier) : E.α :=
  ((primeToRootsSystem k E.α).projection n x).val.val

variable (a : Algebra k E.α)

/-- The full roots limit of the relative separable closure under the stored action. -/
def nativeSeparableRootsGroup : GrpCat.{v} :=
  nativeFullRootsGroup k (nativeSeparableResidueField k E a)

instance nativeSeparableRootsGroup_topology :
    TopologicalSpace (nativeSeparableRootsGroup k E a).carrier :=
  nativeFullRootsGroup_topology k (nativeSeparableResidueField k E a)

/-- The actual separable coefficient at one full exponent. -/
def nativeSeparableRootsCoordinate (n : InvertibleExponent k)
    (x : (nativeSeparableRootsGroup k E a).carrier) :
    (nativeSeparableResidueField k E a).α :=
  nativeFullRootsScalar k (nativeSeparableResidueField k E a) n x

/-- The same coordinate viewed in the stored larger residue field. -/
def nativeSeparableRootsScalar (n : InvertibleExponent k)
    (x : (nativeSeparableRootsGroup k E a).carrier) : E.α := by
  exact nativeSeparableResidueScalar k E a (nativeSeparableRootsCoordinate k E a n x)

/-- Literal scalar coordinates separate points of the full separable roots limit. -/
theorem nativeSeparableRootsScalar_ext
    (x y : (nativeSeparableRootsGroup k E a).carrier)
    (h : ∀ n : InvertibleExponent k,
      nativeSeparableRootsScalar k E a n x = nativeSeparableRootsScalar k E a n y) :
    x = y := by
  apply (primeToRootsSystem k (nativeSeparableResidueField k E a).α).ext
  intro n
  apply rootsOfUnity.coe_injective
  exact Subtype.ext (h n)

/-- Root inclusion identifies the full roots groups of the two stored fields. -/
def nativeSeparableRootsInclusionEquiv :
    (nativeSeparableRootsGroup k E a).carrier ≃ₜ*
      (nativeFullRootsGroup k E).carrier := by
  let := a
  exact primeToRootsSeparableClosureLimitEquiv k E.α

/-- The native comparison is the literal inclusion on every scalar coordinate. -/
theorem nativeSeparableRootsInclusionEquiv_scalar
    (n : InvertibleExponent k) (x : (nativeSeparableRootsGroup k E a).carrier) :
    nativeFullRootsScalar k E n ((nativeSeparableRootsInclusionEquiv k E a).toFun x) =
      nativeSeparableRootsScalar k E a n x := by
  let := a
  exact primeToRootsSeparableClosureLimitEquiv_scalar k E.α n x

/-- The existing separable residue automorphisms act on every full root coordinate. -/
def nativeSeparableRootsAction :
    (nativeSeparableResidueGroup k E a).carrier →*
      Equiv.Perm (nativeSeparableRootsGroup k E a).carrier := by
  let := a
  exact
    { toFun := fun σ =>
        (primeToRootsResidueAction k (separableClosure k E.α)).toFun σ.toRingEquiv
      map_one' := (primeToRootsResidueAction k (separableClosure k E.α)).map_one
      map_mul' := fun σ τ =>
        (primeToRootsResidueAction k (separableClosure k E.α)).map_mul
          σ.toRingEquiv τ.toRingEquiv }

/-- Plain application of the coefficient action on the full separable roots limit. -/
def nativeSeparableRootsAction_apply
    (σ : (nativeSeparableResidueGroup k E a).carrier)
    (x : (nativeSeparableRootsGroup k E a).carrier) :
    (nativeSeparableRootsGroup k E a).carrier :=
  ((nativeSeparableRootsAction k E a).toFun σ).toFun x

/-- A root-action coordinate is the stored separable residue action on that coefficient. -/
theorem nativeSeparableRootsAction_scalar
    (σ : (nativeSeparableResidueGroup k E a).carrier)
    (n : InvertibleExponent k) (x : (nativeSeparableRootsGroup k E a).carrier) :
    nativeSeparableRootsScalar k E a n (nativeSeparableRootsAction_apply k E a σ x) =
      nativeSeparableResidueActionScalar k E a σ
        (nativeSeparableRootsCoordinate k E a n x) := rfl

end EtaleFundamentalGroups.Inertia

end
