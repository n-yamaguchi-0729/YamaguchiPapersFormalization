/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NativeSeparableRoots
import ProCGroups.InverseSystems.CofinalGroups

/-!
# Separable roots compared with a cofinal set of actual degrees

The two constructed equivalences are composed only after the coefficient
field and cofinal restriction owners have proved their own coordinate laws.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory ProCGroups.InverseSystems

universe u v

variable (k : Type u) [Field k] (E : Bundled Field.{v})
  (T : Set (InvertibleExponent k))

/-- The native group of the literal restricted roots system, with its existing operations. -/
def nativeRestrictedRootsGroup : GrpCat.{v} :=
  GrpCat.of ((primeToRootsSystem k E.α).restrict T).inverseLimit

instance nativeRestrictedRootsGroup_topology :
    TopologicalSpace (nativeRestrictedRootsGroup k E T).carrier :=
  inferInstanceAs (TopologicalSpace ((primeToRootsSystem k E.α).restrict T).inverseLimit)

/-- The retained scalar coordinate, closing the restricted stage owner. -/
def nativeRestrictedRootsScalar (t : T)
    (x : (nativeRestrictedRootsGroup k E T).carrier) : E.α :=
  (((primeToRootsSystem k E.α).restrict T).projection t x).val.val

variable
  (hT : ∀ n : InvertibleExponent k, ∃ t : T, n ≤ t.val)

/-- The native full roots group restricts to the original cofinal subsystem. -/
def nativeFullRootsRestrictionEquiv :
    (nativeFullRootsGroup k E).carrier ≃ₜ*
      (nativeRestrictedRootsGroup k E T).carrier :=
  (primeToRootsSystem k E.α).continuousMulEquiv_restrict_cofinal T
    (InvertibleExponent.directed k) hT

/-- The native cofinal equivalence is the original retained-coordinate map. -/
theorem nativeFullRootsRestrictionEquiv_scalar
    (t : T) (x : (nativeFullRootsGroup k E).carrier) :
    nativeRestrictedRootsScalar k E T t
      ((nativeFullRootsRestrictionEquiv k E T hT).toFun x) =
      nativeFullRootsScalar k E t.val x := by
  exact congrArg (fun z : rootsOfUnity t.val.val E.α => z.val.val)
    ((primeToRootsSystem k E.α).projection_continuousMulEquiv_restrict_cofinal T
      (InvertibleExponent.directed k) hT t x)

variable (a : Algebra k E.α)

/-- The actual root inclusion followed by the proved cofinal restriction. -/
def nativeSeparableRootsRestrictionEquiv :
    (nativeSeparableRootsGroup k E a).carrier ≃ₜ*
      (nativeRestrictedRootsGroup k E T).carrier :=
  (nativeSeparableRootsInclusionEquiv k E a).trans
    (nativeFullRootsRestrictionEquiv k E T hT)

/-- Every retained scalar is inclusion of the same separable-root coordinate. -/
theorem nativeSeparableRootsRestrictionEquiv_scalar
    (t : T) (x : (nativeSeparableRootsGroup k E a).carrier) :
    nativeRestrictedRootsScalar k E T t
      ((nativeSeparableRootsRestrictionEquiv k E T hT a).toFun x) =
      nativeSeparableRootsScalar k E a t.val x := by
  exact (nativeFullRootsRestrictionEquiv_scalar k E T hT t
    ((nativeSeparableRootsInclusionEquiv k E a).toFun x)).trans
      (nativeSeparableRootsInclusionEquiv_scalar k E a t.val x)

end EtaleFundamentalGroups.Inertia

end
