/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Induced subgroup restriction from a proved image equality

The map is the literal ambient homomorphism on subgroup elements. A proved
image equality supplies membership and every target element's actual lift.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- The literal restriction to subgroups whose image equality is proved. -/
def subgroupRestrictionOfImage
    {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (P : Subgroup G) (Q : Subgroup H) (h : P.map f = Q) : P →* Q :=
  (MulEquiv.subgroupCongr h).toMonoidHom.comp (f.subgroupMap P)

/-- The induced homomorphism is the same ambient homomorphism on values. -/
theorem subgroupRestrictionOfImage_val
    {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (P : Subgroup G) (Q : Subgroup H) (h : P.map f = Q) (x : P) :
    ((subgroupRestrictionOfImage f P Q h).toFun x).val = f.toFun x.val :=
  MulEquiv.subgroupCongr_apply h ((f.subgroupMap P).toFun x)

/-- The proved image equality supplies surjectivity of this same restriction. -/
theorem subgroupRestrictionOfImage_surjective
    {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (P : Subgroup G) (Q : Subgroup H) (h : P.map f = Q) :
    Function.Surjective (subgroupRestrictionOfImage f P Q h).toFun :=
  (MulEquiv.subgroupCongr h).surjective.comp (f.subgroupMap_surjective P)

end EtaleFundamentalGroups.Inertia
