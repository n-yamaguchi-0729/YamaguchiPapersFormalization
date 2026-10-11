/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Kernels of three native group morphisms

The categorical composition and its native group dictionaries are closed
in this group-only owner before concrete field and normalization data enter.
-/

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory

universe u

/-- Pull back a proved middle kernel through the first map, after cancelling
an injective final map in the SAME categorical composite. -/
theorem grpCat_comp_comp_ker_of_injective
    (G H M N : GrpCat.{u}) (f : G ⟶ H) (g : H ⟶ M) (e : M ⟶ N)
    (he : Function.Injective e.hom'.toFun)
    (P : Subgroup H.carrier) (hP : g.hom'.ker = P) :
    (f ≫ g ≫ e).hom'.ker = P.comap f.hom' := by
  have hcancel : (f ≫ g ≫ e).hom'.ker = (g.hom'.comp f.hom').ker :=
    MonoidHom.ker_comp_of_injective (g.hom'.comp f.hom') e.hom' he
  have hpullback : (g.hom'.comp f.hom').ker = g.hom'.ker.comap f.hom' :=
    (MonoidHom.comap_ker g.hom' f.hom').symm
  exact hcancel.trans (hpullback.trans
    (congrArg (fun U : Subgroup H.carrier => U.comap f.hom') hP))

end EtaleFundamentalGroups.Inertia
