/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCategories.FundamentalGroup
import Mathlib.CategoryTheory.Galois.GaloisObjects
import Mathlib.CategoryTheory.Galois.Decomposition

/-!
# Finite quotients represented by Galois objects

A pointed Galois object identifies its fiber with its categorical
automorphism group.  Since categorical automorphisms act on the right of the
fiber while the fundamental group acts on the left, the resulting quotient
has target the opposite automorphism group.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe u₁ u₂ w v

variable {C : Type u₁} [Category.{u₂} C]
variable (F : CategoryTheory.Functor C FintypeCat.{w})
  [GaloisCategory C] [FiberFunctor F]
variable (G : Type v) [Group G]
variable [∀ X, MulAction G (F.obj X)] [hNatural : IsNaturalSMul F G]

/-- The quotient represented by a pointed Galois object.  The opposite on
the target records the contravariance of categorical automorphism
multiplication relative to the left fundamental-group action. -/
noncomputable def galoisObjectQuotientMonoidHom
    (A : C) [IsGalois A] (a : F.obj A) : G →* (Aut A)ᵐᵒᵖ := by
  let e := evaluationEquivOfIsGalois F A a
  refine
    { toFun := fun g ↦ MulOpposite.op (e.symm (g • a))
      map_one' := ?_
      map_mul' := ?_ }
  · apply MulOpposite.unop_injective
    apply e.injective
    simp [e]
  · intro g h
    apply MulOpposite.unop_injective
    apply e.injective
    calc
      F.map ((e.symm ((g * h) • a)).hom) a =
          (g * h) • a :=
        evaluationEquivOfIsGalois_symm_fiber F A a ((g * h) • a)
      _ = g • (h • a) := mul_smul g h a
      _ = g • F.map ((e.symm (h • a)).hom) a := by
        rw [evaluationEquivOfIsGalois_symm_fiber]
      _ = F.map ((e.symm (h • a)).hom) (g • a) :=
        (IsNaturalSMul.naturality g (e.symm (h • a)).hom a).symm
      _ = F.map ((e.symm (g • a)).hom ≫
          (e.symm (h • a)).hom) a := by
        rw [F.map_comp, FintypeCat.comp_apply,
          evaluationEquivOfIsGalois_symm_fiber]
      _ = F.map ((e.symm (h • a) * e.symm (g • a)).hom) a := rfl

include hNatural in
@[simp]
theorem galoisObjectQuotientMonoidHom_unop_apply
    (A : C) [IsGalois A] (a : F.obj A) (g : G) :
    (galoisObjectQuotientMonoidHom F G A a g).unop =
      (evaluationEquivOfIsGalois F A a).symm (g • a) :=
  rfl

include hNatural in
/-- Evaluating the cover automorphism selected by the quotient recovers the
fundamental-group action on the chosen point. -/
@[simp]
theorem galoisObjectQuotientMonoidHom_evaluation
    (A : C) [IsGalois A] (a : F.obj A) (g : G) :
    F.map ((galoisObjectQuotientMonoidHom F G A a g).unop.hom) a = g • a := by
  exact evaluationEquivOfIsGalois_symm_fiber F A a (g • a)

/-- The kernel of the finite quotient represented by a pointed Galois object
is exactly the stabilizer of the chosen fiber point. -/
theorem galoisObjectQuotientMonoidHom_ker
    (A : C) [IsGalois A] (a : F.obj A) :
    (galoisObjectQuotientMonoidHom F G A a).ker =
      MulAction.stabilizer G a := by
  ext g
  rw [MonoidHom.mem_ker, MulAction.mem_stabilizer_iff]
  constructor
  · intro hg
    have h := galoisObjectQuotientMonoidHom_evaluation F G A a g
    rw [hg] at h
    simpa using h.symm
  · intro hg
    apply MulOpposite.unop_injective
    apply (evaluationEquivOfIsGalois F A a).injective
    rw [galoisObjectQuotientMonoidHom_unop_apply, hg]
    simp

/-- A transitive fundamental-group action makes the quotient represented by
a Galois object surjective. -/
theorem galoisObjectQuotientMonoidHom_surjective
    (A : C) [IsGalois A] (a : F.obj A)
    [MulAction.IsPretransitive G (F.obj A)] :
    Function.Surjective (galoisObjectQuotientMonoidHom F G A a) := by
  intro sigma
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G
    a (F.map sigma.unop.hom a)
  refine ⟨g, ?_⟩
  apply MulOpposite.unop_injective
  apply (evaluationEquivOfIsGalois F A a).injective
  rw [galoisObjectQuotientMonoidHom_unop_apply, hg]
  exact (evaluationEquivOfIsGalois F A a).apply_symm_apply _

/-- Pointed finite Galois quotients separate the automorphisms of a fiber
functor. A natural automorphism fixing the fiber of every Galois object fixes
every fiber, since every fiber point is the image of a pointed Galois object. -/
theorem iInf_galoisObjectQuotientMonoidHom_ker :
    (⨅ (A : C) (hA : IsGalois A) (a : F.obj A),
      (letI : IsGalois A := hA
       galoisObjectQuotientMonoidHom F (Aut F) A a).ker) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro g hg
  rw [Subgroup.mem_bot]
  apply Iso.ext
  apply natTrans_ext_of_isGalois F
  intro A hA
  apply FintypeCat.hom_ext
  intro a
  have hfix := (Subgroup.mem_iInf.mp
    (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hg A) hA) a)
  rw [galoisObjectQuotientMonoidHom_ker,
    MulAction.mem_stabilizer_iff] at hfix
  change g • a = a
  exact hfix

end CategoryTheory.PreGaloisCategory
