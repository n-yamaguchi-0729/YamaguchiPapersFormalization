/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import EtaleFundamentalGroups.GaloisCategories.Functoriality

/-!
# Isomorphic finite fiber functors

A natural isomorphism of finite-set-valued functors induces an isomorphism
of their topological automorphism groups. For fiber functors, the associated
finite continuous-action functors agree after restriction along this
isomorphism. Changing the natural isomorphism changes the group isomorphism
by inner conjugation.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] {F G : C ⥤ FintypeCat.{w}}

/-- A natural isomorphism induces a topological isomorphism of automorphism groups. -/
def continuousConjAut (t : F ≅ G) : Aut F ≃ₜ* Aut G where
  toMulEquiv := t.conjAut
  continuous_toFun := continuous_conjAut t
  continuous_invFun :=
    Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := t.conjAut.toEquiv) (continuous_conjAut t)

/-- Changing the natural isomorphism changes the group isomorphism by conjugation. -/
theorem continuousConjAut_eq_conj (t₁ t₂ : F ≅ G) (a : Aut F) :
    continuousConjAut t₂ a =
      MulAut.conj (G := Aut G) (t₁.symm ≪≫ t₂) (continuousConjAut t₁ a) := by
  have ht : t₁ ≪≫ (t₁.symm ≪≫ t₂) = t₂ := by
    rw [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  have hconj : t₂.conjAut a = (t₁.symm ≪≫ t₂).conjAut (t₁.conjAut a) :=
    (congrArg (fun t : F ≅ G ↦ t.conjAut a) ht.symm).trans
      (Iso.trans_conjAut t₁ (t₁.symm ≪≫ t₂) a)
  have hinner (b c : Aut G) : b.conjAut c = MulAut.conj (G := Aut G) b c := by
    apply Aut.ext
    rfl
  exact hconj.trans (hinner (t₁.symm ≪≫ t₂) (t₁.conjAut a))

variable [GaloisCategory C] [FiberFunctor F] [FiberFunctor G]

/-- The finite-action equivalences of isomorphic fiber functors are compatible
with restriction along the resulting topological group isomorphism. -/
def functorToContActionFiberIso (t : F ≅ G) :
    functorToContAction F ≅ functorToContAction G ⋙
      (ContAction.resEquiv FintypeCat (continuousConjAut t)).functor :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _
      (Action.mkIso (t.app X) (fun a ↦ by
        change a.hom.app X ≫ t.hom.app X =
          t.hom.app X ≫ (t.conjAut a).hom.app X
        simp only [Iso.conjAut_hom, Iso.conj_apply, NatTrans.comp_app]
        simp only [← Category.assoc, t.hom_inv_id_app, Category.id_comp])))
    (fun {X Y} f ↦ by
      ext : 2
      exact t.hom.naturality f)

end CategoryTheory.PreGaloisCategory
