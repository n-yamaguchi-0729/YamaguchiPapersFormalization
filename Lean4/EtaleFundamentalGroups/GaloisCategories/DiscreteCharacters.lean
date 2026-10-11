/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient
import EtaleFundamentalGroups.GaloisCovers.OpenNormalUniverse
import ProCGroups.ProC.OpenNormalSubgroups.Basic

/-!
# Galois objects representing discrete characters

A continuous character of the fundamental group with discrete target factors
through a pointed Galois object. The induced homomorphism from the opposite
deck group is injective: the object is constructed from the actual kernel of
the character, so its deck group identifies with the character's image.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe u v w z

/-- A continuous homomorphism with discrete target is represented by a pointed
Galois object and an embedding of its opposite deck group into the target. -/
theorem exists_galoisObject_discreteCharacter_embedding
    {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    {A : Type z} [Group A] [TopologicalSpace A] [DiscreteTopology A]
    (χ : Aut F →ₜ* A) :
    ∃ (W : C) (hW : IsGalois W) (w : F.obj W),
      letI : IsGalois W := hW
      ∃ e : (Aut W)ᵐᵒᵖ →* A,
        Function.Injective e ∧
          e.comp (galoisObjectQuotientMonoidHom F (Aut F) W w) = χ.toMonoidHom := by
  obtain ⟨W, hW, w, hw⟩ :=
    exists_galois_object_point_stabilizer_eq_any_universe F
      (ProCGroups.ProC.OpenNormalSubgroup.ker χ)
  let : IsGalois W := hW
  let q : Aut F →* (Aut W)ᵐᵒᵖ := galoisObjectQuotientMonoidHom F (Aut F) W w
  have hq : Function.Surjective q :=
    galoisObjectQuotientMonoidHom_surjective F (Aut F) W w
  have hker : q.ker = χ.toMonoidHom.ker :=
    (galoisObjectQuotientMonoidHom_ker F (Aut F) W w).trans hw
  let e : (Aut W)ᵐᵒᵖ →* A :=
    q.liftOfSurjective hq ⟨χ.toMonoidHom, hker.le⟩
  have he : e.comp q = χ.toMonoidHom :=
    congrArg Subtype.val
      ((q.liftOfSurjective hq).symm_apply_apply ⟨χ.toMonoidHom, hker.le⟩)
  refine ⟨W, hW, w, e, ?_, he⟩
  apply (injective_iff_map_eq_one e).mpr
  intro a ha
  obtain ⟨g, rfl⟩ := hq a
  have hg : g ∈ χ.toMonoidHom.ker := by
    change χ g = 1
    exact (DFunLike.congr_fun he g).symm.trans ha
  rw [← hker] at hg
  exact hg

end CategoryTheory.PreGaloisCategory
