/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729

Uses Mathlib's Algebra/Category/Ring/Constructions.lean, Copyright (c) 2021
Andrew Yang; RingTheory/TensorProduct/Basic.lean, Copyright (c) 2020
Kim Morrison, authors Kim Morrison and Johan Commelin; and
CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean, Copyright (c) 2022
Kim Morrison, authors Kim Morrison, Joël Riou, and Calle Sönne.
All are released under Apache 2.0.
-/

import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Native ring models for tensor-product pushouts
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace EtaleFundamentalGroups.CategoricalTensor

variable (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B]

/-- The literal model coprojection, retained as a RingHom before entering
the Under categories. Only this construction exposes its R-AlgHom owner. -/
def nativeModelInclusion : B →+* S ⊗[R] B :=
  (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom

/-- The concrete tensor/pushout Iso in CommRingCat, with the model leg first.
Its public interface has no coefficient-algebra structure on the tensor. -/
def nativeTensorPushoutIso : CommRingCat.of (S ⊗[R] B) ≅
    pushout (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap R S)) :=
  (CommRingCat.isPushout_tensorProduct R S B).flip.isoPushout

/-- The native Iso carries the categorical model coprojection to the literal
right tensor inclusion. This is the actual tensor pushout universal property. -/
lemma nativeModelInclusion_eq_pushout_inl :
    CommRingCat.ofHom (nativeModelInclusion R S B) =
      pushout.inl (CommRingCat.ofHom (algebraMap R B))
        (CommRingCat.ofHom (algebraMap R S)) ≫
          (nativeTensorPushoutIso R S B).inv :=
  (CommRingCat.isPushout_tensorProduct R S B).flip.inl_isoPushout_inv.symm

end EtaleFundamentalGroups.CategoricalTensor

end
