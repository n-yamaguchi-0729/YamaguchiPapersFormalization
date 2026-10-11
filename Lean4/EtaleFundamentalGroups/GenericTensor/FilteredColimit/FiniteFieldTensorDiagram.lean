/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Valuation.Completion.FiniteSubfieldTensor
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Constant extensions as colimits with their native tensor actions

Finite intermediate fields index the actual algebras `R ⊗[k] F`.
Their inclusions form a filtered diagram with colimit `R ⊗[k] L` for an
algebraic extension `L/k`. We use the existing finite-coefficient tensor lift
and flat tensor injectivity, retaining the native tensor actions at each point.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace EtaleFundamentalGroups

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- The actual finite intermediate fields, ordered by inclusion. -/
abbrev FiniteIntermediateFieldIndex :=
  { F : IntermediateField k L // FiniteDimensional k F }

instance finiteIntermediateFieldIndexNonempty : Nonempty (FiniteIntermediateFieldIndex k L) :=
  ⟨⟨⊥, inferInstance⟩⟩

instance finiteIntermediateFieldIndexDirected :
    IsDirectedOrder (FiniteIntermediateFieldIndex k L) where
  directed F E := by
    let : FiniteDimensional k F.val := F.property
    let : FiniteDimensional k E.val := E.property
    have hF : F.val ≤ F.val ⊔ E.val := le_sup_left
    have hE : E.val ≤ F.val ⊔ E.val := le_sup_right
    exact ⟨⟨F.val ⊔ E.val, inferInstance⟩, hF, hE⟩

variable (R : Type u) [CommRing R] [Algebra k R]

/-- A filtered diagram using the native tensor product at every finite field. -/
def finiteIntermediateFieldTensorDiagram :
    FiniteIntermediateFieldIndex k L ⥤ Under (CommRingCat.of R) where
  obj F := CommRingCat.mkUnder (CommRingCat.of R) (R ⊗[k] F.val.toSubalgebra)
  map {F E} f := (Algebra.TensorProduct.map (AlgHom.id R R)
    (Subalgebra.inclusion
      (show F.val.toSubalgebra ≤ E.val.toSubalgebra from f.le))).toUnder
  map_id F := by
    with_reducible_and_instances
      change AlgHom.toUnder (R := CommRingCat.of R)
        (Algebra.TensorProduct.map (AlgHom.id R R)
          (Subalgebra.inclusion (le_refl F.val.toSubalgebra))) = 𝟙 _
      rw [Subalgebra.inclusion_self, Algebra.TensorProduct.map_id]
      ext z
      simp only [AlgHom.toUnder_right, AlgHom.id_apply, Under.id_right, CommRingCat.id_apply]
  map_comp {F E G} f g := by
    have hi : (Subalgebra.inclusion
        (show E.val.toSubalgebra ≤ G.val.toSubalgebra from g.le)).comp
        (Subalgebra.inclusion
          (show F.val.toSubalgebra ≤ E.val.toSubalgebra from f.le)) =
        Subalgebra.inclusion
          (show F.val.toSubalgebra ≤ G.val.toSubalgebra from (f ≫ g).le) := by
      ext x
      rfl
    with_reducible_and_instances
      simp only [← AlgHom.toUnder_comp, ← Algebra.TensorProduct.map_id_comp, hi]

/-- The literal tensor maps of the finite-field inclusions into `L`. -/
def finiteIntermediateFieldTensorCocone :
    Cocone (finiteIntermediateFieldTensorDiagram k L R) where
  pt := CommRingCat.mkUnder (CommRingCat.of R) (R ⊗[k] L)
  ι.app F := (Algebra.TensorProduct.map (AlgHom.id R R) F.val.toSubalgebra.val).toUnder
  ι.naturality F E f := by
    have hi : E.val.toSubalgebra.val.comp
        (Subalgebra.inclusion
          (show F.val.toSubalgebra ≤ E.val.toSubalgebra from f.le)) = F.val.toSubalgebra.val := by
      ext x
      rfl
    with_reducible_and_instances
      simp only [finiteIntermediateFieldTensorDiagram, ← AlgHom.toUnder_comp,
        ← Algebra.TensorProduct.map_id_comp, hi, CategoryTheory.Functor.const_obj_map]
      ext z
      rfl

/-- Finite-coefficient lifts give joint surjectivity; flatness detects equality
at each actual finite-field tensor stage. -/
def finiteIntermediateFieldTensorCoconeIsColimit [Algebra.IsAlgebraic k L] :
    IsColimit (finiteIntermediateFieldTensorCocone k L R) := by
  letI : IsConnected (FiniteIntermediateFieldIndex k L) := IsFiltered.isConnected _
  apply isColimitOfReflects (Under.forget (CommRingCat.of R))
  letI : ReflectsColimit
      (finiteIntermediateFieldTensorDiagram k L R ⋙ Under.forget (CommRingCat.of R))
      (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommRingCat.{u})
  apply Types.FilteredColimit.isColimitOf'
  · intro z
    obtain ⟨F, hF, w, hw⟩ :=
      ValuationTheory.Completion.exists_finiteSubfield_tensor_lift z
    exact ⟨⟨F, hF⟩, w, hw.symm⟩
  · intro F x y hxy
    have hinj : Function.Injective
        (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val.toSubalgebra.val) :=
      TensorProduct.map_injective_of_flat_flat
        (AlgHom.id k R).toLinearMap F.val.toSubalgebra.val.toLinearMap
        Function.injective_id Subtype.val_injective
    refine ⟨F, 𝟙 F, ?_⟩
    apply congrArg
    exact hinj hxy

end EtaleFundamentalGroups

end
