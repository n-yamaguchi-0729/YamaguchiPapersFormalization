/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.ModuleSetComparison
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Constant module sheaves from constant underlying set sheaves

For a functor preserving sheafification and reflecting isomorphisms, the
constant-sheaf counit is an isomorphism whenever its image sheaf is constant
and the target constant-sheaf functor is fully faithful. The source constant
functor need not be fully faithful: the actual counit comparison already
supplies the required isomorphism.

Applied to étale module sheaves, this constructs the constant module model
from sections over a terminal object. The ring and the scheme are arbitrary;
full faithfulness of the constant set-sheaf functor is an explicit input.
The proof uses Mathlib's `constantSheafAdj_counit_w` and the affine étale site
to supply preservation of sheafification by the module forgetful functor.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology.Sites

/-- The actual constant-sheaf counit is invertible if the forgotten sheaf is
constant and only the target constant-sheaf functor is fully faithful. -/
lemma constantCounit_isIso_of_forget
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {D : Type*} [Category* D] {B : Type*} [Category* B]
    [HasWeakSheafify J D] [HasWeakSheafify J B]
    (U : D ⥤ B) [J.PreservesSheafification U] [J.HasSheafCompose U]
    [U.ReflectsIsomorphisms]
    [(constantSheaf J B).Faithful] [(constantSheaf J B).Full]
    (F : Sheaf J D) [Sheaf.IsConstant J ((sheafCompose J U).obj F)]
    {T : C} (hT : IsTerminal T) :
    IsIso ((constantSheafAdj J D hT).counit.app F) := by
  have hc : IsIso ((constantSheafAdj J B hT).counit.app ((sheafCompose J U).obj F)) :=
    (Sheaf.isConstant_iff_isIso_counit_app J ((sheafCompose J U).obj F) hT).mp inferInstance
  have hm : IsIso ((sheafCompose J U).map ((constantSheafAdj J D hT).counit.app F)) := by
    rw [← constantSheafAdj_counit_w J U F hT]
    exact IsIso.comp_isIso' (inferInstanceAs (IsIso
      ((constantCommuteCompose J U).app (F.obj.obj (op T))).hom)) hc
  exact isIso_of_reflects_iso _ (sheafCompose J U)

end EtaleCohomology.Sites

namespace EtaleCohomology

/-- A constant underlying set sheaf yields an actual constant module sheaf
via the counit, with its module of global sections as the model. -/
def etaleModuleConstantIso (X : Scheme.{u}) (R : Type u) [CommRing R]
    [(constantSheaf X.smallEtaleTopology (Type u)).Faithful]
    [(constantSheaf X.smallEtaleTopology (Type u)).Full]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    [Sheaf.IsConstant X.smallEtaleTopology ((etaleModuleUnderlying X R).obj F)]
    {T : X.Etale} (hT : IsTerminal T) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (F.obj.obj (op T)) ≅ F := by
  let : X.smallEtaleTopology.PreservesSheafification (forget (ModuleCat.{u} R)) :=
    GrothendieckTopology.PreservesSheafification.transport
      X.smallEtaleTopology (Scheme.AffineEtale.topology X) (Scheme.AffineEtale.Spec X)
      (Type u) (forget (ModuleCat.{u} R))
  have : Sheaf.IsConstant X.smallEtaleTopology
      ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u} R))).obj F) :=
    inferInstanceAs (Sheaf.IsConstant X.smallEtaleTopology
      ((etaleModuleUnderlying X R).obj F))
  have := Sites.constantCounit_isIso_of_forget X.smallEtaleTopology
    (forget (ModuleCat.{u} R)) F hT
  exact asIso ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hT).counit.app F)

/-- A finite constant underlying set sheaf has an actual finite constant
module model. The coefficient ring itself need not be finite. -/
theorem exists_finite_constantModule_of_underlying_iso
    {X : Scheme.{u}} {R : Type u} [CommRing R]
    [(constantSheaf X.smallEtaleTopology (Type u)).Faithful]
    [(constantSheaf X.smallEtaleTopology (Type u)).Full]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (A : Type u) [Finite A]
    (e : (etaleModuleUnderlying X R).obj F ≅
      (constantSheaf X.smallEtaleTopology (Type u)).obj A)
    {T : X.Etale} (hT : IsTerminal T) :
    ∃ M : ModuleCat.{u} R, Finite M ∧ Module.Finite R M ∧
      Nonempty (F ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) := by
  have : Sheaf.IsConstant X.smallEtaleTopology ((etaleModuleUnderlying X R).obj F) :=
    Sheaf.isConstant_of_iso X.smallEtaleTopology e
  let es : ((etaleModuleUnderlying X R).obj F).obj.obj (op T) ≅ A :=
    ((sheafSections X.smallEtaleTopology (Type u)).obj (op T)).mapIso e ≪≫
      (asIso ((constantSheafAdj X.smallEtaleTopology (Type u) hT).unit.app A)).symm
  have : Finite (F.obj.obj (op T)) := Finite.of_equiv A es.toEquiv.symm
  exact ⟨F.obj.obj (op T), inferInstance, Module.Finite.of_finite,
    ⟨(etaleModuleConstantIso X R F hT).symm⟩⟩

end EtaleCohomology
