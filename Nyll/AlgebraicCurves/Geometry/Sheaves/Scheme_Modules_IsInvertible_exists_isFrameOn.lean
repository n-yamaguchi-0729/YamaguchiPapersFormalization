/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.PresheafInternalHom
import Nyll.SchemeTheory.Modules.SheafificationMonoidal
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import Nyll.SchemeTheory.Modules.TensorSections

/-!
# Frames near a point of an invertible module

An invertible module admits a section that is a frame on a neighbourhood of each point,
obtained from a local trivialization.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_exists_isFrameOn

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory.Limits

noncomputable section

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

namespace FrameBridge

open Opposite

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- A compatible family of generators whose scalar multiplication maps trivialize a module
    presheaf below an object. -/
structure TrivializationBelow (X₀ : Cᵒᵖ) where
  /-- The chosen generator for each morphism out of the base object. -/
  gen : ∀ {Y : Cᵒᵖ} (_ : X₀ ⟶ Y), F.obj Y
  /-- Compatibility of the chosen generators with presheaf restriction maps. -/
  compat : ∀ {Y Z : Cᵒᵖ} (f : X₀ ⟶ Y) (g : Y ⟶ Z), F.map g (gen f) = gen (f ≫ g)
  /-- Scalar multiplication by each chosen generator is bijective. -/
  bij : ∀ {Y : Cᵒᵖ} (f : X₀ ⟶ Y), Function.Bijective (fun a : R.obj Y => a • gen f)

end FrameBridge

end PresheafOfModules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace FrameBridge

open TopologicalSpace Opposite PresheafOfModules.FrameBridge

variable {X : Scheme.{u}}

variable (U : X.Opens)

/-- The identity map of ring sheaves describing restriction to the scheme associated to an open
    subset. -/
noncomputable def restrictRingCatSheafHom : (U : Scheme.{u}).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (U : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

/-- Restriction of module sheaves to an open subset, expressed as a sheaf pushforward. -/
noncomputable def restrictFunctor' : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom U)

lemma restrictFunctor'_eq : restrictFunctor' U = Modules.restrictFunctor U.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (U.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- The natural isomorphism identifying open restriction with pullback along its inclusion. -/
noncomputable def restrictFunctor'IsoPullback : restrictFunctor' U ≅ Modules.pullback U.ι :=
  eqToIso (restrictFunctor'_eq U) ≪≫ restrictFunctorIsoPullback U.ι

variable {U} (L : X.Modules)

lemma image_preimage_of_le {V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

section

variable (e : (restrictFunctor' U).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

/-- The local generator obtained by applying the inverse trivialization to the unit section. -/
noncomputable def gen₀ (W : (U : Scheme.{u}).Opens) : L.val.obj (op (U.ι ''ᵁ W)) :=
  (e.inv.val.app (op W)).hom (1 : Γ(U, W))

lemma gen₀_spec (W : (U : Scheme.{u}).Opens) (b : Γ(X, U.ι ''ᵁ W)) :
    (e.inv.val.app (op W)).hom b = b • (show Γ(L, U.ι ''ᵁ W) from gen₀ L e W) := by
  have h := (e.inv.val.app (op W)).hom.map_smul b (1 : Γ(U, W))
  have hunit : (show Γ(U, W) from b) • (1 : Γ(U, W)) = b :=
    (smul_eq_mul (show Γ(U, W) from b) (1 : Γ(U, W))).trans (mul_one _)
  exact (congrArg (e.inv.val.app (op W)).hom hunit).symm.trans h

lemma gen₀_bijective (W : (U : Scheme.{u}).Opens) :
    Function.Bijective (fun b : Γ(X, U.ι ''ᵁ W) => b • (show Γ(L, U.ι ''ᵁ W) from gen₀ L e W)) := by
  have h : Function.Bijective ((e.inv.val.app (op W)).hom) := by
    refine Function.bijective_iff_has_inverse.2 ⟨(e.hom.val.app (op W)).hom, fun b => ?_, fun m
        => ?_⟩
    · exact congr($(e.inv_hom_id).val.app (op W) |>.hom b)
    · exact congr($(e.hom_inv_id).val.app (op W) |>.hom m)
  exact (funext (gen₀_spec L e W) ▸ h :)

lemma gen₀_map {W W' : (U : Scheme.{u}).Opens} (i : W' ⟶ W) :
    L.val.map (U.ι.opensFunctor.map i).op (gen₀ L e W) = gen₀ L e W' := by
  have := PresheafOfModules.naturality_apply e.inv.val i.op (1 : Γ(U, W))
  rw [show ((SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf).val.map i.op) (1 : Γ(U, W)) =
    (1 : Γ(U, W')) from ((U : Scheme.{u}).presheaf.map i.op).hom.map_one] at this
  exact this.symm

omit e in
lemma bijective_smul_map_eqToHom {A B : X.Opens} (q : A = B) (t : L.val.obj (op A))
    (h : Function.Bijective (fun b : Γ(X, A) => b • (show Γ(L, A) from t))) :
    Function.Bijective (fun a : Γ(X, B) =>
      a • (show Γ(L, B) from L.val.map (eqToHom q.symm : B ⟶ A).op t)) := by
  subst q
  have e1 : L.val.map (eqToHom (rfl : A = A) : A ⟶ A).op t = t := by
    rw [eqToHom_refl, op_id]
    exact PresheafOfModules.InternalHom.map_id_apply (R := X.sheaf.obj) L.val _ _
  simpa only [e1] using h

/-- The compatible family of local generators supplied by a trivialization of the restricted
    module sheaf. -/
noncomputable def trivializationBelow : TrivializationBelow L.val (op U) where
  gen {Y} f := L.val.map (eqToHom (image_preimage_of_le (U := U) f.unop.le).symm :
      Y.unop ⟶ U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop)).op (gen₀ L e (U.ι ⁻¹ᵁ Y.unop))
  compat {Y Z} f g := by
    have hle : U.ι ⁻¹ᵁ Z.unop ≤ U.ι ⁻¹ᵁ Y.unop := fun x hx => g.unop.le hx
    dsimp only
    rw [← gen₀_map L e (homOfLE hle)]
    erw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    exact congrFun (congrArg
      (fun φ : (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop)) ⟶ Z) =>
        ((L.val.map φ).hom : L.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop))) → L.val.obj Z))
      (Subsingleton.elim _ _)) _
  bij {Y} f := bijective_smul_map_eqToHom L (image_preimage_of_le (U := U) f.unop.le) _
    (gen₀_bijective L e _)

end

end FrameBridge

namespace IsInvertible
open _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible
end IsInvertible
open scoped _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible in
open FrameBridge in
theorem IsInvertible.exists_isFrameOn' {X : Scheme.{u}} {M : X.Modules} (hM :
    Scheme.Modules.IsInvertible M) (x : X) :
    ∃ (U : X.Opens) (s : Γ(M, U)), x ∈ U ∧ IsFrameOn s U := by
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hM.1 x
  let e : (restrictFunctor' U).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf :=
    (restrictFunctor'IsoPullback U).app M ≪≫ eU
  let D := trivializationBelow M e
  refine ⟨U, D.gen (𝟙 (Opposite.op U)), hxU, ?_⟩
  intro W hWU _
  have hc : M.presheaf.map (homOfLE hWU).op (D.gen (𝟙 (Opposite.op U))) = D.gen (homOfLE hWU).op
      := by
    have h := D.compat (𝟙 (Opposite.op U)) (homOfLE hWU).op
    rw [Category.id_comp] at h
    exact h
  simp only [hc]
  exact D.bij (homOfLE hWU).op

end AlgebraicGeometry.Scheme.Modules

end

with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open _root_.AlgebraicGeometry Scheme_Modules_IsInvertible_exists_isFrameOn.AlgebraicGeometry
    _root_.AlgebraicGeometry.Scheme.Modules
    Scheme_Modules_IsInvertible_exists_isFrameOn.AlgebraicGeometry.Scheme.Modules in
with_weak_namespace Scheme_Modules_IsInvertible_exists_isFrameOn
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn {X :
    AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) (x : X) :
    ∃ (U : X.Opens) (s : Γ(M, U)), x ∈ U ∧ AlgebraicGeometry.Scheme.Modules.IsFrameOn s U :=
  AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn' hM x
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_exists_isFrameOn
end ProofImplementation
