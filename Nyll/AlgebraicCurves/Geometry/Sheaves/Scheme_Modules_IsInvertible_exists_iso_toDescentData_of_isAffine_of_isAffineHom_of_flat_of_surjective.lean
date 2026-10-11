/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffine_of_isAffineHom_of_flat_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTildePullback
import Nyll.AlgebraicCurves.Foundations.Algebra.Algebra_DescentCofaces
import Nyll.AlgebraicCurves.Geometry.Sheaves.tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_FaithfullyFlat_exists_submodule_isBaseChange_of_cocycle
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial
import Nyll.AlgebraicCurves.Geometry.Projective.Scheme_Modules_isInvertible_tilde_of_projective_rankOne
import Nyll.AlgebraicCurves.Geometry.Projective.Scheme_Modules_projective_sections_of_locallyTrivial
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_finite_sections_of_locallyTrivial
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_Invertible_of_projective_of_forall_finrank_eq_one

/-!
# Scheme Modules Is Invertible exists iso to Descent Data of is Affine of is Affine Hom of
flat of surjective
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.InvertibleAffineDescent

universe t v' u' v u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite


namespace CategoryTheory
open _root_.CategoryTheory
namespace Pseudofunctor
open _root_.CategoryTheory.Pseudofunctor
namespace DescentData
open _root_.CategoryTheory.Pseudofunctor.DescentData
open _root_.CategoryTheory.Pseudofunctor.DescentData
open _root_.CategoryTheory.Pseudofunctor
open _root_.CategoryTheory

open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

@[simps obj hom]
private def _root_.CategoryTheory.Pseudofunctor.DescentData.changeObj (D : F.DescentData f) (M : ∀
  i, F.obj (.mk (op (X i)))) (e : ∀ i, M i ≅ D.obj i) :
    F.DescentData f where
  obj := M
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (F.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D.hom q f₁ f₂ hf₁ hf₂ ≫
      (F.map f₂.op.toLoc).toFunctor.map (e i₂).inv
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [← D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
    dsimp only [pullHom]
    simp only [Functor.map_comp, Category.assoc, mapComp'_hom_naturality_assoc,
      mapComp'_inv_naturality]
  hom_self Y q i g hg := by
    rw [D.hom_self q g hg, Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id,
      _root_.CategoryTheory.Functor.map_id]
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc (F.map f₂.op.toLoc).toFunctor (e i₂).inv, Iso.inv_hom_id,
      _root_.CategoryTheory.Functor.map_id, Category.id_comp, D.hom_comp_assoc]

open _root_.CategoryTheory.Pseudofunctor.DescentData

private def _root_.CategoryTheory.Pseudofunctor.DescentData.changeObjIso (D : F.DescentData f) (M :
  ∀ i, F.obj (.mk (op (X i)))) (e : ∀ i, M i ≅ D.obj i) :
    D.changeObj M e ≅ D :=
  isoMk e (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ => by
    change (F.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D.hom q f₁ f₂ hf₁ hf₂ =
      ((F.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D.hom q f₁ f₂ hf₁ hf₂ ≫
        (F.map f₂.op.toLoc).toFunctor.map (e i₂).inv) ≫
          (F.map f₂.op.toLoc).toFunctor.map (e i₂).hom
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      _root_.CategoryTheory.Functor.map_id, Category.comp_id])

open _root_.CategoryTheory.Pseudofunctor.DescentData

-- Keep the pseudofunctor computation abstract before specializing it to modules.
private theorem pullHom_eq_comp {X₁ X₂ Y Y' : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ h₁ h₂ =
      (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by rw [← h₁]; rfl)).hom.toNatTrans.app M₁ ≫
        (F.map g.op.toLoc).toFunctor.map φ ≫
        (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (by rw [← h₂]; rfl)).inv.toNatTrans.app M₂ := rfl

private theorem toDescentData_obj_hom_eq {S X : C} (q : X ⟶ S)
    (L : F.obj (.mk (op S))) {Z : C} (z : Z ⟶ S) (g₁ g₂ : Z ⟶ X)
    (h₁ : g₁ ≫ q = z) (h₂ : g₂ ≫ q = z) :
    ((F.toDescentData (fun _ : Unit => q)).obj L).hom z g₁ g₂ h₁ h₂ (i₁ := ()) (i₂ := ()) =
      (F.mapComp' q.op.toLoc g₁.op.toLoc z.op.toLoc (by rw [← h₁]; rfl)).inv.toNatTrans.app L ≫
        (F.mapComp' q.op.toLoc g₂.op.toLoc z.op.toLoc
          (by rw [← h₂]; rfl)).hom.toNatTrans.app L := rfl

theorem pullHom_hom_comp_pullHom_hom {S X : C} {q : X ⟶ S} (D : F.DescentData (fun _ : Unit => q))
    {Z : C} (z : Z ⟶ S) (g₁ g₂ : Z ⟶ X) (hg₁ : g₁ ≫ q = z) (hg₂ : g₂ ≫ q = z)
    {W : C} (d₀ d₁ d₂ : W ⟶ Z) (π₁ π₂ π₃ : W ⟶ X)
    (h₂₁ : d₂ ≫ g₁ = π₁) (h₂₂ : d₂ ≫ g₂ = π₂) (h₀₁ : d₀ ≫ g₁ = π₂) (h₀₂ : d₀ ≫ g₂ = π₃)
    (h₁₁ : d₁ ≫ g₁ = π₁) (h₁₂ : d₁ ≫ g₂ = π₃) :
    pullHom (D.hom z g₁ g₂ hg₁ hg₂ (i₁ := ()) (i₂ := ())) d₂ π₁ π₂ h₂₁ h₂₂ ≫
        pullHom (D.hom z g₁ g₂ hg₁ hg₂ (i₁ := ()) (i₂ := ())) d₀ π₂ π₃ h₀₁ h₀₂ =
      pullHom (D.hom z g₁ g₂ hg₁ hg₂ (i₁ := ()) (i₂ := ())) d₁ π₁ π₃ h₁₁ h₁₂ := by
  have e₀ : d₀ ≫ z = d₂ ≫ z := by
    rw [← hg₁, reassoc_of% h₀₁, ← h₂₂, Category.assoc, hg₂, hg₁]
  have e₁ : d₁ ≫ z = d₂ ≫ z := by
    rw [← hg₁, reassoc_of% h₁₁, ← h₂₁, Category.assoc]
  rw [D.pullHom_hom d₂ z (d₂ ≫ z) rfl g₁ g₂ hg₁ hg₂ π₁ π₂ h₂₁ h₂₂,
    D.pullHom_hom d₀ z (d₂ ≫ z) e₀ g₁ g₂ hg₁ hg₂ π₂ π₃ h₀₁ h₀₂,
    D.pullHom_hom d₁ z (d₂ ≫ z) e₁ g₁ g₂ hg₁ hg₂ π₁ π₃ h₁₁ h₁₂,
    D.hom_comp]

theorem pullHom_hom_diag {S X : C} {q : X ⟶ S} (D : F.DescentData (fun _ : Unit => q))
    {Z : C} (z : Z ⟶ S) (g₁ g₂ : Z ⟶ X) (hg₁ : g₁ ≫ q = z) (hg₂ : g₂ ≫ q = z)
    (Δ : X ⟶ Z) (hΔ₁ : Δ ≫ g₁ = 𝟙 X) (hΔ₂ : Δ ≫ g₂ = 𝟙 X) :
    pullHom (D.hom z g₁ g₂ hg₁ hg₂ (i₁ := ()) (i₂ := ())) Δ (𝟙 X) (𝟙 X) hΔ₁ hΔ₂ = 𝟙 _ := by
  rw [D.pullHom_hom Δ z q (by rw [← hg₁, reassoc_of% hΔ₁]) g₁ g₂ hg₁ hg₂ (𝟙 X) (𝟙 X) hΔ₁ hΔ₂,
    D.hom_self]
  simp

theorem comm_of_fac {S X : C} {q : X ⟶ S} (D₁ D₂ : F.DescentData (fun _ : Unit => q))
    (φ : D₁.obj () ⟶ D₂.obj ())
    {Z : C} (z : Z ⟶ S) (g₁ g₂ : Z ⟶ X) (hg₁ : g₁ ≫ q = z) (hg₂ : g₂ ≫ q = z)
    (H : (F.map g₁.op.toLoc).toFunctor.map φ ≫ D₂.hom z g₁ g₂ hg₁ hg₂ =
      D₁.hom z g₁ g₂ hg₁ hg₂ ≫ (F.map g₂.op.toLoc).toFunctor.map φ)
    {Y : C} (y : Y ⟶ S) (f₁ f₂ : Y ⟶ X) (hf₁ : f₁ ≫ q = y) (hf₂ : f₂ ≫ q = y)
    (l : Y ⟶ Z) (hl₁ : l ≫ g₁ = f₁) (hl₂ : l ≫ g₂ = f₂) :
    (F.map f₁.op.toLoc).toFunctor.map φ ≫ D₂.hom y f₁ f₂ hf₁ hf₂ =
      D₁.hom y f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map φ := by
  have hy : l ≫ z = y := by rw [← hg₁, reassoc_of% hl₁, hf₁]
  rw [← D₁.pullHom_hom l z y hy g₁ g₂ hg₁ hg₂ f₁ f₂ hl₁ hl₂,
    ← D₂.pullHom_hom l z y hy g₁ g₂ hg₁ hg₂ f₁ f₂ hl₁ hl₂]
  dsimp only [pullHom]
  simp only [Category.assoc]
  rw [mapComp'_hom_naturality_assoc]
  rw [← Functor.map_comp_assoc, H, Functor.map_comp_assoc, mapComp'_inv_naturality]

private theorem nonempty_iso_of_fac {S X : C} {q : X ⟶ S}
    (D₁ D₂ : F.DescentData (fun _ : Unit => q)) (e : D₁.obj () ≅ D₂.obj ())
    {Z : C} (z : Z ⟶ S) (g₁ g₂ : Z ⟶ X) (h₁ : g₁ ≫ q = z) (h₂ : g₂ ≫ q = z)
    (fac : ∀ ⦃Y : C⦄ (f₁ f₂ : Y ⟶ X), f₁ ≫ q = f₂ ≫ q →
      ∃ l : Y ⟶ Z, l ≫ g₁ = f₁ ∧ l ≫ g₂ = f₂)
    (H : (F.map g₁.op.toLoc).toFunctor.map e.hom ≫ D₂.hom z g₁ g₂ h₁ h₂ =
      D₁.hom z g₁ g₂ h₁ h₂ ≫ (F.map g₂.op.toLoc).toFunctor.map e.hom) : Nonempty (D₁ ≅ D₂) := by
  refine ⟨isoMk (fun _ => e) ?_⟩
  intro Y y i₁ i₂ f₁ f₂ hf₁ hf₂
  obtain ⟨l, hl₁, hl₂⟩ := fac f₁ f₂ (hf₁.trans hf₂.symm)
  exact comm_of_fac D₁ D₂ e.hom z g₁ g₂ h₁ h₂ H y f₁ f₂ hf₁ hf₂ l hl₁ hl₂

theorem exists_iso_toDescentData_of_arrow_iso
    (P : ∀ ⦃Z : C⦄, F.obj (.mk (op Z)) → Prop)
    (hP : ∀ ⦃Z Z' : C⦄ (g : Z' ⟶ Z) (M : F.obj (.mk (op Z))), P M → P ((F.map
      g.op.toLoc).toFunctor.obj M))
    {S₁ X₁ S₀ X₀ : C} {q : X₁ ⟶ S₁} {q₀ : X₀ ⟶ S₀} (e : S₁ ≅ S₀) (e' : X₁ ≅ X₀)
    (comm : e'.hom ≫ q₀ = q ≫ e.hom)
    (H : ∀ (D₀ : F.DescentData (fun _ : Unit => q₀)), (∀ i, P (D₀.obj i)) →
      ∃ L₀ : F.obj (.mk (op S₀)), P L₀ ∧ Nonempty ((F.toDescentData (fun _ : Unit => q₀)).obj L₀ ≅
        D₀))
    (D : F.DescentData (fun _ : Unit => q)) (hD : ∀ i, P (D.obj i)) :
    ∃ L : F.obj (.mk (op S₁)), P L ∧ Nonempty ((F.toDescentData (fun _ : Unit => q)).obj L ≅ D) :=
      by
  have w : ∀ (_ : Unit), e'.inv ≫ q = q₀ ≫ e.symm.hom := fun _ => by
    rw [Iso.symm_hom, Iso.inv_comp_eq, reassoc_of% comm, e.hom_inv_id, Category.comp_id]
  have w' : ∀ (_ : Unit), e'.hom ≫ q₀ = q ≫ e.symm.inv := fun _ => by simpa using comm
  let E := pullFunctorEquivalence (f := fun _ : Unit => q) (f' := fun _ : Unit => q₀) F e.symm
    (α := fun j => j) (p' := fun _ => e'.inv) w (β := fun i => i) (q' := fun _ => e'.hom) w'
  obtain ⟨L₀, hL₀, ⟨ι⟩⟩ := H (E.functor.obj D) (fun i => hP _ _ (hD i))
  exact ⟨(F.map e.hom.op.toLoc).toFunctor.obj L₀, hP _ _ hL₀,
    ⟨((toDescentDataCompPullFunctorIso F (f := fun _ : Unit => q₀) (f' := fun _ : Unit => q) (α :=
      fun i => i)
        (p := e.symm.inv) (p' := fun _ => e'.hom) w').app L₀).symm ≪≫
      E.inverse.mapIso ι ≪≫ (E.unitIso.app D).symm⟩⟩

end CategoryTheory.Pseudofunctor.DescentData

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry


namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

/-- The pseudofunctor of modules on schemes used to form descent data. -/
noncomputable abbrev MOD : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

section dictionary

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem Mod_map_obj (L : Y.Modules) : (MOD.map f.op.toLoc).toFunctor.obj L =
  (_root_.AlgebraicGeometry.Scheme.Modules.pullback f).obj L := rfl

theorem Mod_map_map {L L' : Y.Modules} (a : L ⟶ L') :
    (MOD.map f.op.toLoc).toFunctor.map a = (_root_.AlgebraicGeometry.Scheme.Modules.pullback f).map
      a := rfl

theorem Mod_mapComp'_hom_app_aux {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u : a ⟶ b) (v : b ⟶ d) (M
  : MOD.obj a) :
    (MOD.mapComp' u v (u ≫ v) rfl).hom.toNatTrans.app M = (MOD.mapComp u v).hom.toNatTrans.app M :=
      by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem Mod_mapComp'_inv_app_aux {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u : a ⟶ b) (v : b ⟶ d) (M
  : MOD.obj a) :
    (MOD.mapComp' u v (u ≫ v) rfl).inv.toNatTrans.app M = (MOD.mapComp u v).inv.toNatTrans.app M :=
      by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem Mod_mapComp'_hom_app (fg : X ⟶ Z) (h : f ≫ g = fg) (L : Z.Modules) :
    (MOD.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app L =
    (pullbackCongr h.symm).hom.app L ≫ (pullbackComp f g).inv.app L := by
  subst h
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact Mod_mapComp'_hom_app_aux g.op.toLoc f.op.toLoc L

theorem Mod_mapComp'_inv_app (fg : X ⟶ Z) (h : f ≫ g = fg) (L : Z.Modules) :
    (MOD.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app L =
    (pullbackComp f g).hom.app L ≫ (pullbackCongr h).hom.app L := by
  subst h
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  exact Mod_mapComp'_inv_app_aux g.op.toLoc f.op.toLoc L

theorem pullbackCongr_hom_app {f f' : X ⟶ Y} (h : f = f') (L : Y.Modules) :
    (pullbackCongr h).hom.app L = eqToHom (by rw [h]) := by
  subst h; simp [pullbackCongr]

theorem pullbackCongr_inv_app {f f' : X ⟶ Y} (h : f = f') (L : Y.Modules) :
    (pullbackCongr h).inv.app L = eqToHom (by rw [h]) := by
  subst h; simp [pullbackCongr]

theorem pullbackCongr_symm_hom {f f' : X ⟶ Y} (h : f = f') :
    (pullbackCongr h.symm).hom = (pullbackCongr h).inv := by
  subst h; rfl
@[reassoc (attr := simp)]
theorem pullbackCongr_hom_app_inv_app {f f' : X ⟶ Y} (h : f = f') (L : Y.Modules) :
    (pullbackCongr h).hom.app L ≫ (pullbackCongr h).inv.app L = 𝟙 _ :=
  Iso.hom_inv_id_app _ _
@[reassoc (attr := simp)]
theorem pullbackCongr_inv_app_hom_app {f f' : X ⟶ Y} (h : f = f') (L : Y.Modules) :
    (pullbackCongr h).inv.app L ≫ (pullbackCongr h).hom.app L = 𝟙 _ :=
  Iso.inv_hom_id_app _ _
@[reassoc]
theorem pullbackCongr_hom_app_trans {f f' f'' : X ⟶ Y} (h : f = f') (h' : f' = f'') (L : Y.Modules)
  :
    (pullbackCongr h).hom.app L ≫ (pullbackCongr h').hom.app L = (pullbackCongr (h.trans
      h')).hom.app L := by
  subst h h'; simp [pullbackCongr]

theorem pullbackCongr_rfl_hom_app (f : X ⟶ Y) (L : Y.Modules) :
    (pullbackCongr (rfl : f = f)).hom.app L = 𝟙 _ := by
  simp [pullbackCongr]

theorem pullbackCongr_rfl_inv_app (f : X ⟶ Y) (L : Y.Modules) :
    (pullbackCongr (rfl : f = f)).inv.app L = 𝟙 _ := by
  simp [pullbackCongr]

theorem pullHom_MOD {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules} {f₁ : Y ⟶ X₁} {f₂
  : Y ⟶ X₂}
    (χ : (_root_.AlgebraicGeometry.Scheme.Modules.pullback f₁).obj M₁ ⟶
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback f₂).obj M₂) (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁)
      (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := MOD) (M₁ := M₁) (M₂ := M₂) (f₁ := f₁) (f₂ :=
      f₂)
        χ g gf₁ gf₂ h₁ h₂ =
      (pullbackCongr h₁).inv.app M₁ ≫ (pullbackComp g f₁).inv.app M₁ ≫
        (_root_.AlgebraicGeometry.Scheme.Modules.pullback g).map χ ≫
        (pullbackComp g f₂).hom.app M₂ ≫ (pullbackCongr h₂).hom.app M₂ := by
  refine (CategoryTheory.Pseudofunctor.DescentData.pullHom_eq_comp
    (F := MOD) χ g gf₁ gf₂ h₁ h₂).trans ?_
  rw [Mod_mapComp'_hom_app g f₁ gf₁ h₁, Mod_mapComp'_inv_app g f₂ gf₂ h₂, pullbackCongr_symm_hom h₁]
  exact Category.assoc _ _ _

end dictionary

section single

variable {X S : Scheme.{u}} {q : X ⟶ S}

/-- The comparison morphism supplied by descent data for two lifts of the same morphism. -/
noncomputable def ddHom (D : MOD.DescentData (fun _ : Unit => q)) {Z : Scheme.{u}} (z : Z ⟶ S)
    (g₁ g₂ : Z ⟶ X) (h₁ : g₁ ≫ q = z) (h₂ : g₂ ≫ q = z) :
    (_root_.AlgebraicGeometry.Scheme.Modules.pullback g₁).obj (D.obj ()) ⟶
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback g₂).obj (D.obj ()) :=
  D.hom z g₁ g₂ h₁ h₂ (i₁ := ()) (i₂ := ())

theorem ddHom_eq (D : MOD.DescentData (fun _ : Unit => q)) {Z : Scheme.{u}} (z : Z ⟶ S)
    (g₁ g₂ : Z ⟶ X) (h₁ : g₁ ≫ q = z) (h₂ : g₂ ≫ q = z) :
    ddHom D z g₁ g₂ h₁ h₂ = D.hom z g₁ g₂ h₁ h₂ (i₁ := ()) (i₂ := ()) := rfl

scoped instance isIso_ddHom (D : MOD.DescentData (fun _ : Unit => q)) {Z : Scheme.{u}} (z : Z ⟶ S)
    (g₁ g₂ : Z ⟶ X) (h₁ : g₁ ≫ q = z) (h₂ : g₂ ≫ q = z) : IsIso (ddHom D z g₁ g₂ h₁ h₂) :=
  ⟨⟨D.hom z g₂ g₁ h₂ h₁ (i₁ := ()) (i₂ := ()), (D.iso z g₁ g₂ h₁ h₂ (i₁ := ()) (i₂ :=
    ())).hom_inv_id,
    (D.iso z g₁ g₂ h₁ h₂ (i₁ := ()) (i₂ := ())).inv_hom_id⟩⟩

theorem ddHom_toDescentData (L : S.Modules) {Z : Scheme.{u}} (z : Z ⟶ S) (g₁ g₂ : Z ⟶ X)
    (h₁ : g₁ ≫ q = z) (h₂ : g₂ ≫ q = z) :
    ddHom ((MOD.toDescentData (fun _ : Unit => q)).obj L) z g₁ g₂ h₁ h₂ =
      (pullbackComp g₁ q).hom.app L ≫ (pullbackCongr (h₁.trans h₂.symm)).hom.app L ≫
        (pullbackComp g₂ q).inv.app L := by
  refine (CategoryTheory.Pseudofunctor.DescentData.toDescentData_obj_hom_eq
    (F := MOD) q L z g₁ g₂ h₁ h₂).trans ?_
  rw [Mod_mapComp'_inv_app g₁ q z h₁ L, Mod_mapComp'_hom_app g₂ q z h₂ L]
  exact (Category.assoc ((pullbackComp g₁ q).hom.app L)
    ((pullbackCongr h₁).hom.app L)
    ((pullbackCongr h₂.symm).hom.app L ≫ (pullbackComp g₂ q).inv.app L)).trans
      (congrArg (fun t => (pullbackComp g₁ q).hom.app L ≫ t)
        (pullbackCongr_hom_app_trans_assoc h₁ h₂.symm L ((pullbackComp g₂ q).inv.app L)))

theorem ddHom_cocycle (D : MOD.DescentData (fun _ : Unit => q)) {Z : Scheme.{u}} (z : Z ⟶ S)
    (g₁ g₂ : Z ⟶ X) (hg₁ : g₁ ≫ q = z) (hg₂ : g₂ ≫ q = z) {W : Scheme.{u}} (d₀ d₁ d₂ : W ⟶ Z)
    (h₀₁ : d₀ ≫ g₁ = d₂ ≫ g₂) (h₁₁ : d₁ ≫ g₁ = d₂ ≫ g₁) (h₁₂ : d₁ ≫ g₂ = d₀ ≫ g₂) :
    ((pullbackComp d₂ g₁).inv.app _ ≫ (_root_.AlgebraicGeometry.Scheme.Modules.pullback d₂).map
      (ddHom D z g₁ g₂ hg₁ hg₂) ≫
        (pullbackComp d₂ g₂).hom.app _) ≫
      ((pullbackCongr h₀₁).inv.app _ ≫ (pullbackComp d₀ g₁).inv.app _ ≫
        (_root_.AlgebraicGeometry.Scheme.Modules.pullback d₀).map (ddHom D z g₁ g₂ hg₁ hg₂) ≫
          (pullbackComp d₀ g₂).hom.app _) =
    (pullbackCongr h₁₁).inv.app _ ≫ (pullbackComp d₁ g₁).inv.app _ ≫
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback d₁).map (ddHom D z g₁ g₂ hg₁ hg₂) ≫
      (pullbackComp d₁ g₂).hom.app _ ≫ (pullbackCongr h₁₂).hom.app _ := by
  have H := CategoryTheory.Pseudofunctor.DescentData.pullHom_hom_comp_pullHom_hom
    D z g₁ g₂ hg₁ hg₂ d₀ d₁ d₂
    (d₂ ≫ g₁) (d₂ ≫ g₂) (d₀ ≫ g₂) rfl rfl h₀₁ rfl h₁₁ h₁₂
  rw [← ddHom_eq] at H
  erw [pullHom_MOD, pullHom_MOD, pullHom_MOD] at H
  have H' :
      ((pullbackCongr (rfl : d₂ ≫ g₁ = d₂ ≫ g₁)).inv.app (D.obj ()) ≫
        (pullbackComp d₂ g₁).inv.app (D.obj ()) ≫
        (Scheme.Modules.pullback d₂).map (ddHom D z g₁ g₂ hg₁ hg₂) ≫
        (pullbackComp d₂ g₂).hom.app (D.obj ()) ≫
        (pullbackCongr (rfl : d₂ ≫ g₂ = d₂ ≫ g₂)).hom.app (D.obj ())) ≫
      ((pullbackCongr h₀₁).inv.app (D.obj ()) ≫
        (pullbackComp d₀ g₁).inv.app (D.obj ()) ≫
        (Scheme.Modules.pullback d₀).map (ddHom D z g₁ g₂ hg₁ hg₂) ≫
        (pullbackComp d₀ g₂).hom.app (D.obj ()) ≫
        (pullbackCongr (rfl : d₀ ≫ g₂ = d₀ ≫ g₂)).hom.app (D.obj ())) =
      (pullbackCongr h₁₁).inv.app (D.obj ()) ≫
        (pullbackComp d₁ g₁).inv.app (D.obj ()) ≫
        (Scheme.Modules.pullback d₁).map (ddHom D z g₁ g₂ hg₁ hg₂) ≫
        (pullbackComp d₁ g₂).hom.app (D.obj ()) ≫
        (pullbackCongr h₁₂).hom.app (D.obj ()) := H
  simpa only [pullbackCongr_rfl_hom_app (d₂ ≫ g₂) (D.obj ()),
    pullbackCongr_rfl_hom_app (d₀ ≫ g₂) (D.obj ()),
    pullbackCongr_rfl_inv_app (d₂ ≫ g₁) (D.obj ()),
    Category.comp_id, Category.id_comp, Category.assoc] using H'

theorem nonempty_toDescentData_iso (D : MOD.DescentData (fun _ : Unit => q)) (L : S.Modules)
    (e₀ : (_root_.AlgebraicGeometry.Scheme.Modules.pullback q).obj L ≅ D.obj ())
    {Z : Scheme.{u}} (z : Z ⟶ S) (g₁ g₂ : Z ⟶ X) (h₁ : g₁ ≫ q = z) (h₂ : g₂ ≫ q = z)
    (fac : ∀ ⦃Y : Scheme.{u}⦄ (f₁ f₂ : Y ⟶ X), f₁ ≫ q = f₂ ≫ q → ∃ l : Y ⟶ Z, l ≫ g₁ = f₁ ∧ l ≫ g₂
      = f₂)
    (hcomm : (_root_.AlgebraicGeometry.Scheme.Modules.pullback g₁).map e₀.hom ≫ ddHom D z g₁ g₂ h₁
      h₂ =
      ((pullbackComp g₁ q).hom.app L ≫ (pullbackCongr (h₁.trans h₂.symm)).hom.app L ≫
        (pullbackComp g₂ q).inv.app L) ≫ (_root_.AlgebraicGeometry.Scheme.Modules.pullback g₂).map
          e₀.hom) :
    Nonempty ((MOD.toDescentData (fun _ : Unit => q)).obj L ≅ D) := by
  refine CategoryTheory.Pseudofunctor.DescentData.nonempty_iso_of_fac
    ((MOD.toDescentData (fun _ : Unit => q)).obj L) D e₀ z g₁ g₂ h₁ h₂ fac ?_
  change (_root_.AlgebraicGeometry.Scheme.Modules.pullback g₁).map e₀.hom ≫ ddHom D z g₁ g₂ h₁ h₂ =
    ddHom ((MOD.toDescentData (fun _ : Unit => q)).obj L) z g₁ g₂ h₁ h₂ ≫
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback g₂).map e₀.hom
  rw [ddHom_toDescentData]
  exact hcomm

theorem ddHom_cocycle' (D : MOD.DescentData (fun _ : Unit => q)) {M : X.Modules} (hM : D.obj () = M)
    {Z : Scheme.{u}} (z : Z ⟶ S) (g₁ g₂ : Z ⟶ X) (hg₁ : g₁ ≫ q = z) (hg₂ : g₂ ≫ q = z)
    {W : Scheme.{u}} (d₀ d₁ d₂ : W ⟶ Z)
    (h₀₁ : d₀ ≫ g₁ = d₂ ≫ g₂) (h₁₁ : d₁ ≫ g₁ = d₂ ≫ g₁) (h₁₂ : d₁ ≫ g₂ = d₀ ≫ g₂)
    (χ : (_root_.AlgebraicGeometry.Scheme.Modules.pullback g₁).obj M ⟶
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback g₂).obj M) (hχ : HEq χ (ddHom D z g₁ g₂ hg₁
      hg₂)) :
    ((pullbackComp d₂ g₁).inv.app _ ≫ (_root_.AlgebraicGeometry.Scheme.Modules.pullback d₂).map χ ≫
      (pullbackComp d₂ g₂).hom.app _) ≫
      ((pullbackCongr h₀₁).inv.app _ ≫ (pullbackComp d₀ g₁).inv.app _ ≫
        (_root_.AlgebraicGeometry.Scheme.Modules.pullback d₀).map χ ≫ (pullbackComp d₀ g₂).hom.app
          _) =
    (pullbackCongr h₁₁).inv.app _ ≫ (pullbackComp d₁ g₁).inv.app _ ≫
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback d₁).map χ ≫ (pullbackComp d₁ g₂).hom.app _
        ≫ (pullbackCongr h₁₂).hom.app _ := by
  subst hM
  obtain rfl := eq_of_heq hχ
  exact ddHom_cocycle D z g₁ g₂ hg₁ hg₂ d₀ d₁ d₂ h₀₁ h₁₁ h₁₂

theorem nonempty_toDescentData_iso' (D : MOD.DescentData (fun _ : Unit => q)) {M : X.Modules}
    (hM : D.obj () = M) (L : S.Modules) (e₀ : (_root_.AlgebraicGeometry.Scheme.Modules.pullback
      q).obj L ≅ M)
    {Z : Scheme.{u}} (z : Z ⟶ S) (g₁ g₂ : Z ⟶ X) (h₁ : g₁ ≫ q = z) (h₂ : g₂ ≫ q = z)
    (fac : ∀ ⦃Y : Scheme.{u}⦄ (f₁ f₂ : Y ⟶ X), f₁ ≫ q = f₂ ≫ q → ∃ l : Y ⟶ Z, l ≫ g₁ = f₁ ∧ l ≫ g₂
      = f₂)
    (χ : (_root_.AlgebraicGeometry.Scheme.Modules.pullback g₁).obj M ⟶
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback g₂).obj M) (hχ : HEq χ (ddHom D z g₁ g₂ h₁
      h₂))
    (hcomm : (_root_.AlgebraicGeometry.Scheme.Modules.pullback g₁).map e₀.hom ≫ χ =
      ((pullbackComp g₁ q).hom.app L ≫ (pullbackCongr (h₁.trans h₂.symm)).hom.app L ≫
        (pullbackComp g₂ q).inv.app L) ≫ (_root_.AlgebraicGeometry.Scheme.Modules.pullback g₂).map
          e₀.hom) :
    Nonempty ((MOD.toDescentData (fun _ : Unit => q)).obj L ≅ D) := by
  subst hM
  obtain rfl := eq_of_heq hχ
  exact nonempty_toDescentData_iso D L e₀ z g₁ g₂ h₁ h₂ fac hcomm

end single

end AlgebraicGeometry.Scheme.Modules

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry


namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section tildeFace

variable {S T U : CommRingCat.{u}}

scoped instance tilde_map_isIso {M M' : ModuleCat.{u} S} (f : M ⟶ M') [IsIso f] : IsIso (tilde.map
  f) :=
  inferInstanceAs (IsIso ((tilde.functor S).map f))

theorem pullbackSpecIso_hom_eq {α β : S ⟶ T} (h : α = β) (N : ModuleCat.{u} S)
    (E₁ : (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map β)).obj (tilde N) =
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map α)).obj (tilde N))
    (E₂ : (ModuleCat.extendScalars α.hom).obj N = (ModuleCat.extendScalars β.hom).obj N) :
    (tilde.pullbackSpecIso β N).hom = eqToHom E₁ ≫ (tilde.pullbackSpecIso α N).hom ≫ tilde.map
      (eqToHom E₂) := by
  subst h; simp

theorem pullbackSpecIso_inv_eq {α β : S ⟶ T} (h : α = β) (N : ModuleCat.{u} S)
    (E₁ : (ModuleCat.extendScalars β.hom).obj N = (ModuleCat.extendScalars α.hom).obj N)
    (E₂ : (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map α)).obj (tilde N) =
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map β)).obj (tilde N)) :
    (tilde.pullbackSpecIso β N).inv = tilde.map (eqToHom E₁) ≫ (tilde.pullbackSpecIso α N).inv ≫
      eqToHom E₂ := by
  subst h; simp

theorem pullbackSpecIso_inv_eqToHom_hom {α β : S ⟶ T} (h : α = β) (N : ModuleCat.{u} S)
    (E : (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map α)).obj (tilde N) =
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map β)).obj (tilde N))
    (E' : (ModuleCat.extendScalars α.hom).obj N = (ModuleCat.extendScalars β.hom).obj N) :
    (tilde.pullbackSpecIso α N).inv ≫ eqToHom E ≫ (tilde.pullbackSpecIso β N).hom = tilde.map
      (eqToHom E') := by
  subst h; simp

theorem pullbackSpecIso_hom_tilde_map_eqToHom {α β : S ⟶ T} (h : α = β) (N : ModuleCat.{u} S)
    (E : (ModuleCat.extendScalars α.hom).obj N = (ModuleCat.extendScalars β.hom).obj N)
    (E' : (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map α)).obj (tilde N) =
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map β)).obj (tilde N)) :
    (tilde.pullbackSpecIso α N).hom ≫ tilde.map (eqToHom E) = eqToHom E' ≫ (tilde.pullbackSpecIso β
      N).hom := by
  subst h; simp

theorem pullbackSpecIso_hom_tilde_map_eqToHom_comp {α β : S ⟶ T} (h : α = β) (N : ModuleCat.{u} S)
    (E : (ModuleCat.extendScalars α.hom).obj N = (ModuleCat.extendScalars β.hom).obj N)
    (E' : (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map α)).obj (tilde N) =
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map β)).obj (tilde N))
    {Z : ModuleCat.{u} T} (X : (ModuleCat.extendScalars β.hom).obj N ⟶ Z) :
    (tilde.pullbackSpecIso α N).hom ≫ tilde.map (eqToHom E ≫ X) =
      eqToHom E' ≫ (tilde.pullbackSpecIso β N).hom ≫ tilde.map X := by
  subst h; simp

theorem tilde_face {i₁ i₂ : S ⟶ T} {N : ModuleCat.{u} S}
    (χ : (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map i₁)).obj (tilde N) ⟶
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map i₂)).obj (tilde N))
    (ψ : (ModuleCat.extendScalars i₁.hom).obj N ⟶ (ModuleCat.extendScalars i₂.hom).obj N)
    (hψ : (tilde.pullbackSpecIso i₁ N).hom ≫ tilde.map ψ = χ ≫ (tilde.pullbackSpecIso i₂ N).hom)
    (δ : T ⟶ U) :
    (pullbackComp (Spec.map δ) (Spec.map i₁)).inv.app (tilde N) ≫
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map δ)).map χ ≫
        (pullbackComp (Spec.map δ) (Spec.map i₂)).hom.app (tilde N) =
      (pullbackCongr (Spec.map_comp i₁ δ).symm).hom.app (tilde N) ≫ (tilde.pullbackSpecIso (i₁ ≫ δ)
        N).hom ≫
        tilde.map ((ModuleCat.extendScalarsComp i₁.hom δ.hom).hom.app N ≫
          (ModuleCat.extendScalars δ.hom).map ψ ≫ (ModuleCat.extendScalarsComp i₂.hom
            δ.hom).inv.app N) ≫
        (tilde.pullbackSpecIso (i₂ ≫ δ) N).inv ≫ (pullbackCongr (Spec.map_comp i₂ δ).symm).inv.app
          (tilde N) := by
  have H₁ := tilde.pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom i₁ δ N
  have H₂ := tilde.pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom i₂ δ N
  have Hn := tilde.pullbackSpecIso_hom_naturality δ ψ
  revert hψ H₁ H₂ Hn
  generalize pullbackCongr (Spec.map_comp i₁ δ).symm = G₁
  generalize pullbackCongr (Spec.map_comp i₂ δ).symm = G₂
  generalize pullbackComp (Spec.map δ) (Spec.map i₁) = C₁
  generalize pullbackComp (Spec.map δ) (Spec.map i₂) = C₂
  generalize tilde.pullbackSpecIso i₁ N = β₁
  generalize tilde.pullbackSpecIso i₂ N = β₂
  generalize tilde.pullbackSpecIso (i₁ ≫ δ) N = B₁
  generalize tilde.pullbackSpecIso (i₂ ≫ δ) N = B₂
  generalize tilde.pullbackSpecIso δ ((ModuleCat.extendScalars i₁.hom).obj N) = γ₁
  generalize tilde.pullbackSpecIso δ ((ModuleCat.extendScalars i₂.hom).obj N) = γ₂
  intro hψ H₁ H₂ Hn
  obtain rfl : χ = β₁.hom ≫ tilde.map ψ ≫ β₂.inv := by
    rw [← Category.assoc, hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp only [tilde.functor] at H₁ H₂ Hn ⊢
  rw [← cancel_mono (G₂.hom.app (tilde N) ≫ B₂.hom ≫
    tilde.map ((ModuleCat.extendScalarsComp i₂.hom δ.hom).hom.app N))]
  simp only [Functor.map_comp, tilde.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_assoc]
  rw [← tilde.map_comp ((ModuleCat.extendScalarsComp i₂.hom δ.hom).inv.app N), Iso.inv_hom_id_app,
    tilde.map_id]
  dsimp only [Functor.comp_obj]
  rw [Category.comp_id]
  erw [← H₂]
  rw [Iso.map_inv_hom_id_assoc]
  erw [Hn, reassoc_of% H₁]
  simp only [Iso.inv_hom_id_app_assoc]

end tildeFace

end AlgebraicGeometry.Scheme.Modules

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.TensorProduct
open _root_.Algebra.DescentCofaces


namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace AffineInvertibleDescent

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The algebra structure homomorphism regarded as a morphism of commutative rings. -/
abbrev alg : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)

theorem spec_i₁_alg : Spec.map (i₁ A B) ≫ Spec.map (alg A B) = Spec.map (alg A B ≫ i₁ A B) :=
  (Spec.map_comp _ _).symm

theorem spec_i₂_alg : Spec.map (i₂ A B) ≫ Spec.map (alg A B) = Spec.map (alg A B ≫ i₁ A B) := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (algebraMap_i₁_eq_i₂ A B).symm

theorem fac {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ Spec (.of B))
    (h : f₁ ≫ Spec.map (alg A B) = f₂ ≫ Spec.map (alg A B)) :
    ∃ l : Y ⟶ Spec (R₂ A B), l ≫ Spec.map (i₁ A B) = f₁ ∧ l ≫ Spec.map (i₂ A B) = f₂ := by
  refine ⟨pullback.lift f₁ f₂ h ≫ (pullbackSpecIso A B B).hom, ?_, ?_⟩
  · have e : i₁ A B = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := rfl
    rw [Category.assoc, e, pullbackSpecIso_hom_fst, pullback.lift_fst]
  · have e : i₂ A B = CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B))) := rfl
    rw [Category.assoc, e, pullbackSpecIso_hom_snd, pullback.lift_snd]

theorem h₀₁ : Spec.map (c₂₃ A B) ≫ Spec.map (i₁ A B) = Spec.map (c₁₂ A B) ≫ Spec.map (i₂ A B) := by
  rw [← Spec.map_comp, ← Spec.map_comp, i₂_c₁₂]

theorem h₁₁ : Spec.map (c₁₃ A B) ≫ Spec.map (i₁ A B) = Spec.map (c₁₂ A B) ≫ Spec.map (i₁ A B) := by
  rw [← Spec.map_comp, ← Spec.map_comp, i₁_c₁₂]

theorem h₁₂ : Spec.map (c₁₃ A B) ≫ Spec.map (i₂ A B) = Spec.map (c₂₃ A B) ≫ Spec.map (i₂ A B) := by
  rw [← Spec.map_comp, ← Spec.map_comp, i₂_c₁₃]

variable {A B}

theorem cocycle_of_plain (N : ModuleCat.{u} (CommRingCat.of B))
    (χ : (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map (i₁ A B))).obj (tilde N) ⟶
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map (i₂ A B))).obj (tilde N))
    (hcoc : ((pullbackComp (Spec.map (c₁₂ A B)) (Spec.map (i₁ A B))).inv.app _ ≫
        (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map (c₁₂ A B))).map χ ≫
          (pullbackComp (Spec.map (c₁₂ A B)) (Spec.map (i₂ A B))).hom.app _) ≫
      ((pullbackCongr (h₀₁ A B)).inv.app _ ≫ (pullbackComp (Spec.map (c₂₃ A B)) (Spec.map (i₁ A
        B))).inv.app _ ≫
        (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map (c₂₃ A B))).map χ ≫
          (pullbackComp (Spec.map (c₂₃ A B)) (Spec.map (i₂ A B))).hom.app _) =
      (pullbackCongr (h₁₁ A B)).inv.app _ ≫ (pullbackComp (Spec.map (c₁₃ A B)) (Spec.map (i₁ A
        B))).inv.app _ ≫
        (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map (c₁₃ A B))).map χ ≫
          (pullbackComp (Spec.map (c₁₃ A B)) (Spec.map (i₂ A B))).hom.app _ ≫
        (pullbackCongr (h₁₂ A B)).hom.app _)
    (ψ : (ModuleCat.extendScalars (i₁ A B).hom).obj N ⟶ (ModuleCat.extendScalars (i₂ A B).hom).obj
      N)
    (hψ : (tilde.pullbackSpecIso (i₁ A B) N).hom ≫ tilde.map ψ = χ ≫ (tilde.pullbackSpecIso (i₂ A
      B) N).hom) :
    Cocycle (A := A) (B := B) N ψ := by
  have F₁₂ := tilde_face χ ψ hψ (c₁₂ A B)
  have F₂₃ := tilde_face χ ψ hψ (c₂₃ A B)
  have F₁₃ := tilde_face χ ψ hψ (c₁₃ A B)
  revert hcoc F₁₂ F₂₃ F₁₃
  generalize h₀₁ A B = E₀₁
  generalize h₁₁ A B = E₁₁
  generalize h₁₂ A B = E₁₂
  generalize (Spec.map_comp (i₁ A B) (c₁₂ A B)).symm = E₁
  generalize (Spec.map_comp (i₂ A B) (c₁₂ A B)).symm = E₂
  generalize (Spec.map_comp (i₁ A B) (c₂₃ A B)).symm = E₃
  generalize (Spec.map_comp (i₂ A B) (c₂₃ A B)).symm = E₄
  generalize (Spec.map_comp (i₁ A B) (c₁₃ A B)).symm = E₅
  generalize (Spec.map_comp (i₂ A B) (c₁₃ A B)).symm = E₆
  intro hcoc F₁₂ F₂₃ F₁₃
  have e₁ := i₂_c₁₂ A B
  have e₂ := i₁_c₁₂ A B
  have e₃ := i₂_c₁₃ A B
  rw [F₁₂, F₂₃, reassoc_of% F₁₃] at hcoc
  clear F₁₂ F₂₃ F₁₃
  simp only [Category.assoc, pullbackCongr_hom_app, pullbackCongr_inv_app, eqToHom_trans_assoc]
    at hcoc
  rw [pullbackSpecIso_hom_eq e₁ N (by rw [e₁]) (by rw [e₁]),
    pullbackSpecIso_hom_eq e₂ N (by rw [e₂]) (by rw [e₂]),
    pullbackSpecIso_inv_eq e₃.symm N (by rw [e₃]) (by rw [e₃])] at hcoc
  revert hcoc
  generalize tilde.pullbackSpecIso (i₁ A B ≫ c₁₂ A B) N = B₁
  generalize tilde.pullbackSpecIso (i₂ A B ≫ c₁₂ A B) N = B₂
  generalize tilde.pullbackSpecIso (i₂ A B ≫ c₂₃ A B) N = B₃
  intro hcoc
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc] at hcoc
  simp only [Category.assoc, eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc,
    ← tilde.map_comp_assoc] at hcoc
  dsimp only [CommRingCat.hom_comp, Functor.comp_obj] at hcoc
  rw [eqToHom_comp_iff] at hcoc
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hcoc
  simp only [← Category.assoc] at hcoc
  rw [comp_eqToHom_iff] at hcoc
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hcoc
  rw [cancel_epi] at hcoc
  simp only [← Category.assoc] at hcoc
  rw [cancel_mono] at hcoc
  simp only [Category.assoc] at hcoc
  have key := (tilde.fullyFaithfulFunctor (R := R₃ A B)).map_injective hcoc
  dsimp only [tilde.functor] at key
  erw [eqToHom_refl, eqToHom_refl, eqToHom_refl] at key
  erw [Category.id_comp, Category.id_comp, Category.comp_id] at key
  unfold Algebra.DescentCofaces.Cocycle Algebra.DescentCofaces.T
  let a := (ModuleCat.extendScalarsComp (i₁ A B).hom (c₁₂ A B).hom).hom.app N
  let b := (ModuleCat.extendScalars (c₁₂ A B).hom).map ψ
  let c := (ModuleCat.extendScalarsComp (i₂ A B).hom (c₁₂ A B).hom).inv.app N
  let d := (ModuleCat.extendScalarsComp (i₁ A B).hom (c₂₃ A B).hom).hom.app N
  let e := (ModuleCat.extendScalars (c₂₃ A B).hom).map ψ
  let f := (ModuleCat.extendScalarsComp (i₂ A B).hom (c₂₃ A B).hom).inv.app N
  exact (Category.assoc a (b ≫ c) (d ≫ e ≫ f)).trans
    ((congrArg (fun z => a ≫ z) (Category.assoc b c (d ≫ e ≫ f))).trans key)

private theorem comm_of_square_generic
    {R S T : CommRingCat.{u}} (α : R ⟶ S) (j₁ j₂ : S ⟶ T)
    (e : α ≫ j₁ = α ≫ j₂)
    (h : Spec.map j₁ ≫ Spec.map α = Spec.map j₂ ≫ Spec.map α) (N : ModuleCat.{u} S) (M :
      ModuleCat.{u} R)
    (χ : (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map j₁)).obj (tilde N) ⟶
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map j₂)).obj (tilde N))
    (ψ : (ModuleCat.extendScalars j₁.hom).obj N ⟶ (ModuleCat.extendScalars j₂.hom).obj N)
    (hψ : (tilde.pullbackSpecIso j₁ N).hom ≫ tilde.map ψ = χ ≫ (tilde.pullbackSpecIso j₂ N).hom)
    (θ : (ModuleCat.extendScalars α.hom).obj M ⟶ N)
    (hsq : (ModuleCat.extendScalars j₁.hom).map θ ≫ ψ =
      ((ModuleCat.extendScalarsComp α.hom j₁.hom).inv.app M ≫
        eqToHom (congrArg (fun f : R →+* T => (ModuleCat.extendScalars f).obj M)
          (congrArg CommRingCat.Hom.hom e)) ≫
        (ModuleCat.extendScalarsComp α.hom j₂.hom).hom.app M) ≫ (ModuleCat.extendScalars
          j₂.hom).map θ) :
    (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map j₁)).map ((tilde.pullbackSpecIso α
      M).hom ≫ tilde.map θ) ≫ χ =
      ((pullbackComp (Spec.map j₁) (Spec.map α)).hom.app (tilde M) ≫
        (pullbackCongr h).hom.app (tilde M) ≫
        (pullbackComp (Spec.map j₂) (Spec.map α)).inv.app (tilde M)) ≫
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map j₂)).map ((tilde.pullbackSpecIso
        α M).hom ≫ tilde.map θ) := by
  have C₁ := tilde.pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom α j₁ M
  have C₂ := tilde.pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom α j₂ M
  have N₁ := tilde.pullbackSpecIso_hom_naturality j₁ θ
  have N₂ := tilde.pullbackSpecIso_hom_naturality j₂ θ
  dsimp only [CommRingCat.hom_comp] at C₁ C₂ N₁ N₂ ⊢
  dsimp only [tilde.functor] at C₁ C₂ N₁ N₂ ⊢
  have L := pullbackSpecIso_hom_tilde_map_eqToHom_comp e M (by rw [e]) (by rw [e])
    ((ModuleCat.extendScalarsComp α.hom j₂.hom).hom.app M ≫
      (ModuleCat.extendScalars j₂.hom).map θ)
  revert hψ hsq C₁ C₂ N₁ N₂ L
  generalize h = E₀
  generalize (Spec.map_comp α j₁).symm = E₁
  generalize (Spec.map_comp α j₂).symm = E₂
  generalize e = E₃
  generalize tilde.pullbackSpecIso α M = Bα
  generalize tilde.pullbackSpecIso j₁ N = B₁
  generalize tilde.pullbackSpecIso j₂ N = B₂
  generalize tilde.pullbackSpecIso j₁ ((ModuleCat.extendScalars α.hom).obj M) = B₁'
  generalize tilde.pullbackSpecIso j₂ ((ModuleCat.extendScalars α.hom).obj M) = B₂'
  generalize tilde.pullbackSpecIso (α ≫ j₁) M = Bα₁
  generalize tilde.pullbackSpecIso (α ≫ j₂) M = Bα₂
  intro hψ hsq C₁ C₂ N₁ N₂ L
  rw [← cancel_mono B₂.hom]
  simp only [Category.assoc, Functor.map_comp]
  rw [← hψ, ← Category.assoc ((Scheme.Modules.pullback (Spec.map j₁)).map (tilde.map θ))]
  erw [N₁, Category.assoc, reassoc_of% C₁]
  rw [← tilde.map_comp ((ModuleCat.extendScalars j₁.hom).map θ) ψ, hsq]
  erw [N₂, reassoc_of% C₂]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [cancel_epi]
  rw [← tilde.map_comp ((ModuleCat.extendScalarsComp α.hom j₁.hom).hom.app M)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← tilde.map_comp ((ModuleCat.extendScalarsComp α.hom j₂.hom).hom.app M), L]
  rewrite [pullbackCongr_hom_app, eqToHom_trans_assoc, eqToHom_comp_iff]
  simp only [pullbackCongr_hom_app, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

theorem comm_of_square (N : ModuleCat.{u} (CommRingCat.of B)) (M : ModuleCat.{u} (CommRingCat.of A))
    (χ : (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map (i₁ A B))).obj (tilde N) ⟶
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map (i₂ A B))).obj (tilde N))
    (ψ : (ModuleCat.extendScalars (i₁ A B).hom).obj N ⟶ (ModuleCat.extendScalars (i₂ A B).hom).obj
      N)
    (hψ : (tilde.pullbackSpecIso (i₁ A B) N).hom ≫ tilde.map ψ = χ ≫ (tilde.pullbackSpecIso (i₂ A
      B) N).hom)
    (θ : (ModuleCat.extendScalars (algebraMap A B)).obj M ⟶ N)
    (hsq : (ModuleCat.extendScalars (i₁ A B).hom).map θ ≫ ψ =
      canonical A B M ≫ (ModuleCat.extendScalars (i₂ A B).hom).map θ) :
    (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map (i₁ A B))).map
      ((tilde.pullbackSpecIso (alg A B) M).hom ≫ tilde.map θ) ≫ χ =
      ((pullbackComp (Spec.map (i₁ A B)) (Spec.map (alg A B))).hom.app (tilde M) ≫
        (pullbackCongr ((spec_i₁_alg A B).trans (spec_i₂_alg A B).symm)).hom.app (tilde M) ≫
        (pullbackComp (Spec.map (i₂ A B)) (Spec.map (alg A B))).inv.app (tilde M)) ≫
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map (i₂ A B))).map
        ((tilde.pullbackSpecIso (alg A B) M).hom ≫ tilde.map θ) := by
  exact comm_of_square_generic (alg A B) (i₁ A B) (i₂ A B)
    (algebraMap_i₁_eq_i₂ A B) ((spec_i₁_alg A B).trans (spec_i₂_alg A B).symm)
    N M χ ψ hψ θ hsq

theorem isInvertible_tilde_of_invertible (M : Type u) [AddCommGroup M] [Module A M]
  [Module.Invertible A M] :
    IsInvertible (tilde (ModuleCat.of (CommRingCat.of A) M)) := by
  have : Module.Finite (CommRingCat.of A) (ModuleCat.of (CommRingCat.of A) M) :=
    inferInstanceAs (Module.Finite A M)
  have : Module.Projective (CommRingCat.of A) (ModuleCat.of (CommRingCat.of A) M) :=
    inferInstanceAs (Module.Projective A M)
  refine isInvertible_tilde_of_projective_rankOne (R := CommRingCat.of A) (ModuleCat.of
    (CommRingCat.of A) M)
    (fun K _ _ => ?_)
  have : Module.Invertible K (K ⊗[A] M) := inferInstance
  exact Module.Invertible.finrank_eq_one K (K ⊗[A] M)

private theorem _root_.Module.Invertible.of_bijective_algebraMap {R S : Type*} [CommRing R]
  [CommRing S] [Algebra R S]
    (hRS : Function.Bijective (algebraMap R S)) (P : Type*) [AddCommGroup P] [Module R P] [Module S
      P]
    [IsScalarTower R S P] [Module.Invertible R P] : Module.Invertible S P := by
  have : IsLocalization (IsUnit.submonoid R) S :=
    IsLocalization.of_le_isUnit_of_bijective Algebra.algebraMapSubmonoid_isUnit_le hRS
  have : IsLocalizedModule (IsUnit.submonoid R) (LinearMap.id : P →ₗ[R] P) :=
    isLocalizedModule_id (IsUnit.submonoid R) P S
  exact Module.Invertible.of_isLocalization (IsUnit.submonoid R) (LinearMap.id : P →ₗ[R] P)
alias Module.Invertible.of_bijective_algebraMap := _root_.Module.Invertible.of_bijective_algebraMap

theorem moduleSpecΓFunctor_smul_eq (L : (Spec (CommRingCat.of B)).Modules) (b : B)
    (m : (moduleSpecΓFunctor (R := CommRingCat.of B)).obj L) :
    b • m = (show Γ(L, ⊤) from
      (show Γ(Spec (CommRingCat.of B), ⊤) from (StructureSheaf.globalSectionsIso (CommRingCat.of
        B)).hom.hom b) •
        (show Γ(L, ⊤) from m)) := by
  change (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso (CommRingCat.of
    B)).hom.hom).obj _ at m
  erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]

theorem invertible_sections (L : (Spec (CommRingCat.of B)).Modules) (hL : IsInvertible L) :
    Module.Invertible B ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L) := by
  have := projective_sections_of_locallyTrivial L hL.1 ⟨⊤, isAffineOpen_top _⟩
  have := finite_sections_of_locallyTrivial L hL.1 ⟨⊤, isAffineOpen_top _⟩
  have hInv : Module.Invertible Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens))
    Γ(L, ⊤) :=
    Module.Invertible.of_projective_of_forall_finrank_eq_one _
      (fun K _ _ => finrank_baseChange_sections_eq_one_of_locallyTrivial L hL.1 ⟨⊤,
        isAffineOpen_top _⟩ K)
  let e : B ≃+* Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens)) :=
    (StructureSheaf.globalSectionsIso (CommRingCat.of B)).commRingCatIsoToRingEquiv
  have smul_eq : ∀ (b : B) (m : (moduleSpecΓFunctor (R := CommRingCat.of B)).obj L),
      b • m = (show Γ(L, ⊤) from e b • (show Γ(L, ⊤) from m)) := fun b m =>
    moduleSpecΓFunctor_smul_eq L b m
  let : Module Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens))
      ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L) :=
    show Module Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens)) Γ(L, ⊤) from
      inferInstance
  have : Module.Invertible Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens))
      ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L) := hInv
  let : Algebra Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens)) B :=
    e.symm.toRingHom.toAlgebra
  have : IsScalarTower Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens)) B
      ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L) := by
    refine ⟨fun r b m => ?_⟩
    change e (e.symm r * b) • (show Γ(L, ⊤) from m) =
      r • (e b • (show Γ(L, ⊤) from m))
    rw [map_mul, RingEquiv.apply_symm_apply, mul_smul]
  refine Module.Invertible.of_bijective_algebraMap
    (R := Γ(Spec (CommRingCat.of B), (⊤ : (Spec (.of B)).Opens))) ?_ _
  rw [RingHom.algebraMap_toAlgebra]
  exact e.symm.bijective

theorem core [Module.FaithfullyFlat A B]
    (D : MOD.DescentData (fun _ : Unit => Spec.map (alg A B)))
    (N : Type u) [AddCommGroup N] [moduleB : Module B N] [Module A N] [IsScalarTower A B N]
    (ε : tilde (ModuleCat.of (CommRingCat.of B) N) ≅ D.obj ()) (hN : Module.Invertible B N) :
    ∃ L : (Spec (CommRingCat.of A)).Modules, IsInvertible L ∧
      Nonempty ((MOD.toDescentData (fun _ : Unit => Spec.map (alg A B))).obj L ≅ D) := by
  let D' := D.changeObj (fun _ => tilde (ModuleCat.of (CommRingCat.of B) N)) (fun _ => ε)
  suffices h : ∃ L : (Spec (CommRingCat.of A)).Modules, IsInvertible L ∧
      Nonempty ((MOD.toDescentData (fun _ : Unit => Spec.map (alg A B))).obj L ≅ D') by
    obtain ⟨L, hL, ⟨e⟩⟩ := h
    exact ⟨L, hL, ⟨e ≪≫ D.changeObjIso _ _⟩⟩
  let χ : (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map (i₁ A B))).obj (tilde
    (ModuleCat.of (CommRingCat.of B) N)) ⟶
      (_root_.AlgebraicGeometry.Scheme.Modules.pullback (Spec.map (i₂ A B))).obj (tilde
        (ModuleCat.of (CommRingCat.of B) N)) :=
    ddHom D' (Spec.map (alg A B ≫ i₁ A B)) (Spec.map (i₁ A B)) (Spec.map (i₂ A B))
      (spec_i₁_alg A B) (spec_i₂_alg A B)
  have : IsIso χ := isIso_ddHom D' (Spec.map (alg A B ≫ i₁ A B)) (Spec.map (i₁ A B)) (Spec.map (i₂
    A B))
    (spec_i₁_alg A B) (spec_i₂_alg A B)
  obtain ⟨φ', hψ⟩ : ∃ φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj (ModuleCat.of (CommRingCat.of
    B) N) ≅
      (ModuleCat.extendScalars (i₂ A B).hom).obj (ModuleCat.of (CommRingCat.of B) N),
      (tilde.pullbackSpecIso (i₁ A B) (ModuleCat.of (CommRingCat.of B) N)).hom ≫ tilde.map φ'.hom =
        χ ≫ (tilde.pullbackSpecIso (i₂ A B) (ModuleCat.of (CommRingCat.of B) N)).hom := by
    let eχ : tilde ((ModuleCat.extendScalars (i₁ A B).hom).obj (ModuleCat.of (CommRingCat.of B) N))
      ≅
        tilde ((ModuleCat.extendScalars (i₂ A B).hom).obj (ModuleCat.of (CommRingCat.of B) N)) :=
      (tilde.pullbackSpecIso (i₁ A B) (ModuleCat.of (CommRingCat.of B) N)).symm ≪≫ asIso χ ≪≫
        tilde.pullbackSpecIso (i₂ A B) (ModuleCat.of (CommRingCat.of B) N)
    refine ⟨(tilde.fullyFaithfulFunctor (R := R₂ A B)).preimageIso eχ, ?_⟩
    have hmap : (tilde.functor (R₂ A B)).map ((tilde.fullyFaithfulFunctor (R := R₂ A
      B)).preimageIso eχ).hom = eχ.hom := by
      exact (tilde.fullyFaithfulFunctor (R := R₂ A B)).map_preimage eχ.hom
    simp only [tilde.functor_map] at hmap
    rw [hmap]
    simp only [eχ, Iso.trans_hom, Iso.symm_hom, asIso_hom, Iso.hom_inv_id_assoc]
  have hcoc : Cocycle (ModuleCat.of (CommRingCat.of B) N) φ'.hom :=
    cocycle_of_plain (ModuleCat.of (CommRingCat.of B) N) χ
      (ddHom_cocycle' D' (M := tilde (ModuleCat.of (CommRingCat.of B) N)) rfl _ _ _
        (spec_i₁_alg A B) (spec_i₂_alg A B) (Spec.map (c₂₃ A B)) (Spec.map (c₁₃ A B)) (Spec.map
          (c₁₂ A B))
        (h₀₁ A B) (h₁₁ A B) (h₁₂ A B) χ HEq.rfl)
      φ'.hom hψ
  obtain ⟨M, -, -, ⟨θ, -, hsq⟩, hinv⟩ :=
    Module.FaithfullyFlat.exists_submodule_isBaseChange_of_cocycle N φ' hcoc
  have : Module.Invertible A M := hinv hN
  refine ⟨tilde (ModuleCat.of (CommRingCat.of A) M), isInvertible_tilde_of_invertible (A := A) M,
    ?_⟩
  refine nonempty_toDescentData_iso' D' (M := tilde (ModuleCat.of (CommRingCat.of B) N)) rfl
    (tilde (ModuleCat.of (CommRingCat.of A) M))
    ((tilde.pullbackSpecIso (alg A B) (ModuleCat.of (CommRingCat.of A) M)) ≪≫ (tilde.functor
      _).mapIso θ)
    (Spec.map (alg A B ≫ i₁ A B)) (Spec.map (i₁ A B)) (Spec.map (i₂ A B)) (spec_i₁_alg A B)
      (spec_i₂_alg A B)
    (fun Y f₁ f₂ h => fac A B f₁ f₂ h) χ HEq.rfl ?_
  exact comm_of_square (ModuleCat.of (CommRingCat.of B) N) (ModuleCat.of (CommRingCat.of A) M) χ
    φ'.hom hψ θ.hom hsq

end AffineInvertibleDescent

theorem affine_case {Y Y' : Scheme.{u}} [IsAffine Y] (q : Y' ⟶ Y) [IsAffineHom q] [Flat q]
  [Surjective q]
    (D : MOD.DescentData (fun _ : Unit => q)) (hD : ∀ i, IsInvertible (D.obj i)) :
    ∃ L : Y.Modules, IsInvertible L ∧ Nonempty ((MOD.toDescentData (fun _ : Unit => q)).obj L ≅ D)
      := by
  have : IsAffine Y' := isAffine_of_isAffineHom q
  let : Algebra Γ(Y, ⊤) Γ(Y', ⊤) := q.appTop.hom.toAlgebra
  have : Module.FaithfullyFlat Γ(Y, ⊤) Γ(Y', ⊤) :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).mp ⟨inferInstance, inferInstance⟩
  refine CategoryTheory.Pseudofunctor.DescentData.exists_iso_toDescentData_of_arrow_iso
    (F := MOD)
    (fun _ M => IsInvertible M) (fun _ _ g M hM => hM.pullback g)
    (q₀ := Spec.map (AffineInvertibleDescent.alg Γ(Y, ⊤) Γ(Y', ⊤))) Y.isoSpec Y'.isoSpec ?_ ?_ D hD
  · exact Scheme.isoSpec_hom_naturality q
  intro D₀ hD₀
  let L₀ : (Spec (CommRingCat.of Γ(Y', ⊤))).Modules := D₀.obj ()
  let N₀ : ModuleCat (CommRingCat.of Γ(Y', ⊤)) :=
    (moduleSpecΓFunctor (R := CommRingCat.of Γ(Y', ⊤))).obj L₀
  have : IsIso L₀.fromTildeΓ := isIso_fromTildeGamma_of_locallyTrivial L₀ (hD₀ ()).1
  let e₀ := asIso L₀.fromTildeΓ
  let : Module Γ(Y', ⊤) N₀ := N₀.isModule
  let : Module Γ(Y, ⊤) N₀ := Module.compHom N₀ (algebraMap Γ(Y, ⊤) Γ(Y', ⊤))
  have : IsScalarTower Γ(Y, ⊤) Γ(Y', ⊤) N₀ := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact AffineInvertibleDescent.core (A := Γ(Y, ⊤)) (B := Γ(Y', ⊤))
    (moduleB := N₀.isModule) D₀ N₀ e₀ (AffineInvertibleDescent.invertible_sections L₀ (hD₀ ()))

end AlgebraicGeometry.Scheme.Modules

end AlgebraicCurves.Geometry.Sheaves.Proofs.InvertibleAffineDescent

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open InvertibleAffineDescent.AlgebraicGeometry.Scheme.Modules in
theorem exists_iso_toDescentData_of_isAffine_of_isAffineHom_of_flat_of_surjective
    {Y Y' : Scheme.{u}} [IsAffine Y] (q : Y' ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (D : ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData (fun _ : Unit
      => q))
    (hD : ∀ i, Scheme.Modules.IsInvertible (D.obj i)) :
    ∃ L : Y.Modules, Scheme.Modules.IsInvertible L ∧
      Nonempty ((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).obj L ≅ D) :=
  affine_case q D hD
end AlgebraicGeometry.Scheme.Modules.IsInvertible
end ProofImplementation

attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul
  Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul
