/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_toDescentData_map_bijective_of_openCover
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Bicategory.Functor.Cat
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Forget
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Sites.Sieves.Basic
import Mathlib.CategoryTheory.Sites.Sieves.Presieve
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Set.Image
import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.Order.Lattice
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Choose
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
Effectivity of descent data for sheaves of scheme modules on an open cover.
Compatible local sections form the glued sheaf and recover the prescribed transitions.
-/

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_toDescentData_map_bijective_of_openCover.AlgebraicGeometry.Scheme.Modules.HomZar


section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_toDescentData_essSurj_of_openCover

universe v v' u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace


namespace CategoryTheory
open _root_.CategoryTheory
namespace Pseudofunctor
open _root_.CategoryTheory.Pseudofunctor
namespace LocallyDiscreteOpToCat
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open _root_.CategoryTheory.Pseudofunctor
open _root_.CategoryTheory

variable {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}

theorem pullHom_comp' ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃M₃ :
    F.obj (.mk (op X₃))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (b : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (h₃ : g ≫ f₃ = gf₃) :
    pullHom (a ≫ b) g gf₁ gf₃ h₁ h₃ = pullHom a g gf₁ gf₂ h₁ h₂ ≫ pullHom b g gf₂ gf₃ h₂ h₃ := by
  simp [pullHom, Functor.map_comp]

theorem map_map_eq_pullHom ⦃X Y : C⦄ (f : Y ⟶ X) ⦃M N : F.obj (.mk (op X))⦄ (ψ : M ⟶ N) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf : Y' ⟶ X) (hgf : g ≫ f = gf) :
    (F.map gf.op.toLoc).toFunctor.map ψ = pullHom ((F.map f.op.toLoc).toFunctor.map ψ) g gf gf hgf
      hgf := by
  dsimp only [pullHom]
  rw [← Category.assoc, ← F.mapComp'_hom_naturality f.op.toLoc g.op.toLoc gf.op.toLoc (
    by rw [← hgf]; rfl) ψ,
    Category.assoc]
  simp

-- Local proof-performance refinements: Copyright (c) 2026 Naganori Yamaguchi.
-- Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
-- https://github.com/n-yamaguchi-0729
-- Transport an already proved compatibility square through an arbitrary pullback.
private theorem comm_of_pullHom {ι : Type*} {S : C} {X : ι → C}
    {f : ∀ i, X i ⟶ S} (D₁ D₂ : F.DescentData f) {i j : ι}
    (a : D₁.obj i ⟶ D₂.obj i) (b : D₁.obj j ⟶ D₂.obj j)
    {Z₀ Z : C} (q₀ : Z₀ ⟶ S) (g₁ : Z₀ ⟶ X i) (g₂ : Z₀ ⟶ X j)
    (w₁ : g₁ ≫ f i = q₀) (w₂ : g₂ ≫ f j = q₀)
    (comm : (F.map g₁.op.toLoc).toFunctor.map a ≫ D₂.hom q₀ g₁ g₂ w₁ w₂ =
      D₁.hom q₀ g₁ g₂ w₁ w₂ ≫ (F.map g₂.op.toLoc).toFunctor.map b)
    (q : Z ⟶ S) (f₁ : Z ⟶ X i) (f₂ : Z ⟶ X j)
    (h₁ : f₁ ≫ f i = q) (h₂ : f₂ ≫ f j = q)
    (φ : Z ⟶ Z₀) (hφ : φ ≫ q₀ = q) (hφ₁ : φ ≫ g₁ = f₁) (hφ₂ : φ ≫ g₂ = f₂) :
    (F.map f₁.op.toLoc).toFunctor.map a ≫ D₂.hom q f₁ f₂ h₁ h₂ =
      D₁.hom q f₁ f₂ h₁ h₂ ≫ (F.map f₂.op.toLoc).toFunctor.map b := by
  rw [← D₂.pullHom_hom φ q₀ q hφ g₁ g₂ w₁ w₂ f₁ f₂ hφ₁ hφ₂,
    ← D₁.pullHom_hom φ q₀ q hφ g₁ g₂ w₁ w₂ f₁ f₂ hφ₁ hφ₂,
    map_map_eq_pullHom g₁ a φ f₁ hφ₁, map_map_eq_pullHom g₂ b φ f₂ hφ₂,
    ← pullHom_comp', ← pullHom_comp', comm]

-- Construct the comparison while the canonical object's fibers stay abstract.
private noncomputable def canonical_iso {ι : Type*} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) (M : F.obj (.mk (op S))) (D : F.DescentData f)
    (e : ∀ i, (F.map (f i).op.toLoc).toFunctor.obj M ≅ D.obj i)
    (comm : ∀ ⦃Z : C⦄ (q : Z ⟶ S) ⦃i j : ι⦄ (f₁ : Z ⟶ X i) (f₂ : Z ⟶ X j)
      (h₁ : f₁ ≫ f i = q) (h₂ : f₂ ≫ f j = q),
      (F.map f₁.op.toLoc).toFunctor.map (e i).hom ≫ D.hom q f₁ f₂ h₁ h₂ =
        ((F.toDescentData f).obj M).hom q f₁ f₂ h₁ h₂ ≫
          (F.map f₂.op.toLoc).toFunctor.map (e j).hom) : (F.toDescentData f).obj M ≅ D :=
  Pseudofunctor.DescentData.isoMk e (fun _ q _ _ f₁ f₂ h₁ h₂ => comm q f₁ f₂ h₁ h₂)

end CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace ObjGlue
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

/-- The canonical pseudofunctor of scheme modules used by the descent data. -/
noncomputable abbrev MOD : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Mdl.{u}

theorem keyMC {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u' : a ⟶ b) (v' : b ⟶ d) (M : MOD.obj a) :
    (MOD.mapComp' u' v' (u' ≫ v') rfl).hom.toNatTrans.app M = (MOD.mapComp u'
      v').hom.toNatTrans.app M := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem mapComp'_hom_app_eq {X X' Z : Scheme.{u}} (f : X ⟶ X') (g : X' ⟶ Z) (L : Z.Modules) (fg :
    X ⟶ Z) (h : f ≫ g = fg) :
    (MOD.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app L =
    (Scheme.Modules.pullbackCongr h.symm).hom.app L ≫ (Scheme.Modules.pullbackComp f g).inv.app L
      := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  exact keyMC g.op.toLoc f.op.toLoc L


theorem crux_MOD {Z' Z X₁ X₂ : Scheme.{u}} (e : Z' ⟶ Z) (f₁ : Z ⟶ X₁) (f₂ : Z ⟶ X₂)
    (gf₁ : Z' ⟶ X₁) (gf₂ : Z' ⟶ X₂) [IsOpenImmersion e] [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    [IsOpenImmersion gf₁] [IsOpenImmersion gf₂] (h₁ : e ≫ f₁ = gf₁) (h₂ : e ≫ f₂ = gf₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (φ : (MOD.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (MOD.map f₂.op.toLoc).toFunctor.obj M₂) :
    (restrictFunctorIsoPullback gf₁).hom.app M₁ ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := MOD) φ e gf₁ gf₂ h₁ h₂ ≫
        (restrictFunctorIsoPullback gf₂).inv.app M₂ =
      (restrictFunctorCongr h₁.symm).hom.app M₁ ≫ (restrictFunctorComp e f₁).hom.app M₁ ≫
        (restrictFunctor e).map ((restrictFunctorIsoPullback f₁).hom.app M₁ ≫ φ ≫
          (restrictFunctorIsoPullback f₂).inv.app M₂) ≫
        (restrictFunctorComp e f₂).inv.app M₂ ≫ (restrictFunctorCongr h₂).hom.app M₂ :=
  restrictFunctorIsoPullback_conj_pullHom e f₁ f₂ gf₁ gf₂ h₁ h₂ M₁ M₂ φ

section WLOG
variable {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i,
  IsOpenImmersion (g i)]

/-- The opens occurring as ranges of the given family of open immersions. -/
abbrev Ranges : Type u := {O : Y.Opens // ∃ i, (g i).opensRange = O}

theorem sieve_ofArrows_eq_opensRange :
    Sieve.ofArrows _ g = Sieve.ofArrows (fun O : Ranges g => ((O.1 : Y.Opens) : Scheme.{u})) (fun
      O => O.1.ι) := by
  apply le_antisymm
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro Z _ ⟨i⟩
    exact ⟨_, (g i).isoOpensRange.hom, (⟨(g i).opensRange, i, rfl⟩ : Ranges g).1.ι,
      Presieve.ofArrows.mk (⟨(g i).opensRange, i, rfl⟩ : Ranges g), (g i).isoOpensRange_hom_ι⟩
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro Z _ ⟨O⟩
    obtain ⟨O, i, rfl⟩ := O
    exact ⟨_, (g i).isoOpensRange.inv, g i, Presieve.ofArrows.mk i, (g i).isoOpensRange_inv_comp⟩
omit [∀ i, IsOpenImmersion (g i)] in
theorem essSurj_iff_of_sieve_eq {ι' : Type v'} {V' : ι' → Scheme.{u}} (g' : ∀ i, V' i ⟶ Y)
    (h : Sieve.ofArrows _ g = Sieve.ofArrows _ g') :
    (MOD.toDescentData g).EssSurj ↔ (MOD.toDescentData g').EssSurj := by
  obtain ⟨e, ⟨iso⟩⟩ := Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq MOD g g' h
  constructor
  · intro _
    have : (MOD.toDescentData g ⋙ e.functor).EssSurj := Functor.essSurj_comp _ _
    exact Functor.essSurj_of_iso iso
  · intro _
    have : (MOD.toDescentData g ⋙ e.functor).EssSurj := Functor.essSurj_of_iso iso.symm
    exact Functor.essSurj_of_comp_fully_faithful _ e.functor

end WLOG

section Opens
variable {Y : Scheme.{u}} {ι : Type u} (U : ι → Y.Opens)

/-- The inclusion of an open from the covering family into the ambient scheme. -/
abbrev incl (i : ι) : (U i : Scheme.{u}) ⟶ Y := (U i).ι

/-- The inclusion of a pairwise intersection into its first covering open. -/
noncomputable abbrev p₁ (i j : ι) : ((U i ⊓ U j : Y.Opens) : Scheme.{u}) ⟶ (U i : Scheme.{u}) :=
  Y.homOfLE inf_le_left
/-- The inclusion of a pairwise intersection into its second covering open. -/
noncomputable abbrev p₂ (i j : ι) : ((U i ⊓ U j : Y.Opens) : Scheme.{u}) ⟶ (U j : Scheme.{u}) :=
  Y.homOfLE inf_le_right

variable (D : (MOD.{u}).DescentData (incl U))

/-- The module attached to a covering open by the given descent datum. -/
noncomputable abbrev Dobj (i : ι) : ((U i : Y.Opens) : Scheme.{u}).Modules := D.obj i

theorem D_pullHom ⦃Z Z' : Scheme.{u}⦄ (φ : Z' ⟶ Z) (q : Z ⟶ Y) (q' : Z' ⟶ Y) (hq : φ ≫ q = q') ⦃i
    j : ι⦄
    (f₁ : Z ⟶ (U i : Scheme.{u})) (f₂ : Z ⟶ (U j : Scheme.{u})) (hf₁ : f₁ ≫ incl U i = q) (hf₂ :
      f₂ ≫ incl U j = q)
    (g₁ : Z' ⟶ (U i : Scheme.{u})) (g₂ : Z' ⟶ (U j : Scheme.{u})) (hg₁ : φ ≫ f₁ = g₁) (hg₂ : φ ≫
      f₂ = g₂)
    (hg₁' : g₁ ≫ incl U i = q') (hg₂' : g₂ ≫ incl U j = q') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (D.hom q f₁ f₂ hf₁ hf₂) φ g₁ g₂ hg₁ hg₂ =
      D.hom q' g₁ g₂ hg₁' hg₂' :=
  D.pullHom_hom φ q q' hq f₁ f₂ hf₁ hf₂ g₁ g₂ hg₁ hg₂

theorem ofObj_pullHom (M : Y.Modules) ⦃Z Z' : Scheme.{u}⦄ (φ : Z' ⟶ Z) (q : Z ⟶ Y) (q' : Z' ⟶ Y)
    (hq : φ ≫ q = q')
    ⦃i j : ι⦄ (f₁ : Z ⟶ (U i : Scheme.{u})) (f₂ : Z ⟶ (U j : Scheme.{u})) (hf₁ : f₁ ≫ incl U i = q)
    (hf₂ : f₂ ≫ incl U j = q) (g₁ : Z' ⟶ (U i : Scheme.{u})) (g₂ : Z' ⟶ (U j : Scheme.{u})) (hg₁ :
      φ ≫ f₁ = g₁)
    (hg₂ : φ ≫ f₂ = g₂) (hg₁' : g₁ ≫ incl U i = q') (hg₂' : g₂ ≫ incl U j = q') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (((MOD.toDescentData (incl U)).obj M).hom q f₁ f₂
      hf₁ hf₂) φ g₁ g₂
        hg₁ hg₂ = ((MOD.toDescentData (incl U)).obj M).hom q' g₁ g₂ hg₁' hg₂' :=
  D_pullHom U ((MOD.toDescentData (incl U)).obj M) φ q q' hq f₁ f₂ hf₁ hf₂ g₁ g₂ hg₁ hg₂ hg₁' hg₂'

theorem ofObj_hom_eq (M : Y.Modules) ⦃Z : Scheme.{u}⦄ (q : Z ⟶ Y) ⦃i j : ι⦄
    (f₁ : Z ⟶ (U i : Scheme.{u})) (f₂ : Z ⟶ (U j : Scheme.{u}))
    (hf₁ : f₁ ≫ incl U i = q) (hf₂ : f₂ ≫ incl U j = q) {N : Z.Modules}
    (φ : (Modules.pullback f₂).obj ((Modules.pullback (incl U j)).obj M) ⟶ N) :
    @Eq (_root_.AlgebraicGeometry.Scheme.Modules.Hom
      (X := Z)
      ((Modules.pullback f₁).obj ((Modules.pullback (incl U i)).obj M)) N)
      (((MOD.toDescentData (incl U)).obj M).hom q f₁ f₂ hf₁ hf₂ ≫ φ)
      ((((Scheme.Modules.pullbackComp f₁ (incl U i)).hom.app M ≫
          (Scheme.Modules.pullbackCongr hf₁).hom.app M) ≫
        (Scheme.Modules.pullbackCongr hf₂.symm).hom.app M ≫
        (Scheme.Modules.pullbackComp f₂ (incl U j)).inv.app M) ≫ φ) := by
  rw [← Mdl_mapComp'_inv_app f₁ (incl U i) M q hf₁, ← Mdl_mapComp'_hom_app f₂ (incl U j) M q hf₂]
  rfl

/-- The inclusion of a smaller open into a specified covering open. -/
noncomputable abbrev incO (i : ι) (O : Y.Opens) (h : O ≤ U i) : (O : Scheme.{u}) ⟶ (U i :
  Scheme.{u}) := Y.homOfLE h

theorem incO_comp (i : ι) {O O' : Y.Opens} (hO' : O' ≤ O) (hi : O ≤ U i) :
    Y.homOfLE hO' ≫ incO U i O hi = incO U i O' (hO'.trans hi) :=
  Scheme.homOfLE_homOfLE Y hO' hi

/-- The descent transition expressed through the restriction--pullback comparisons. -/
noncomputable def τ (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) :
    (Dobj U D i).restrict (incO U i O hi) ≅ (Dobj U D j).restrict (incO U j O hj) :=
  (restrictFunctorIsoPullback (incO U i O hi)).app (Dobj U D i) ≪≫
    D.iso O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) ≪≫
    ((restrictFunctorIsoPullback (incO U j O hj)).app (Dobj U D j)).symm

/-- The descent transition on the intersection of two covering opens. -/
noncomputable abbrev ρ (i j : ι) : (Dobj U D i).restrict (p₁ U i j) ≅ (Dobj U D j).restrict (p₂ U
  i j) :=
  τ U D i j (U i ⊓ U j) inf_le_left inf_le_right

theorem τ_self (i : ι) (O : Y.Opens) (hi : O ≤ U i) :
    (τ U D i i O hi hi).hom = 𝟙 ((Dobj U D i).restrict (incO U i O hi)) := by
  let e : (Dobj U D i).restrict (incO U i O hi) ≅
      (Modules.pullback (incO U i O hi)).obj (Dobj U D i) :=
    (restrictFunctorIsoPullback (incO U i O hi)).app (Dobj U D i)
  let d : (Modules.pullback (incO U i O hi)).obj (Dobj U D i) ≅
      (Modules.pullback (incO U i O hi)).obj (Dobj U D i) :=
    D.iso O.ι (incO U i O hi) (incO U i O hi) (Y.homOfLE_ι hi) (Y.homOfLE_ι hi)
  have h : d.hom = 𝟙 ((Modules.pullback (incO U i O hi)).obj (Dobj U D i)) :=
    D.hom_self O.ι (incO U i O hi) (Y.homOfLE_ι hi)
  change (e ≪≫ d ≪≫ e.symm).hom = 𝟙 _
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [h, Category.id_comp]
  exact e.hom_inv_id

theorem ρ_self (i : ι) : (ρ U D i i).hom = 𝟙 ((Dobj U D i).restrict (p₁ U i i)) := τ_self U D i _ _

theorem τ_comp (i j k : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (hk : O ≤ U k) :
    (τ U D i j O hi hj).hom ≫ (τ U D j k O hj hk).hom = (τ U D i k O hi hk).hom := by
  let ei : (Dobj U D i).restrict (incO U i O hi) ≅
      (Modules.pullback (incO U i O hi)).obj (Dobj U D i) :=
    (restrictFunctorIsoPullback (incO U i O hi)).app (Dobj U D i)
  let ej : (Dobj U D j).restrict (incO U j O hj) ≅
      (Modules.pullback (incO U j O hj)).obj (Dobj U D j) :=
    (restrictFunctorIsoPullback (incO U j O hj)).app (Dobj U D j)
  let ek : (Dobj U D k).restrict (incO U k O hk) ≅
      (Modules.pullback (incO U k O hk)).obj (Dobj U D k) :=
    (restrictFunctorIsoPullback (incO U k O hk)).app (Dobj U D k)
  let dij : (Modules.pullback (incO U i O hi)).obj (Dobj U D i) ≅
      (Modules.pullback (incO U j O hj)).obj (Dobj U D j) :=
    D.iso O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj)
  let djk : (Modules.pullback (incO U j O hj)).obj (Dobj U D j) ≅
      (Modules.pullback (incO U k O hk)).obj (Dobj U D k) :=
    D.iso O.ι (incO U j O hj) (incO U k O hk) (Y.homOfLE_ι hj) (Y.homOfLE_ι hk)
  let dik : (Modules.pullback (incO U i O hi)).obj (Dobj U D i) ≅
      (Modules.pullback (incO U k O hk)).obj (Dobj U D k) :=
    D.iso O.ι (incO U i O hi) (incO U k O hk) (Y.homOfLE_ι hi) (Y.homOfLE_ι hk)
  have h : dij.hom ≫ djk.hom = dik.hom :=
    D.hom_comp O.ι (incO U i O hi) (incO U j O hj) (incO U k O hk)
      (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) (Y.homOfLE_ι hk)
  change (ei ≪≫ dij ≪≫ ej.symm).hom ≫ (ej ≪≫ djk ≪≫ ek.symm).hom =
    (ei ≪≫ dik ≪≫ ek.symm).hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [ej.inv_hom_id_assoc, reassoc_of% h]

/-- Push the module on a covering open forward to the ambient scheme. -/
noncomputable abbrev P (i : ι) : Y.Modules := (pushforward (incl U i)).obj (Dobj U D i)
/-- Push the second module restricted to an overlap forward to the ambient scheme. -/
noncomputable abbrev Q (i j : ι) : Y.Modules := (pushforward (U i ⊓ U j).ι).obj ((Dobj U D
  j).restrict (p₂ U i j))

/-- Restrict the second covering module to the overlap and push it forward. -/
noncomputable def β (i j : ι) : P U D j ⟶ Q U D i j :=
  (pushforward (incl U j)).map ((restrictAdjunction (p₂ U i j)).unit.app (Dobj U D j)) ≫
    (pushforwardComp (p₂ U i j) (incl U j)).hom.app _ ≫
    (pushforwardCongr (Y.homOfLE_ι inf_le_right)).hom.app _

/-- Restrict the first covering module and transport it by the overlap transition. -/
noncomputable def α (i j : ι) : P U D i ⟶ Q U D i j :=
  ((pushforward (incl U i)).map ((restrictAdjunction (p₁ U i j)).unit.app (Dobj U D i)) ≫
    (pushforwardComp (p₁ U i j) (incl U i)).hom.app _ ≫
    (pushforwardCongr (Y.homOfLE_ι inf_le_left)).hom.app _) ≫
    (pushforward (U i ⊓ U j).ι).map (ρ U D i j).hom

/-- The submodule of families of sections satisfying all overlap compatibility equations. -/
noncomputable def compatible (W : Y.Opens) : Submodule Γ(Y, W) (∀ i, Γ(P U D i, W)) where
  carrier := {s | ∀ i j, (α U D i j).app W (s i) = (β U D i j).app W (s j)}
  add_mem' := by
    intro s t hs ht i j
    simp only [Pi.add_apply, map_add, hs i j, ht i j]
  zero_mem' := by intro i j; simp only [Pi.zero_apply, map_zero]
  smul_mem' := by
    intro r s hs i j
    simp only [Pi.smul_apply, Hom.app_smul, hs i j]

theorem app_presheaf_map {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {W W' : X.Opens} (h : W' ⟶
    W) (x : Γ(M, W)) :
    φ.app W' (M.presheaf.map h.op x) = N.presheaf.map h.op (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality h.op) x

theorem compatible_map {W W' : Y.Opens} (h : W' ⟶ W) (s : ∀ i, Γ(P U D i, W)) (hs : s ∈ compatible
    U D W) :
    (fun i => (P U D i).presheaf.map h.op (s i)) ∈ compatible U D W' := by
  intro i j
  change (α U D i j).app W' ((P U D i).presheaf.map h.op (s i)) = (β U D i j).app W' ((P U D
    j).presheaf.map h.op (s j))
  rw [app_presheaf_map, app_presheaf_map, hs i j]

/-- The abelian presheaf of compatible families of sections. -/
noncomputable def gluedAb : (TopologicalSpace.Opens Y)ᵒᵖ ⥤ Ab where
  obj W := AddCommGrpCat.of (compatible U D W.unop)
  map {W W'} h := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨fun i => (P U D i).presheaf.map h (s.1 i), compatible_map U D h.unop s.1
      s.2⟩
      map_zero' := by apply Subtype.ext; funext i; simp
      map_add' := by intro s t; apply Subtype.ext; funext i; simp }
  map_id W := by
    apply AddCommGrpCat.ext; intro s; apply Subtype.ext; funext i
    simp
  map_comp {W W' W''} h h' := by
    apply AddCommGrpCat.ext; intro s; apply Subtype.ext; funext i
    simp

theorem gluedAb_map_apply_coe {W W' : (TopologicalSpace.Opens Y)ᵒᵖ} (h : W ⟶ W') (s : compatible U
    D W.unop) (i : ι) :
    ((gluedAb U D).map h s).1 i = (P U D i).presheaf.map h (s.1 i) := rfl

/-- The presheaf of modules whose sections are compatible families. -/
noncomputable def gluedPresheaf : Y.PresheafOfModules :=
  @PresheafOfModules.ofPresheaf _ _ _ (gluedAb U D)
    (fun W => show Module Γ(Y, W.unop) (compatible U D W.unop) from inferInstance)
    (by
      intro W W' h r s
      apply Subtype.ext; funext i
      exact (P U D i).map_smul h.unop r (s.1 i))

/-- The underlying abelian sheaf of a sheaf of scheme modules. -/
noncomputable abbrev abSheaf (M : Y.Modules) : TopCat.Sheaf Ab Y.toTopCat := ⟨M.presheaf, M.isSheaf⟩

theorem isSheaf_gluedPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y) (gluedPresheaf U D).presheaf := by
  change TopCat.Presheaf.IsSheaf (gluedAb U D)
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have hc : ∀ i, TopCat.Presheaf.IsCompatible (P U D i).presheaf W (fun a => (sf a).1 i) :=
    fun i a b => congrArg (fun s : compatible U D _ => s.1 i) (hsf a b)
  choose t ht huniq using fun i => (abSheaf (P U D i)).existsUnique_gluing W (fun a => (sf a).1 i)
    (hc i)
  have hmem : t ∈ compatible U D (iSup W) := by
    intro i j
    apply (abSheaf (Q U D i j)).eq_of_locally_eq W
    intro a
    change (Q U D i j).presheaf.map (Opens.leSupr W a).op ((α U D i j).app (iSup W) (t i)) =
      (Q U D i j).presheaf.map (Opens.leSupr W a).op ((β U D i j).app (iSup W) (t j))
    rw [← app_presheaf_map, ← app_presheaf_map]
    erw [ht i a, ht j a]
    exact (sf a).2 i j
  refine ⟨⟨t, hmem⟩, fun a => ?_, fun y hy => ?_⟩
  · apply Subtype.ext; funext i; exact ht i a
  · apply Subtype.ext; funext i
    exact huniq i _ (fun a => congrArg (fun s : compatible U D _ => s.1 i) (hy a))

/-- The sheaf of modules formed by gluing compatible families of sections. -/
noncomputable def glued : Y.Modules := ⟨gluedPresheaf U D, isSheaf_gluedPresheaf U D⟩

theorem glued_presheaf_obj (W : Y.Opens) : ((glued U D).presheaf.obj (op W) : Type u) = compatible
    U D W := rfl

/-- The projection from compatible families to one pushed-forward component. -/
noncomputable def projAb (k : ι) : gluedAb U D ⟶ (P U D k).presheaf where
  app W := AddCommGrpCat.ofHom
    { toFun := fun s => s.1 k, map_zero' := rfl, map_add' := fun _ _ => rfl }
  naturality {W W'} h := by apply AddCommGrpCat.ext; intro s; rfl

/-- The module morphism projecting the glued sheaf onto a pushed-forward component. -/
noncomputable def proj (k : ι) : glued U D ⟶ P U D k :=
  ⟨PresheafOfModules.homMk (M₁ := (glued U D).val) (M₂ := (P U D k).val) (projAb U D k)
    (fun _W _r _s => rfl)⟩

theorem proj_app (k : ι) (W : Y.Opens) (s : compatible U D W) :
    (proj U D k).app W (show Γ(glued U D, W) from s) = s.1 k := rfl

theorem presheaf_map_congr {X : Scheme.{u}} (M : X.Modules) {V V' : X.Opens} (f g : V' ⟶ V) (x :
    Γ(M, V)) :
    M.presheaf.map f.op x = M.presheaf.map g.op x := by rw [Subsingleton.elim f g]

theorem preimage_comp' {X X' X'' : Scheme.{u}} (f : X ⟶ X') (g : X' ⟶ X'') (W : X''.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := rfl

theorem preimage_ι_inf_right (i j : ι) (W : Y.Opens) :
    (U i ⊓ U j).ι ⁻¹ᵁ W = (p₂ U i j) ⁻¹ᵁ ((U j).ι ⁻¹ᵁ W) := by
  rw [← preimage_comp', Scheme.homOfLE_ι]

theorem preimage_ι_inf_left (i j : ι) (W : Y.Opens) :
    (U i ⊓ U j).ι ⁻¹ᵁ W = (p₁ U i j) ⁻¹ᵁ ((U i).ι ⁻¹ᵁ W) := by
  rw [← preimage_comp', Scheme.homOfLE_ι]

theorem β_le (i j : ι) (W : Y.Opens) : (p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) ≤ (U j).ι ⁻¹ᵁ W := by
  rw [preimage_ι_inf_right]; exact Scheme.Hom.image_preimage_le _ _

theorem α_le (i j : ι) (W : Y.Opens) : (p₁ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) ≤ (U i).ι ⁻¹ᵁ W := by
  rw [preimage_ι_inf_left]; exact Scheme.Hom.image_preimage_le _ _

theorem β_eq_of_le {i j : ι} {W : Y.Opens} (hW : W ≤ U i) :
    (p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) = (U j).ι ⁻¹ᵁ W := by
  rw [preimage_ι_inf_right, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.opensRange_homOfLE]
  refine inf_eq_right.mpr ?_
  change (U j).ι ⁻¹ᵁ W ≤ (U j).ι ⁻¹ᵁ (U i ⊓ U j)
  have h1 : (U j).ι ⁻¹ᵁ (U i ⊓ U j) = (U j).ι ⁻¹ᵁ (U i) ⊓ (U j).ι ⁻¹ᵁ (U j) := rfl
  rw [h1, Scheme.Opens.ι_preimage_self, inf_top_eq]
  exact fun y hy => hW hy

theorem β_app_hom (i j : ι) (W : Y.Opens) :
    (β U D i j).app W = (Dobj U D j).presheaf.map (homOfLE (β_le U i j W)).op := by
  have h1 := restrictAdjunction_unit_app_app (p₂ U i j) (Dobj U D j) ((U j).ι ⁻¹ᵁ W)
  have h2 := pushforwardComp_hom_app_app (M := (Dobj U D j).restrict (p₂ U i j)) (p₂ U i j) (incl
    U j) W
  have h3 := pushforwardCongr_hom_app_app (M := (Dobj U D j).restrict (p₂ U i j))
    (Y.homOfLE_ι (inf_le_right : U i ⊓ U j ≤ U j)) W
  rw [β, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, pushforward_map_app]
  erw [h1, h2, h3, Category.id_comp]
  rw [restrict_map]
  refine ((Dobj U D j).presheaf.map_comp _ _).symm.trans ?_
  congr 1

theorem β_app (i j : ι) (W : Y.Opens) (x : Γ(P U D j, W)) :
    (β U D i j).app W x = ((Dobj U D j).presheaf.map (homOfLE (β_le U i j W)).op x :) :=
  ConcreteCategory.congr_hom (β_app_hom U D i j W) x

theorem α_app_hom (i j : ι) (W : Y.Opens) :
    (α U D i j).app W = (Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op ≫
      (ρ U D i j).hom.app ((U i ⊓ U j).ι ⁻¹ᵁ W) := by
  have h1 := restrictAdjunction_unit_app_app (p₁ U i j) (Dobj U D i) ((U i).ι ⁻¹ᵁ W)
  have h2 := pushforwardComp_hom_app_app (M := (Dobj U D i).restrict (p₁ U i j)) (p₁ U i j) (incl
    U i) W
  have h3 := pushforwardCongr_hom_app_app (M := (Dobj U D i).restrict (p₁ U i j))
    (Y.homOfLE_ι (inf_le_left : U i ⊓ U j ≤ U i)) W
  rw [α, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.Hom.comp_app, pushforward_map_app, pushforward_map_app]
  erw [h1, h2, h3, Category.id_comp]
  rw [restrict_map]
  refine congrArg (fun t => t ≫ Hom.app (ρ U D i j).hom ((U i ⊓ U j).ι ⁻¹ᵁ W)) ?_
  refine ((Dobj U D i).presheaf.map_comp _ _).symm.trans ?_
  congr 1

theorem α_app (i j : ι) (W : Y.Opens) (x : Γ(P U D i, W)) :
    (α U D i j).app W x =
      (ρ U D i j).hom.app ((U i ⊓ U j).ι ⁻¹ᵁ W) ((Dobj U D i).presheaf.map (homOfLE (α_le U i j
        W)).op x) :=
  ConcreteCategory.congr_hom (α_app_hom U D i j W) x

theorem restrictFunctor_map_app {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (t : M ⟶ N)
    (V : X.Opens) : ((restrictFunctor f).map t).app V = t.app (f ''ᵁ V) := rfl

theorem presheaf_map_injective_of_eq {X : Scheme.{u}} (M : X.Modules) {V V' : X.Opens} (e : V' =
    V) (h : V' ≤ V) :
    Function.Injective (M.presheaf.map (homOfLE h).op) := by
  subst e
  intro x y hxy
  simpa using hxy

theorem compatible_ext_of_le {k : ι} {W : Y.Opens} (hW : W ≤ U k) {s s' : compatible U D W}
    (h : s.1 k = s'.1 k) : s = s' := by
  apply Subtype.ext; funext i
  have hs := s.2 k i
  have hs' := s'.2 k i
  rw [h, hs'] at hs
  rw [β_app, β_app] at hs
  exact (presheaf_map_injective_of_eq (Dobj U D i) (β_eq_of_le U hW) (β_le U k i W) hs).symm

theorem map_map {X : Scheme.{u}} (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (f : V₂ ⟶ V₁) (g : V₃ ⟶ V₂)
    (x : Γ(M, V₁)) :
    M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map (g ≫ f).op x :=
  (ConcreteCategory.congr_hom (M.presheaf.map_comp f.op g.op) x).symm

theorem map_self {X : Scheme.{u}} (M : X.Modules) {V : X.Opens} (f : V ⟶ V) (x : Γ(M, V)) :
    M.presheaf.map f.op x = x := by
  rw [Subsingleton.elim f (𝟙 V)]
  simp

theorem map_map_self {X : Scheme.{u}} (M : X.Modules) {V₁ V₂ : X.Opens} (f : V₂ ⟶ V₁) (g : V₁ ⟶
    V₂) (x : Γ(M, V₁)) :
    M.presheaf.map g.op (M.presheaf.map f.op x) = x := by
  rw [map_map, map_self]

theorem preimage_ι_eq_incO (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) :
    O.ι ⁻¹ᵁ V = (incO U i O hi) ⁻¹ᵁ ((U i).ι ⁻¹ᵁ V) := by
  rw [← preimage_comp', Scheme.homOfLE_ι]

theorem T_le_in (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) :
    (incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V) ≤ (U i).ι ⁻¹ᵁ V := by
  rw [preimage_ι_eq_incO U i O hi]; exact Scheme.Hom.image_preimage_le _ _

theorem T_eq (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) (hV : V ≤ O) :
    (incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V) = (U i).ι ⁻¹ᵁ V := by
  rw [preimage_ι_eq_incO U i O hi, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.opensRange_homOfLE]
  refine inf_eq_right.mpr ?_
  exact fun y hy => hV hy

theorem T_le_out (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) (hV : V ≤ O) :
    (U i).ι ⁻¹ᵁ V ≤ (incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V) :=
  (T_eq U i O hi V hV).symm.le

/-- Transport a section between two covering modules through a smaller common open. -/
noncomputable def T (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (V : Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) : Γ(Dobj U D j, (U j).ι ⁻¹ᵁ V) :=
  (Dobj U D j).presheaf.map (homOfLE (T_le_out U j O hj V hV)).op
    ((τ U D i j O hi hj).hom.app (O.ι ⁻¹ᵁ V)
      ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x))

theorem T_self (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) : T U D i i O hi hi V hV x = x := by
  simp only [T, τ_self, Scheme.Modules.Hom.id_app]
  exact map_map_self _ _ _ x

theorem T_comp (i j k : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (hk : O ≤ U k) (V :
    Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) :
    T U D j k O hj hk V hV (T U D i j O hi hj V hV x) = T U D i k O hi hk V hV x := by
  let aij : (Dobj U D i).presheaf.obj (op ((incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V))) ⟶
      (Dobj U D j).presheaf.obj (op ((incO U j O hj) ''ᵁ (O.ι ⁻¹ᵁ V))) :=
    (τ U D i j O hi hj).hom.app (O.ι ⁻¹ᵁ V)
  let ajk : (Dobj U D j).presheaf.obj (op ((incO U j O hj) ''ᵁ (O.ι ⁻¹ᵁ V))) ⟶
      (Dobj U D k).presheaf.obj (op ((incO U k O hk) ''ᵁ (O.ι ⁻¹ᵁ V))) :=
    (τ U D j k O hj hk).hom.app (O.ι ⁻¹ᵁ V)
  let aik : (Dobj U D i).presheaf.obj (op ((incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V))) ⟶
      (Dobj U D k).presheaf.obj (op ((incO U k O hk) ''ᵁ (O.ι ⁻¹ᵁ V))) :=
    (τ U D i k O hi hk).hom.app (O.ι ⁻¹ᵁ V)
  have hc : aij ≫ ajk = aik :=
    (Scheme.Modules.Hom.comp_app (τ U D i j O hi hj).hom
      (τ U D j k O hj hk).hom (U := O.ι ⁻¹ᵁ V)).symm.trans
      (congrArg
        (fun a : (Dobj U D i).restrict (incO U i O hi) ⟶
            (Dobj U D k).restrict (incO U k O hk) => a.app (O.ι ⁻¹ᵁ V))
        (τ_comp U D i j k O hi hj hk))
  change (Dobj U D k).presheaf.map (homOfLE (T_le_out U k O hk V hV)).op
      (ajk ((Dobj U D j).presheaf.map (homOfLE (T_le_in U j O hj V)).op
        ((Dobj U D j).presheaf.map (homOfLE (T_le_out U j O hj V hV)).op
          (aij ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x))))) =
    (Dobj U D k).presheaf.map (homOfLE (T_le_out U k O hk V hV)).op
      (aik ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x))
  rw [map_map_self]
  rw [← hc]
  rfl

theorem T_res (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) {V V' : Y.Opens} (hV : V ≤ O)
    (hV' : V' ≤ V)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) :
    T U D i j O hi hj V' (hV'.trans hV) ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono
      hV')).op x) =
      (Dobj U D j).presheaf.map (homOfLE ((U j).ι.preimage_mono hV')).op (T U D i j O hi hj V hV
        x) := by
  let aV : (Dobj U D i).presheaf.obj (op ((incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V))) ⟶
      (Dobj U D j).presheaf.obj (op ((incO U j O hj) ''ᵁ (O.ι ⁻¹ᵁ V))) :=
    (τ U D i j O hi hj).hom.app (O.ι ⁻¹ᵁ V)
  let aV' : (Dobj U D i).presheaf.obj (op ((incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V'))) ⟶
      (Dobj U D j).presheaf.obj (op ((incO U j O hj) ''ᵁ (O.ι ⁻¹ᵁ V'))) :=
    (τ U D i j O hi hj).hom.app (O.ι ⁻¹ᵁ V')
  change (Dobj U D j).presheaf.map
      (homOfLE (T_le_out U j O hj V' (hV'.trans hV))).op
      (aV' ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V')).op
        ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono hV')).op x))) =
    (Dobj U D j).presheaf.map (homOfLE ((U j).ι.preimage_mono hV')).op
      ((Dobj U D j).presheaf.map (homOfLE (T_le_out U j O hj V hV)).op
        (aV ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x)))
  rw [map_map, map_map]
  have nat : aV' ((Dobj U D i).presheaf.map
      ((Hom.opensFunctor (incO U i O hi)).map (homOfLE (O.ι.preimage_mono hV'))).op
      ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x)) =
      (Dobj U D j).presheaf.map
        ((Hom.opensFunctor (incO U j O hj)).map (homOfLE (O.ι.preimage_mono hV'))).op
        (aV ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x)) :=
    app_presheaf_map (τ U D i j O hi hj).hom (homOfLE (O.ι.preimage_mono hV'))
      ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x)
  have step1 : (Dobj U D i).presheaf.map
      (homOfLE (T_le_in U i O hi V') ≫ homOfLE ((U i).ι.preimage_mono hV')).op x =
      (Dobj U D i).presheaf.map
        ((Hom.opensFunctor (incO U i O hi)).map (homOfLE (O.ι.preimage_mono hV'))).op
        ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x) := by
    rw [map_map]
    exact presheaf_map_congr _ _ _ _
  rw [step1, nat]
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

/-- The canonical comparison between restriction along a composite and iterated restriction. -/
noncomputable def Φ {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
  [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctor a').obj M ⟶ (restrictFunctor e).obj ((restrictFunctor a).obj M) :=
  (restrictFunctorIsoPullback a').hom.app M ≫
    (MOD.mapComp' a.op.toLoc e.op.toLoc a'.op.toLoc (by rw [← w]; rfl)).hom.toNatTrans.app M ≫
    (restrictFunctorIsoPullback e).inv.app ((Modules.pullback a).obj M) ≫
    (restrictFunctor e).map ((restrictFunctorIsoPullback a).inv.app M)

theorem Φ_eq_congr_comp {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
    [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    Φ e a a' w M = (restrictFunctorCongr w.symm).hom.app M ≫ (restrictFunctorComp e a).hom.app M
      := by
  subst w
  have hc : (restrictFunctorCongr (rfl : e ≫ a = e ≫ a)).hom.app M = 𝟙 _ := by
    apply Scheme.Modules.hom_ext; intro V
    erw [restrictFunctorCongr_hom_app_app]
    simp
    rfl
  rw [hc, Category.id_comp, Φ]
  erw [restrictFunctorIsoPullback_comp_hom_app e a M, mapComp'_hom_app_eq e a M (e ≫ a) rfl]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp,
    Category.assoc]
  have c1 : (restrictFunctorIsoPullback e).hom.app ((Modules.pullback a).obj M) ≫
      (restrictFunctorIsoPullback e).inv.app ((Modules.pullback a).obj M) = 𝟙 _ :=
        Iso.hom_inv_id_app _ _
  have c2 : (restrictFunctor e).map ((restrictFunctorIsoPullback a).hom.app M) ≫
      (restrictFunctor e).map ((restrictFunctorIsoPullback a).inv.app M) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have c0 : (pullbackComp e a).hom.app M ≫ (pullbackComp e a).inv.app M = 𝟙 _ :=
    Iso.hom_inv_id_app _ _
  erw [reassoc_of% c0, reassoc_of% c1, c2]
  erw [Category.comp_id]

theorem image_comp_of_eq {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
    [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (V : X₀.Opens) : a ''ᵁ (e ''ᵁ V) =
      a' ''ᵁ V := by
  subst w
  apply TopologicalSpace.Opens.ext
  exact (Set.image_comp _ _ _).symm

theorem Φ_app {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) (V : X₀.Opens)
    (x : Γ(M, a' ''ᵁ V)) :
    (Φ e a a' w M).app V x = (M.presheaf.map (eqToHom (image_comp_of_eq e a a' w V)).op x :
      Γ(M, a ''ᵁ (e ''ᵁ V))) := by
  have h1 := restrictFunctorCongr_hom_app_app (U := V) w.symm M
  have h2 := restrictFunctorComp_hom_app_app (U := V) e a M
  rw [Φ_eq_congr_comp]
  refine (show _ = (Hom.app ((restrictFunctorComp e a).hom.app M) V)
    ((Hom.app ((restrictFunctorCongr w.symm).hom.app M) V) x) from rfl).trans ?_
  refine (congrArg _ (ConcreteCategory.congr_hom h1 x)).trans ?_
  refine (ConcreteCategory.congr_hom h2 _).trans ?_
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

/-- The forward comparison from a composite restriction to its iterated restriction. -/
noncomputable def castComp {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
  [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctor a').obj M ⟶ (restrictFunctor e).obj ((restrictFunctor a).obj M) :=
  (restrictFunctorCongr w.symm).hom.app M ≫ (restrictFunctorComp e a).hom.app M

/-- The reverse comparison from an iterated restriction to its composite restriction. -/
noncomputable def castComp' {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
  [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctor e).obj ((restrictFunctor a).obj M) ⟶ (restrictFunctor a').obj M :=
  (restrictFunctorComp e a).inv.app M ≫ (restrictFunctorCongr w).hom.app M

theorem castComp_app {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
    [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) (V : X₀.Opens)
    (x : Γ(M, a' ''ᵁ V)) :
    (castComp e a a' w M).app V x = (M.presheaf.map (eqToHom (image_comp_of_eq e a a' w V)).op x :
      Γ(M, a ''ᵁ (e ''ᵁ V))) := by
  have h := Φ_app e a a' w M V x
  rw [Φ_eq_congr_comp] at h
  exact h

theorem castComp'_app {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂)
    [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) (V : X₀.Opens)
    (x : Γ(M, a ''ᵁ (e ''ᵁ V))) :
    (castComp' e a a' w M).app V x = (M.presheaf.map (eqToHom (image_comp_of_eq e a a' w
      V).symm).op x :
      Γ(M, a' ''ᵁ V)) := by
  have h1 := restrictFunctorComp_inv_app_app (U := V) e a M
  have h2 := restrictFunctorCongr_hom_app_app (U := V) w M
  refine (show _ = (Hom.app ((restrictFunctorCongr w).hom.app M) V)
    ((Hom.app ((restrictFunctorComp e a).inv.app M) V) x) from rfl).trans ?_
  refine (congrArg _ (ConcreteCategory.congr_hom h1 x)).trans ?_
  refine (ConcreteCategory.congr_hom h2 _).trans ?_
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

theorem τ_hom_eq (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) : (τ U D i j O hi hj).hom =
    (restrictFunctorIsoPullback (incO U i O hi)).hom.app (Dobj U D i) ≫
      D.hom O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) ≫
      (restrictFunctorIsoPullback (incO U j O hj)).inv.app (Dobj U D j) := by
  let ei : (Dobj U D i).restrict (incO U i O hi) ≅
      (Modules.pullback (incO U i O hi)).obj (Dobj U D i) :=
    (restrictFunctorIsoPullback (incO U i O hi)).app (Dobj U D i)
  let ej : (Dobj U D j).restrict (incO U j O hj) ≅
      (Modules.pullback (incO U j O hj)).obj (Dobj U D j) :=
    (restrictFunctorIsoPullback (incO U j O hj)).app (Dobj U D j)
  let d : (Modules.pullback (incO U i O hi)).obj (Dobj U D i) ≅
      (Modules.pullback (incO U j O hj)).obj (Dobj U D j) :=
    D.iso O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj)
  have hd : d.hom = (D.hom O.ι (incO U i O hi) (incO U j O hj)
      (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) :
      (Modules.pullback (incO U i O hi)).obj (Dobj U D i) ⟶
        (Modules.pullback (incO U j O hj)).obj (Dobj U D j)) := rfl
  exact congrArg
    (fun a : (Modules.pullback (incO U i O hi)).obj (Dobj U D i) ⟶
        (Modules.pullback (incO U j O hj)).obj (Dobj U D j) =>
      ei.hom ≫ a ≫ ej.inv) hd

theorem τ_locality (i j : ι) {O O' : Y.Opens} (hO' : O' ≤ O) (hi : O ≤ U i) (hj : O ≤ U j) :
    (restrictFunctorIsoPullback (incO U i O' (hO'.trans hi))).hom.app (D.obj i) ≫
      D.hom O'.ι (incO U i O' (hO'.trans hi)) (incO U j O' (hO'.trans hj))
        (Y.homOfLE_ι (hO'.trans hi)) (Y.homOfLE_ι (hO'.trans hj)) ≫
      (restrictFunctorIsoPullback (incO U j O' (hO'.trans hj))).inv.app (D.obj j) =
    (restrictFunctorCongr (incO_comp U i hO' hi).symm).hom.app (D.obj i) ≫
      (restrictFunctorComp (Y.homOfLE hO') (incO U i O hi)).hom.app (D.obj i) ≫
      (restrictFunctor (Y.homOfLE hO')).map
        ((restrictFunctorIsoPullback (incO U i O hi)).hom.app (D.obj i) ≫
          D.hom O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) ≫
          (restrictFunctorIsoPullback (incO U j O hj)).inv.app (D.obj j)) ≫
      (restrictFunctorComp (Y.homOfLE hO') (incO U j O hj)).inv.app (D.obj j) ≫
      (restrictFunctorCongr (incO_comp U j hO' hj)).hom.app (D.obj j) := by
  have hh := crux_MOD (Y.homOfLE hO') (incO U i O hi) (incO U j O hj)
    (incO U i O' (hO'.trans hi)) (incO U j O' (hO'.trans hj)) (incO_comp U i hO' hi) (incO_comp U
      j hO' hj)
    (D.obj i) (D.obj j) (D.hom O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι
      hj))
  rw [D_pullHom U D (Y.homOfLE hO') O.ι O'.ι (Y.homOfLE_ι hO') (incO U i O hi) (incO U j O hj)
    (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) (incO U i O' (hO'.trans hi)) (incO U j O' (hO'.trans hj))
    (incO_comp U i hO' hi) (incO_comp U j hO' hj) (Y.homOfLE_ι _) (Y.homOfLE_ι _)] at hh
  exact hh

theorem T_indep (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (V : Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) :
    T U D i j O hi hj V hV x = T U D i j V (hV.trans hi) (hV.trans hj) V le_rfl x := by
  symm
  simp only [T]
  have loc := τ_locality U D i j hV hi hj
  have hsub : (Y.homOfLE hV) ''ᵁ (V.ι ⁻¹ᵁ V) ≤ O.ι ⁻¹ᵁ V :=
    ((Y.homOfLE hV).image_le_opensRange _).trans (by rw [Scheme.opensRange_homOfLE])
  have ev : ∀ y, (τ U D i j V (hV.trans hi) (hV.trans hj)).hom.app (V.ι ⁻¹ᵁ V) y =
      ((restrictFunctorCongr (Scheme.homOfLE_homOfLE Y hV hj)).hom.app (Dobj U D j)).app (V.ι ⁻¹ᵁ V)
      (((restrictFunctorComp (Y.homOfLE hV) (incO U j O hj)).inv.app (Dobj U D j)).app (V.ι ⁻¹ᵁ V)
      (((restrictFunctorIsoPullback (incO U i O hi)).hom.app (Dobj U D i) ≫
          D.hom O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) ≫
          (restrictFunctorIsoPullback (incO U j O hj)).inv.app (Dobj U D j)).app ((Y.homOfLE hV)
            ''ᵁ (V.ι ⁻¹ᵁ V))
      (((restrictFunctorComp (Y.homOfLE hV) (incO U i O hi)).hom.app (Dobj U D i)).app (V.ι ⁻¹ᵁ V)
      (((restrictFunctorCongr (Scheme.homOfLE_homOfLE Y hV hi).symm).hom.app (Dobj U D i)).app
        (V.ι ⁻¹ᵁ V) y)))) := by
    intro y; rw [τ_hom_eq, loc]; rfl
  have c1 := restrictFunctorCongr_hom_app_app (U := V.ι ⁻¹ᵁ V) (Scheme.homOfLE_homOfLE Y hV
    hi).symm (Dobj U D i)
  have c2 := restrictFunctorComp_hom_app_app (U := V.ι ⁻¹ᵁ V) (Y.homOfLE hV) (incO U i O hi) (Dobj
    U D i)
  have c3 := restrictFunctorComp_inv_app_app (U := V.ι ⁻¹ᵁ V) (Y.homOfLE hV) (incO U j O hj) (Dobj
    U D j)
  have c4 := restrictFunctorCongr_hom_app_app (U := V.ι ⁻¹ᵁ V) (Scheme.homOfLE_homOfLE Y hV hj)
    (Dobj U D j)
  have hEv := ev ((Dobj U D i).presheaf.map
    (homOfLE (T_le_in U i V (hV.trans hi) V)).op x)
  have hOuter := congrArg
    (fun y : Γ((Dobj U D j).restrict (incO U j V (hV.trans hj)), V.ι ⁻¹ᵁ V) =>
      (Dobj U D j).presheaf.map
        (homOfLE (T_le_out U j V (hV.trans hj) V le_rfl)).op y) hEv
  refine hOuter.trans ?_
  erw [c1, c2, c3, c4, ← τ_hom_eq]
  generalize (τ U D i j O hi hj).hom = τ₀
  refine (map_map _ _ _ _).trans ((map_map _ _ _ _).trans ?_)
  erw [map_map (Dobj U D i), map_map (Dobj U D i)]
  erw [presheaf_map_congr (Dobj U D i) _
    ((Hom.opensFunctor (incO U i O hi)).map (homOfLE hsub) ≫ homOfLE (T_le_in U i O hi V)) x]
  erw [← map_map (Dobj U D i) (homOfLE (T_le_in U i O hi V)) ((Hom.opensFunctor (incO U i O
    hi)).map (homOfLE hsub)) x]
  have nat := app_presheaf_map τ₀ (homOfLE hsub)
    ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x)
  rw [restrict_map, restrict_map] at nat
  erw [nat]
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

theorem presheaf_map_injective_of_eq' {X : Scheme.{u}} (M : X.Modules) {V V' : X.Opens} (e : V' =
    V) (f : V' ⟶ V) :
    Function.Injective (M.presheaf.map f.op) := by
  subst e
  intro x y hxy
  rwa [map_self, map_self] at hxy

theorem preimage_ι_inf_self (O W : Y.Opens) : O.ι ⁻¹ᵁ (W ⊓ O) = O.ι ⁻¹ᵁ W := by
  change O.ι ⁻¹ᵁ W ⊓ O.ι ⁻¹ᵁ O = _
  rw [Scheme.Opens.ι_preimage_self, inf_top_eq]

theorem compat_of_T (W : Y.Opens) (s : ∀ i, Γ(P U D i, W)) (i j : ι)
    (h : T U D i j (U i ⊓ U j) inf_le_left inf_le_right (W ⊓ (U i ⊓ U j)) inf_le_right
        ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono inf_le_left)).op (s i)) =
      (Dobj U D j).presheaf.map (homOfLE ((U j).ι.preimage_mono inf_le_left)).op (s j)) :
    (α U D i j).app W (s i) = (β U D i j).app W (s j) := by
  rw [α_app, β_app]
  have hm : (U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j)) ≤ (U i ⊓ U j).ι ⁻¹ᵁ W :=
    (U i ⊓ U j).ι.preimage_mono inf_le_left
  have he : (p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j))) =
      (p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) := by
    rw [preimage_ι_inf_self]
  let a : (Dobj U D i).presheaf.obj
      (op ((p₁ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j))))) ⟶
      (Dobj U D j).presheaf.obj
        (op ((p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j))))) :=
    (ρ U D i j).hom.app ((U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j)))
  let aW : (Dobj U D i).presheaf.obj (op ((p₁ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W))) ⟶
      (Dobj U D j).presheaf.obj (op ((p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W))) :=
    (ρ U D i j).hom.app ((U i ⊓ U j).ι ⁻¹ᵁ W)
  change aW ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op (s i)) =
    (Dobj U D j).presheaf.map (homOfLE (β_le U i j W)).op (s j)
  apply presheaf_map_injective_of_eq' (Dobj U D j) he
    ((Hom.opensFunctor (p₂ U i j)).map (homOfLE hm))
  have nat : a ((Dobj U D i).presheaf.map
      ((Hom.opensFunctor (p₁ U i j)).map (homOfLE hm)).op
      ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op (s i))) =
      (Dobj U D j).presheaf.map ((Hom.opensFunctor (p₂ U i j)).map (homOfLE hm)).op
        (aW ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op (s i))) :=
    app_presheaf_map (ρ U D i j).hom (homOfLE hm)
      ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op (s i))
  rw [← nat]
  have hR := map_map (Dobj U D j) (homOfLE (β_le U i j W))
    ((Hom.opensFunctor (p₂ U i j)).map (homOfLE hm))
    (show (Dobj U D j).presheaf.obj (op ((U j).ι ⁻¹ᵁ W)) from s j)
  refine Eq.trans ?_ hR.symm
  have eL : (Dobj U D i).presheaf.map
      ((Hom.opensFunctor (p₁ U i j)).map (homOfLE hm)).op
      ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op (s i)) =
      (Dobj U D i).presheaf.map
        (homOfLE (T_le_in U i (U i ⊓ U j) inf_le_left (W ⊓ (U i ⊓ U j)))).op
        ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono inf_le_left)).op
          (s i)) :=
    (map_map _ _ _ _).trans
      ((presheaf_map_congr _ _ _ _).trans (map_map _ _ _ _).symm)
  refine (congrArg
    (fun x : (Dobj U D i).presheaf.obj
        (op ((p₁ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j))))) => a x) eL).trans ?_
  change (Dobj U D j).presheaf.map
      (homOfLE (T_le_out U j (U i ⊓ U j) inf_le_right
        (W ⊓ (U i ⊓ U j)) inf_le_right)).op
      (a ((Dobj U D i).presheaf.map
        (homOfLE (T_le_in U i (U i ⊓ U j) inf_le_left (W ⊓ (U i ⊓ U j)))).op
        ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono inf_le_left)).op
          (s i)))) =
    (Dobj U D j).presheaf.map (homOfLE ((U j).ι.preimage_mono inf_le_left)).op (s j) at h
  have h' := congrArg ((Dobj U D j).presheaf.map
    (homOfLE (T_le_in U j (U i ⊓ U j) inf_le_right (W ⊓ (U i ⊓ U j)))).op) h
  have h'' := (map_map_self (Dobj U D j) _ _ _).symm.trans
    (h'.trans (map_map (Dobj U D j) _ _ _))
  refine h''.trans ?_
  exact presheaf_map_congr _ _ _ _

/-- Restrict the glued sheaf to a covering open and project to its descent component. -/
noncomputable def restrictGluedHom (k : ι) : (glued U D).restrict (incl U k) ⟶ Dobj U D k :=
  (restrictFunctor (incl U k)).map (proj U D k) ≫ (restrictAdjunction (incl U k)).counit.app (Dobj
    U D k)

theorem restrictGluedHom_app (k : ι) (V : ((U k : Y.Opens) : Scheme.{u}).Opens)
    (s : compatible U D ((incl U k) ''ᵁ V)) :
    (restrictGluedHom U D k).app V (show Γ((glued U D).restrict (incl U k), V) from s) =
      (Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V).symm).op (s.1 k) := by
  have h := restrictAdjunction_counit_app_app (incl U k) (Dobj U D k) V
  rw [restrictGluedHom, Scheme.Modules.Hom.comp_app]
  erw [h]
  rfl

theorem restrictGluedHom_app_injective (k : ι) (V : ((U k : Y.Opens) : Scheme.{u}).Opens) :
    Function.Injective ((restrictGluedHom U D k).app V) := by
  intro s s' h
  change compatible U D ((incl U k) ''ᵁ V) at s s'
  rw [restrictGluedHom_app, restrictGluedHom_app] at h
  have hinj : Function.Injective ((Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq
    V).symm).op) := by
    intro x y hxy
    simpa using congrArg ((Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V)).op)
      hxy
  exact compatible_ext_of_le U D ((incl U k).image_le_opensRange V |>.trans (by simp)) (hinj h)

theorem preimage_incl_inf_self (i : ι) (W : Y.Opens) : (U i).ι ⁻¹ᵁ (W ⊓ U i) = (U i).ι ⁻¹ᵁ W := by
  change (U i).ι ⁻¹ᵁ W ⊓ (U i).ι ⁻¹ᵁ (U i) = _
  rw [Scheme.Opens.ι_preimage_self, inf_top_eq]

theorem restrictGluedHom_app_surjective (k : ι) (V : ((U k : Y.Opens) : Scheme.{u}).Opens) :
    Function.Surjective ((restrictGluedHom U D k).app V) := by
  intro y
  have hW : (incl U k) ''ᵁ V ≤ U k := ((incl U k).image_le_opensRange V).trans (by simp)
  let t : Γ(P U D k, (incl U k) ''ᵁ V) :=
    (Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V)).op y
  let s : ∀ i, Γ(P U D i, (incl U k) ''ᵁ V) := fun i =>
    (Dobj U D i).presheaf.map (homOfLE (preimage_incl_inf_self U i _).symm.le).op
      (T U D k i (U k ⊓ U i) inf_le_left inf_le_right ((incl U k) ''ᵁ V ⊓ U i) (inf_le_inf_right
        (U i) hW)
        ((Dobj U D k).presheaf.map (homOfLE ((U k).ι.preimage_mono inf_le_left)).op t))
  have step : ∀ (i : ι) (V' : Y.Opens) (hV'W : V' ≤ (incl U k) ''ᵁ V) (hV'i : V' ≤ U i),
      (Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono hV'W)).op (s i) =
        T U D k i V' (hV'W.trans hW) hV'i V' le_rfl
          ((Dobj U D k).presheaf.map (homOfLE ((U k).ι.preimage_mono hV'W)).op t) := by
    intro i V' hV'W hV'i
    have hle : V' ≤ (incl U k) ''ᵁ V ⊓ U i := le_inf hV'W hV'i
    refine (map_map _ _ _ _).trans ?_
    refine (presheaf_map_congr _ _ (homOfLE ((U i).ι.preimage_mono hle)) _).trans ?_
    refine (T_res U D k i (U k ⊓ U i) inf_le_left inf_le_right (inf_le_inf_right (U i) hW) hle
      _).symm.trans ?_
    refine (congrArg (T U D k i (U k ⊓ U i) inf_le_left inf_le_right _ (hle.trans
      (inf_le_inf_right (U i) hW)))
      ((map_map _ _ _ _).trans (presheaf_map_congr _ _ (homOfLE ((U k).ι.preimage_mono hV'W))
        _))).trans ?_
    exact T_indep U D k i _ _ _ _ _ _
  have mem : s ∈ compatible U D ((incl U k) ''ᵁ V) := by
    intro i j
    apply compat_of_T
    rw [step i _ inf_le_left (inf_le_right.trans inf_le_left), step j _ inf_le_left
      (inf_le_right.trans inf_le_right),
      T_indep, T_comp]
  refine ⟨⟨s, mem⟩, ?_⟩
  rw [restrictGluedHom_app]
  have hk : s k = t :=
    (congrArg ((Dobj U D k).presheaf.map (homOfLE (preimage_incl_inf_self U k _).symm.le).op)
      (T_self U D k (U k ⊓ U k) inf_le_left ((incl U k) ''ᵁ V ⊓ U k) (inf_le_inf_right (U k) hW)
        _)).trans
      (map_map_self _ _ _ _)
  exact (congrArg ((Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V).symm).op)
    hk).trans
    (map_map_self _ _ _ _)

theorem isIso_restrictGluedHom (k : ι) : IsIso (restrictGluedHom U D k) := by
  refine Hom.isIso_iff_isIso_app.mpr fun V => ?_
  have : IsIso ((CategoryTheory.forget Ab).map ((restrictGluedHom U D k).app V)) :=
    (isIso_iff_bijective _).mpr ⟨restrictGluedHom_app_injective U D k V,
      restrictGluedHom_app_surjective U D k V⟩
  exact isIso_of_reflects_iso _ (CategoryTheory.forget Ab)

/-- The isomorphism from the pullback of the glued sheaf to a descent component. -/
noncomputable def gluedIso (k : ι) : (Modules.pullback (incl U k)).obj (glued U D) ≅ Dobj U D k :=
  ((restrictFunctorIsoPullback (incl U k)).app (glued U D)).symm ≪≫
    @asIso _ _ _ _ (restrictGluedHom U D k) (isIso_restrictGluedHom U D k)

theorem image_mono' {X X' : Scheme.{u}} (f : X ⟶ X') [IsOpenImmersion f] {A B : X.Opens} (h : A ≤
    B) :
    f ''ᵁ A ≤ f ''ᵁ B := fun _ ⟨z, hz, e⟩ => ⟨z, h hz, e⟩

theorem cs_le (i j : ι) (V : ((U i ⊓ U j : Y.Opens) : Scheme.{u}).Opens) :
    (p₁ U i j) ''ᵁ V ≤ (U i).ι ⁻¹ᵁ ((U i ⊓ U j).ι ''ᵁ V) :=
  (image_mono' (p₁ U i j) (((U i ⊓ U j).ι.preimage_image_eq V).symm.le)).trans (α_le U i j _)

theorem cs_le' (i j : ι) (V : ((U i ⊓ U j : Y.Opens) : Scheme.{u}).Opens) :
    (p₂ U i j) ''ᵁ V ≤ (U j).ι ⁻¹ᵁ ((U i ⊓ U j).ι ''ᵁ V) :=
  (image_mono' (p₂ U i j) (((U i ⊓ U j).ι.preimage_image_eq V).symm.le)).trans (β_le U i j _)


theorem comm_sections (i j : ι) :
    castComp (p₁ U i j) (incl U i) (U i ⊓ U j).ι (Y.homOfLE_ι inf_le_left) (glued U D) ≫
        (restrictFunctor (p₁ U i j)).map (restrictGluedHom U D i) ≫ (ρ U D i j).hom =
      castComp (p₂ U i j) (incl U j) (U i ⊓ U j).ι (Y.homOfLE_ι inf_le_right) (glued U D) ≫
        (restrictFunctor (p₂ U i j)).map (restrictGluedHom U D j) := by
  apply Scheme.Modules.hom_ext
  intro V
  apply AddCommGrpCat.ext
  intro s
  change compatible U D ((U i ⊓ U j).ι ''ᵁ V) at s
  generalize hρ : (ρ U D i j).hom = ρ₀
  have E₁ : (incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V) = (U i ⊓ U j).ι ''ᵁ V :=
    image_comp_of_eq (p₁ U i j) (incl U i) ((U i ⊓ U j).ι) (Y.homOfLE_ι inf_le_left) V
  have E₂ : (incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V) = (U i ⊓ U j).ι ''ᵁ V :=
    image_comp_of_eq (p₂ U i j) (incl U j) ((U i ⊓ U j).ι) (Y.homOfLE_ι inf_le_right) V
  let ci : (glued U D).presheaf.obj (op ((U i ⊓ U j).ι ''ᵁ V)) ⟶
      (glued U D).presheaf.obj (op ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V))) :=
    (castComp (p₁ U i j) (incl U i) (U i ⊓ U j).ι
      (Y.homOfLE_ι inf_le_left) (glued U D)).app V
  let cj : (glued U D).presheaf.obj (op ((U i ⊓ U j).ι ''ᵁ V)) ⟶
      (glued U D).presheaf.obj (op ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V))) :=
    (castComp (p₂ U i j) (incl U j) (U i ⊓ U j).ι
      (Y.homOfLE_ι inf_le_right) (glued U D)).app V
  let ri : (glued U D).presheaf.obj (op ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V))) ⟶
      (Dobj U D i).presheaf.obj (op ((p₁ U i j) ''ᵁ V)) :=
    (restrictGluedHom U D i).app ((p₁ U i j) ''ᵁ V)
  let rj : (glued U D).presheaf.obj (op ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V))) ⟶
      (Dobj U D j).presheaf.obj (op ((p₂ U i j) ''ᵁ V)) :=
    (restrictGluedHom U D j).app ((p₂ U i j) ''ᵁ V)
  let aρ : (Dobj U D i).presheaf.obj (op ((p₁ U i j) ''ᵁ V)) ⟶
      (Dobj U D j).presheaf.obj (op ((p₂ U i j) ''ᵁ V)) :=
    ρ₀.app V
  change (ci ≫ ri ≫ aρ) s = (cj ≫ rj) s
  change aρ (ri (ci s)) = rj (cj s)
  have k1 : ci s = (glued U D).presheaf.map (eqToHom E₁).op s :=
    castComp_app (p₁ U i j) (incl U i) (U i ⊓ U j).ι
      (Y.homOfLE_ι inf_le_left) (glued U D) V s
  have k2 : cj s = (glued U D).presheaf.map (eqToHom E₂).op s :=
    castComp_app (p₂ U i j) (incl U j) (U i ⊓ U j).ι
      (Y.homOfLE_ι inf_le_right) (glued U D) V s
  refine (congrArg
    (fun x : (glued U D).presheaf.obj (op ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V))) =>
      aρ (ri x)) k1).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun x : (glued U D).presheaf.obj (op ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V))) =>
      rj x) k2).symm
  have r1 : ri ((glued U D).presheaf.map (eqToHom E₁).op s) =
      (Dobj U D i).presheaf.map
        (eqToHom ((incl U i).preimage_image_eq ((p₁ U i j) ''ᵁ V)).symm).op
        ((show compatible U D ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V)) from
          (glued U D).presheaf.map (eqToHom E₁).op s).1 i) :=
    restrictGluedHom_app U D i ((p₁ U i j) ''ᵁ V)
      (show compatible U D ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V)) from
        (glued U D).presheaf.map (eqToHom E₁).op s)
  have r2 : rj ((glued U D).presheaf.map (eqToHom E₂).op s) =
      (Dobj U D j).presheaf.map
        (eqToHom ((incl U j).preimage_image_eq ((p₂ U i j) ''ᵁ V)).symm).op
        ((show compatible U D ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V)) from
          (glued U D).presheaf.map (eqToHom E₂).op s).1 j) :=
    restrictGluedHom_app U D j ((p₂ U i j) ''ᵁ V)
      (show compatible U D ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V)) from
        (glued U D).presheaf.map (eqToHom E₂).op s)
  refine (congrArg
    (fun x : (Dobj U D i).presheaf.obj (op ((p₁ U i j) ''ᵁ V)) => aρ x) r1).trans ?_
  refine Eq.trans ?_ r2.symm
  have g1 : (show compatible U D ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V)) from (glued U D).presheaf.map
    (eqToHom E₁).op s).1 i =
      (Dobj U D i).presheaf.map ((Opens.map (incl U i).base).map (eqToHom E₁)).op (s.1 i) := rfl
  have g2 : (show compatible U D ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V)) from (glued U D).presheaf.map
    (eqToHom E₂).op s).1 j =
      (Dobj U D j).presheaf.map ((Opens.map (incl U j).base).map (eqToHom E₂)).op (s.1 j) := rfl
  erw [g1, g2]
  erw [map_map (Dobj U D i), map_map (Dobj U D j)]
  erw [presheaf_map_congr (Dobj U D i) _ (homOfLE (cs_le U i j V)) (s.1 i),
    presheaf_map_congr (Dobj U D j) _ (homOfLE (cs_le' U i j V)) (s.1 j)]
  have hc := s.2 i j
  rw [α_app, β_app] at hc
  rw [hρ] at hc
  have nat := app_presheaf_map ρ₀ (eqToHom (((U i ⊓ U j).ι.preimage_image_eq V).symm))
    ((Dobj U D i).presheaf.map (homOfLE (α_le U i j _)).op (s.1 i))
  rw [restrict_map, restrict_map] at nat
  erw [hc] at nat
  erw [presheaf_map_congr (Dobj U D i) (homOfLE (cs_le U i j V))
    ((Hom.opensFunctor (p₁ U i j)).map (eqToHom (((U i ⊓ U j).ι.preimage_image_eq V).symm)) ≫
      homOfLE (α_le U i j _)) (s.1 i)]
  erw [← map_map (Dobj U D i) (homOfLE (α_le U i j ((U i ⊓ U j).ι ''ᵁ V)))
    ((Hom.opensFunctor (p₁ U i j)).map (eqToHom (((U i ⊓ U j).ι.preimage_image_eq V).symm))) (s.1
      i)]
  erw [nat]
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

theorem pseudo_map_map {X X' : Scheme.{u}} (f : X ⟶ X')
    {M N : X'.Modules} (ψ : M ⟶ N) {P Q : X.Modules}
    (a : P ⟶ (Modules.pullback f).obj M)
    (b : (Modules.pullback f).obj N ⟶ Q) :
    @Eq (_root_.AlgebraicGeometry.Scheme.Modules.Hom (X := X) P Q)
      (a ≫ (MOD.map f.op.toLoc).toFunctor.map ψ ≫ b)
      (a ≫ (Modules.pullback f).map ψ ≫ b) := rfl

theorem pullback_map_eq {X X' : Scheme.{u}} (f : X ⟶ X') [IsOpenImmersion f] {M N : X'.Modules} (ψ
    : M ⟶ N) :
    (Modules.pullback f).map ψ = (restrictFunctorIsoPullback f).inv.app M ≫ (restrictFunctor
      f).map ψ ≫
      (restrictFunctorIsoPullback f).hom.app N := by
  rw [← Category.assoc, ← (restrictFunctorIsoPullback f).inv.naturality ψ, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

theorem dictM {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctorIsoPullback a').hom.app M ≫
      ((Scheme.Modules.pullbackCongr w.symm).hom.app M ≫ (Scheme.Modules.pullbackComp e a).inv.app
        M) ≫
      (restrictFunctorIsoPullback e).inv.app ((Modules.pullback a).obj M) ≫
      (restrictFunctor e).map ((restrictFunctorIsoPullback a).inv.app M) = castComp e a a' w M := by
  rw [← Mdl_mapComp'_hom_app e a M a' w]
  exact Φ_eq_congr_comp e a a' w M


theorem commZ₀_formal {X₀ X₁ X₂ S : Scheme.{u}} (p₁ : X₀ ⟶ X₁) (p₂ : X₀ ⟶ X₂) (ι₁ : X₁ ⟶ S) (ι₂ :
    X₂ ⟶ S)
    (q₀ : X₀ ⟶ S) [IsOpenImmersion p₁] [IsOpenImmersion p₂] [IsOpenImmersion ι₁] [IsOpenImmersion
      ι₂]
    [IsOpenImmersion q₀] (w₁ : p₁ ≫ ι₁ = q₀) (w₂ : p₂ ≫ ι₂ = q₀) (G : S.Modules) (M₁ : X₁.Modules)
    (M₂ : X₂.Modules) (r₁ : (restrictFunctor ι₁).obj G ⟶ M₁) (r₂ : (restrictFunctor ι₂).obj G ⟶ M₂)
    (ρ₀ : (restrictFunctor p₁).obj M₁ ⟶ (restrictFunctor p₂).obj M₂)
    (φ₀ : (Modules.pullback p₁).obj M₁ ⟶ (Modules.pullback p₂).obj M₂)
    (hφ₀ : (restrictFunctorIsoPullback p₁).hom.app M₁ ≫ φ₀ ≫ (restrictFunctorIsoPullback
      p₂).inv.app M₂ = ρ₀)
    (cs : castComp p₁ ι₁ q₀ w₁ G ≫ (restrictFunctor p₁).map r₁ ≫ ρ₀ =
      castComp p₂ ι₂ q₀ w₂ G ≫ (restrictFunctor p₂).map r₂) :
    (Modules.pullback p₁).map ((restrictFunctorIsoPullback ι₁).inv.app G ≫ r₁) ≫ φ₀ =
      (((Scheme.Modules.pullbackComp p₁ ι₁).hom.app G ≫ (Scheme.Modules.pullbackCongr w₁).hom.app
        G) ≫
        (Scheme.Modules.pullbackCongr w₂.symm).hom.app G ≫ (Scheme.Modules.pullbackComp p₂
          ι₂).inv.app G) ≫
      (Modules.pullback p₂).map ((restrictFunctorIsoPullback ι₂).inv.app G ≫ r₂) := by
  rw [← hφ₀, ← dictM p₁ ι₁ q₀ w₁ G, ← dictM p₂ ι₂ q₀ w₂ G] at cs
  have c0 : (Scheme.Modules.pullbackComp p₁ ι₁).inv.app G ≫ (Scheme.Modules.pullbackComp p₁
    ι₁).hom.app G = 𝟙 _ :=
    Iso.inv_hom_id_app _ _
  refine (cancel_epi ((restrictFunctorIsoPullback q₀).hom.app G ≫
      ((Scheme.Modules.pullbackCongr w₁.symm).hom.app G ≫ (Scheme.Modules.pullbackComp p₁
        ι₁).inv.app G))).mp ?_
  refine (cancel_mono ((restrictFunctorIsoPullback p₂).inv.app M₂)).mp ?_
  simp only [Functor.comp_obj, Functor.map_comp, pullback_map_eq, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id, Scheme.Modules.pullbackCongr, eqToIso.hom,
    eqToHom_app, eqToHom_trans_assoc, reassoc_of% c0] at cs ⊢
  exact cs

theorem gluedIso_hom (k : ι) : (gluedIso U D k).hom =
    (restrictFunctorIsoPullback (incl U k)).inv.app (glued U D) ≫ restrictGluedHom U D k := rfl

-- Transport the restriction square before specializing its schemes to covering opens.
private theorem comm_of_restriction_square {κ : Type u} {S Z : Scheme.{u}}
    {X : κ → Scheme.{u}} (f : ∀ k, X k ⟶ S) (E : MOD.DescentData f)
    (i j : κ) (q : Z ⟶ S) (a : Z ⟶ X i) (b : Z ⟶ X j)
    [IsOpenImmersion q] [IsOpenImmersion a] [IsOpenImmersion b]
    [IsOpenImmersion (f i)] [IsOpenImmersion (f j)]
    (wa : a ≫ f i = q) (wb : b ≫ f j = q) (G : S.Modules)
    (ei : (Modules.pullback (f i)).obj G ≅ E.obj i)
    (ej : (Modules.pullback (f j)).obj G ≅ E.obj j)
    (ri : (restrictFunctor (f i)).obj G ⟶ E.obj i)
    (rj : (restrictFunctor (f j)).obj G ⟶ E.obj j)
    (hei : ei.hom = (restrictFunctorIsoPullback (f i)).inv.app G ≫ ri)
    (hej : ej.hom = (restrictFunctorIsoPullback (f j)).inv.app G ≫ rj)
    (rho : (restrictFunctor a).obj (E.obj i) ⟶ (restrictFunctor b).obj (E.obj j))
    (htrans : (restrictFunctorIsoPullback a).hom.app (E.obj i) ≫
      E.hom q a b wa wb ≫ (restrictFunctorIsoPullback b).inv.app (E.obj j) = rho)
    (cs : castComp a (f i) q wa G ≫ (restrictFunctor a).map ri ≫ rho =
      castComp b (f j) q wb G ≫ (restrictFunctor b).map rj) :
    @Eq (_root_.AlgebraicGeometry.Scheme.Modules.Hom (X := Z)
      ((Modules.pullback a).obj ((Modules.pullback (f i)).obj G))
      ((Modules.pullback b).obj (E.obj j)))
      ((MOD.map a.op.toLoc).toFunctor.map ei.hom ≫ E.hom q a b wa wb)
      (((MOD.toDescentData f).obj G).hom q a b wa wb ≫
        (MOD.map b.op.toLoc).toFunctor.map ej.hom) := by
  let transition : (Modules.pullback a).obj (E.obj i) ⟶
      (Modules.pullback b).obj (E.obj j) := E.hom q a b wa wb
  let canonical : (Modules.pullback a).obj ((Modules.pullback (f i)).obj G) ⟶
      (Modules.pullback b).obj ((Modules.pullback (f j)).obj G) :=
    ((Scheme.Modules.pullbackComp a (f i)).hom.app G ≫
        (Scheme.Modules.pullbackCongr wa).hom.app G) ≫
      (Scheme.Modules.pullbackCongr wb.symm).hom.app G ≫
      (Scheme.Modules.pullbackComp b (f j)).inv.app G
  have hMap₁ : @Eq (_root_.AlgebraicGeometry.Scheme.Modules.Hom (X := Z)
      ((Modules.pullback a).obj ((Modules.pullback (f i)).obj G))
      ((Modules.pullback b).obj (E.obj j)))
      ((MOD.map a.op.toLoc).toFunctor.map ei.hom ≫ transition)
      ((Modules.pullback a).map ei.hom ≫ transition) := by
    exact (Category.id_comp (obj := Z.Modules)
      ((MOD.map a.op.toLoc).toFunctor.map ei.hom ≫ transition)).symm.trans
      ((pseudo_map_map a ei.hom (𝟙 _) transition).trans
        (Category.id_comp (obj := Z.Modules)
          ((Modules.pullback a).map ei.hom ≫ transition)))
  have hMap₂ : @Eq (_root_.AlgebraicGeometry.Scheme.Modules.Hom (X := Z)
      ((Modules.pullback a).obj ((Modules.pullback (f i)).obj G))
      ((Modules.pullback b).obj (E.obj j)))
      (canonical ≫ (MOD.map b.op.toLoc).toFunctor.map ej.hom)
      (canonical ≫ (Modules.pullback b).map ej.hom) := by
    exact ((Category.assoc (obj := Z.Modules)
      canonical ((MOD.map b.op.toLoc).toFunctor.map ej.hom) (𝟙 _)).symm.trans
        (Category.comp_id (obj := Z.Modules)
          (canonical ≫ (MOD.map b.op.toLoc).toFunctor.map ej.hom))).symm.trans
      ((pseudo_map_map b ej.hom canonical (𝟙 _)).trans
        ((Category.assoc (obj := Z.Modules)
          canonical ((Modules.pullback b).map ej.hom) (𝟙 _)).symm.trans
          (Category.comp_id (obj := Z.Modules)
            (canonical ≫ (Modules.pullback b).map ej.hom))))
  have hFormal : (Modules.pullback a).map ei.hom ≫ transition =
      canonical ≫ (Modules.pullback b).map ej.hom := by
    rw [hei, hej]
    exact commZ₀_formal a b (f i) (f j) q wa wb G
      (E.obj i) (E.obj j) ri rj rho transition htrans cs
  have hCanonical : ((MOD.toDescentData f).obj G).hom q a b wa wb ≫
      (MOD.map b.op.toLoc).toFunctor.map ej.hom =
      canonical ≫ (MOD.map b.op.toLoc).toFunctor.map ej.hom := by
    dsimp only [canonical]
    rw [← Mdl_mapComp'_inv_app a (f i) G q wa,
      ← Mdl_mapComp'_hom_app b (f j) G q wb]
    rfl
  exact hMap₁.trans (hFormal.trans (hCanonical.trans hMap₂).symm)

theorem commZ₀ (i j : ι) :
    @Eq (_root_.AlgebraicGeometry.Scheme.Modules.Hom
      (X := ((U i ⊓ U j : Y.Opens) : Scheme.{u}))
      ((Modules.pullback (p₁ U i j)).obj
        ((Modules.pullback (incl U i)).obj (glued U D)))
      ((Modules.pullback (p₂ U i j)).obj (Dobj U D j)))
      ((MOD.map (p₁ U i j).op.toLoc).toFunctor.map (gluedIso U D i).hom ≫
        D.hom (U i ⊓ U j).ι (p₁ U i j) (p₂ U i j)
          (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right))
      (((MOD.toDescentData (incl U)).obj (glued U D)).hom
          (U i ⊓ U j).ι (p₁ U i j) (p₂ U i j)
          (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right) ≫
        (MOD.map (p₂ U i j).op.toLoc).toFunctor.map (gluedIso U D j).hom) := by
  exact comm_of_restriction_square (incl U) D i j (U i ⊓ U j).ι
    (p₁ U i j) (p₂ U i j) (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right)
    (glued U D) (gluedIso U D i) (gluedIso U D j)
    (restrictGluedHom U D i) (restrictGluedHom U D j)
    (gluedIso_hom U D i) (gluedIso_hom U D j) (ρ U D i j).hom
    (τ_hom_eq U D i j (U i ⊓ U j) inf_le_left inf_le_right).symm
    (comm_sections U D i j)

theorem gluedIso_comm ⦃Z : Scheme.{u}⦄ (q : Z ⟶ Y) ⦃i j : ι⦄ (f₁ : Z ⟶ (U i : Scheme.{u})) (f₂ : Z
    ⟶ (U j : Scheme.{u}))
    (h₁ : f₁ ≫ incl U i = q) (h₂ : f₂ ≫ incl U j = q) :
    (MOD.map f₁.op.toLoc).toFunctor.map (gluedIso U D i).hom ≫ D.hom q f₁ f₂ h₁ h₂ =
      ((MOD.toDescentData (incl U)).obj (glued U D)).hom q f₁ f₂ h₁ h₂ ≫
        (MOD.map f₂.op.toLoc).toFunctor.map (gluedIso U D j).hom := by
  have H : Set.range q.base ⊆ Set.range (U i ⊓ U j).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← h₁, ← Scheme.Opens.range_ι (U i)]
      exact ⟨f₁.base z, rfl⟩
    · rw [← h₂, ← Scheme.Opens.range_ι (U j)]
      exact ⟨f₂.base z, rfl⟩
  let φ := IsOpenImmersion.lift (U i ⊓ U j).ι q H
  have hφ : φ ≫ (U i ⊓ U j).ι = q := IsOpenImmersion.lift_fac _ _ _
  have hφ₁ : φ ≫ p₁ U i j = f₁ := by
    rw [← cancel_mono (U i).ι, Category.assoc, Scheme.homOfLE_ι, hφ]; exact h₁.symm
  have hφ₂ : φ ≫ p₂ U i j = f₂ := by
    rw [← cancel_mono (U j).ι, Category.assoc, Scheme.homOfLE_ι, hφ]; exact h₂.symm
  exact CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.comm_of_pullHom
    ((MOD.toDescentData (incl U)).obj (glued U D)) D (gluedIso U D i).hom (gluedIso U D j).hom
    (U i ⊓ U j).ι (p₁ U i j) (p₂ U i j) (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right)
    (commZ₀ U D i j) q f₁ f₂ h₁ h₂ φ hφ hφ₁ hφ₂

/-- The descent-data isomorphism between the glued sheaf and the prescribed datum. -/
noncomputable def isoDescentData : (MOD.toDescentData (incl U)).obj (glued U D) ≅ D :=
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.canonical_iso (F := MOD)
    (incl U) (glued U D) D (fun k => gluedIso U D k)
    (fun _Z q _i _j f₁ f₂ h₁ h₂ => gluedIso_comm U D q f₁ f₂ h₁ h₂)

theorem essSurj_incl : (MOD.toDescentData (incl U)).EssSurj :=
  ⟨fun D => ⟨glued U D, ⟨isoDescentData U D⟩⟩⟩

end Opens

theorem toDescentData_essSurj_of_openCover'
    {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g
      i)]
    (_hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base) :
    (MOD.toDescentData g).EssSurj :=
  (essSurj_iff_of_sieve_eq g (fun O : Ranges g => O.1.ι) (sieve_ofArrows_eq_opensRange g)).mpr
    (essSurj_incl (fun O : Ranges g => O.1))

end AlgebraicGeometry.Scheme.Modules.ObjGlue

open _root_.AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.toDescentData_essSurj_of_openCover
    {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g
      i)]
    (hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base) :
    (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData g).EssSurj :=
  AlgebraicGeometry.Scheme.Modules.ObjGlue.toDescentData_essSurj_of_openCover' g hg
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_toDescentData_essSurj_of_openCover
end ProofImplementation
