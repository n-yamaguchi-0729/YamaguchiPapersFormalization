/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Modules.PresheafInternalHom
import SchemeTheory.Modules.SheafificationMonoidal
import SchemeTheory.Modules.Monoidal
import SchemeTheory.Modules.PresheafPullbackMonoidal
import SchemeTheory.Modules.PullbackMonoidal
import AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import SchemeTheory.Modules.TensorSections
import SchemeTheory.Modules.PullbackLocalSection
import SchemeTheory.Modules.TensorSectionSheafification
import SchemeTheory.Modules.TensorSectionMaps
import Mathlib.Util.WithWeakNamespace

/-!
The tensor-unit pullback isomorphism on the canonical unit section, via monoidal sheafification.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TensorProduct
open _root_.CategoryTheory.Functor.LaxMonoidal
open _root_.CategoryTheory.Functor.OplaxMonoidal

local instance presheafSectionsModule {Z : Scheme.{u}}
    (P : Z.PresheafOfModules) (U : Z.Opens) :
    Module Γ(Z, U) (P.obj (op U)) := (P.obj (op U)).isModule

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace PullbackTensorSections

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local instance : (PresheafOfModules.pushforward.{u}
    (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom.hom).IsRightAdjoint :=
  (PresheafOfModules.PullbackMonoidal.adj (TopologicalSpace.Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c).isRightAdjoint

local instance : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  (Modules.pullbackPushforwardAdjunction f).isRightAdjoint

private abbrev _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.adj (Z :
    Scheme.{u}) : Modules.sheafify Z ⊣
    SheafOfModules.toPMod Z.sheaf.obj Z.ringCatSheaf.property :=
  SheafOfModules.sheafifyAdj Z.sheaf.obj Z.ringCatSheaf.property
open _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections

/-- The forgetful functor from scheme modules to the underlying presheaf modules. -/
abbrev ι (Z : Scheme.{u}) : Z.Modules ⥤ Z.PresheafOfModules := SheafOfModules.toPMod Z.sheaf.obj
    Z.ringCatSheaf.property

private abbrev _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.pf :
    X.PresheafOfModules ⥤ Y.PresheafOfModules :=
  PresheafOfModules.PullbackMonoidal.pf (TopologicalSpace.Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c
open _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections

local instance : (pf f).LaxMonoidal :=
  PresheafOfModules.pushforward_laxMonoidal
    (F := TopologicalSpace.Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

/-- The presheaf pullback-pushforward adjunction for the scheme morphism. -/
abbrev adj₀ : pullback₀ f ⊣ pf f :=
  PresheafOfModules.PullbackMonoidal.adj (TopologicalSpace.Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

/-- The comparison between sheafification followed by pullback and the opposite order. -/
abbrev e : Modules.sheafify Y ⋙ Modules.pullback f ≅ pullback₀ f ⋙ Modules.sheafify X :=
  SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom

/-- Pull a presheaf section back along the original adjunction unit. -/
def pb₀Section (P : Y.PresheafOfModules) (V : Y.Opens) (s : P.obj (op V)) :
    ((pullback₀ f).obj P).obj (op (f ⁻¹ᵁ V)) :=
  ((adj₀ f).unit.app P).app (op V) s

/-- Map a presheaf section to its sheafification along the adjunction unit. -/
def shUnit {Z : Scheme.{u}} (A : Z.PresheafOfModules) (W : Z.Opens) (a : A.obj (op W)) :
    Γ((Modules.sheafify Z).obj A, W) :=
  ((adj Z).unit.app A).app (op W) a

example : pullback₀ f = PresheafOfModules.pullback f.toRingCatSheafHom.hom := rfl
example : adj₀ f = PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom := rfl
example : e f =
    Localization.Lifting.iso (Modules.sheafify Y)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
      (pullback₀ f ⋙ Modules.sheafify X) (Modules.pullback f) := rfl

lemma sheafify_map_app_shUnit {Z : Scheme.{u}} {A A' : Z.PresheafOfModules} (g : A ⟶ A') (W :
    Z.Opens)
    (z : A.obj (op W)) :
    Scheme.Modules.Hom.app ((Modules.sheafify Z).map g) W (shUnit A W z) = shUnit A' W (g.app
      (op W) z) := by
  have h := (adj Z).unit.naturality g
  exact (congr($(h.symm).app (op W) z) :)

lemma counit_app_shUnit (L : Y.Modules) (V : Y.Opens) (s : Γ(L, V)) :
    Scheme.Modules.Hom.app ((adj Y).counit.app L) V (shUnit ((ι Y).obj L) V s) = s := by
  have h := (adj Y).right_triangle_components L
  exact (congr($(h).app (op V) s) :)

lemma homEquiv_symm_app_pb₀Section {A : Y.PresheafOfModules} {B : X.PresheafOfModules}
    (k : A ⟶ (pf f).obj B) (V : Y.Opens) (z : A.obj (op V)) :
    (((adj₀ f).homEquiv A B).symm k).app (op (f ⁻¹ᵁ V)) (pb₀Section f A V z) =
      (k.app (op V) z : B.obj (op (f ⁻¹ᵁ V))) := by
  have h1 := (adj₀ f).homEquiv_unit (X := A) (Y := B) (f := ((adj₀ f).homEquiv A B).symm k)
  have h := (((adj₀ f).homEquiv A B).apply_symm_apply k).symm.trans h1
  exact (congr($(h.symm).app (op V) z) :)

lemma e_hom_app_pullbackLocalSection (P : Y.PresheafOfModules) (V : Y.Opens) (s : P.obj (op V)) :
    Scheme.Modules.Hom.app ((e f).hom.app P) (f ⁻¹ᵁ V) (pullbackLocalSection f (shUnit P V s)) =
      shUnit ((pullback₀ f).obj P) (f ⁻¹ᵁ V) (pb₀Section f P V s) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).comp
      (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom))
    ((PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom).comp
      (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj))) P
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  exact (congr($(h).app (op V) s) :)

lemma e_inv_app_shUnit (P : Y.PresheafOfModules) (V : Y.Opens) (s : P.obj (op V)) :
    Scheme.Modules.Hom.app ((e f).inv.app P) (f ⁻¹ᵁ V) (shUnit ((pullback₀ f).obj P) (f ⁻¹ᵁ V)
      (pb₀Section f P V s)) =
      pullbackLocalSection f (shUnit P V s) := by
  rw [← e_hom_app_pullbackLocalSection]
  change Scheme.Modules.Hom.app ((e f).hom.app P ≫ (e f).inv.app P) (f ⁻¹ᵁ V) _ = _
  rw [Iso.hom_inv_id_app]
  rfl

lemma pb₀_δ_eq (P Q : Y.PresheafOfModules) :
    δ (pullback₀ f) P Q = ((adj₀ f).homEquiv _ _).symm
      (((adj₀ f).unit.app P ⊗ₘ (adj₀ f).unit.app Q) ≫ μ (pf f) _ _) := by
  exact Adjunction.leftAdjointOplaxMonoidal_δ (adj₀ f) P Q

lemma pb₀_δ_app_pb₀Section_tmul (P Q : Y.PresheafOfModules) (V : Y.Opens) (x : P.obj (op V)) (y
    : Q.obj (op V)) :
    (δ (pullback₀ f) P Q).app (op (f ⁻¹ᵁ V)) (pb₀Section f (P ⊗ Q) V (x ⊗ₜ[Γ(Y, V)] y)) =
      (pb₀Section f P V x ⊗ₜ[Γ(X, f ⁻¹ᵁ V)] pb₀Section f Q V y :
        (((pullback₀ f).obj P).obj (op (f ⁻¹ᵁ V)) ⊗[Γ(X, f ⁻¹ᵁ V)] ((pullback₀ f).obj Q).obj (op
          (f ⁻¹ᵁ V)) :)) := by
  rw [pb₀_δ_eq]
  refine (homEquiv_symm_app_pb₀Section f
    (((adj₀ f).unit.app P ⊗ₘ (adj₀ f).unit.app Q) ≫ μ (pf f) _ _) V (x ⊗ₜ[Γ(Y, V)] y)).trans ?_
  change (μ (pf f) ((pullback₀ f).obj P) ((pullback₀ f).obj Q)).app (op V)
    ((((adj₀ f).unit.app P ⊗ₘ (adj₀ f).unit.app Q)).app (op V) (x ⊗ₜ[Γ(Y, V)] y)) = _
  erw [PresheafOfModules.PullbackMonoidal.tensorHom_app_tmul]
  erw [PresheafOfModules.PullbackMonoidal.pf_μ_app_tmul]
  rfl

lemma sheafify_δ_app_shUnit_tmul (A B : X.PresheafOfModules) (W : X.Opens) (a : A.obj (op W)) (b
    : B.obj (op W)) :
    (δ (Modules.sheafify X) A B).app W (shUnit (A ⊗ B) W (a ⊗ₜ[Γ(X, W)] b)) =
      Modules.tensorSections (L := (Modules.sheafify X).obj A) (M := (Modules.sheafify X).obj B)
        (shUnit A W a) (shUnit B W b) := by
  have h := Modules.sheafify_mu_app_tensorSections A B a b
  have h2 := congr($(Functor.Monoidal.μ_δ (Modules.sheafify X) A B).app W
    (Modules.tensorSections (L := (Modules.sheafify X).obj A) (M := (Modules.sheafify X).obj B)
      (shUnit A W a) (shUnit B W b)))
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h2
  change (δ (Modules.sheafify X) A B).app W ((μ (Modules.sheafify X) A B).app W _) = _ at h2
  erw [h] at h2
  exact h2

lemma e_hom_app_tensor_comp_δ (P Q : Y.PresheafOfModules) :
    (e f).hom.app (P ⊗ Q) ≫ δ (pullback₀ f ⋙ Modules.sheafify X) P Q =
      δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫ ((e f).hom.app P ⊗ₘ (e f).hom.app Q) := by
  have : MorphismProperty.ContainsIdentities (C := Y.PresheafOfModules)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj) :=
    MorphismProperty.ContainsIdentities.inverseImage
      (P := (Opens.grothendieckTopology Y).W (A := AddCommGrpCat.{u}))
      (PresheafOfModules.toPresheaf (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
  let := SheafOfModules.presheafW_isMonoidal
    (J := Opens.grothendieckTopology Y) Y.sheaf.obj Y.ringCatSheaf.property
  have hmon : NatTrans.IsMonoidal (F₁ := Modules.sheafify Y ⋙ Modules.pullback f)
      (F₂ := pullback₀ f ⋙ Modules.sheafify X) (e f).hom :=
    Localization.Monoidal.lifting_isMonoidal (Modules.sheafify Y)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
      (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)
  have T := hmon.tensor P Q
  calc (e f).hom.app (P ⊗ Q) ≫ δ (pullback₀ f ⋙ Modules.sheafify X) P Q
      = (δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫ μ (Modules.sheafify Y ⋙
        Modules.pullback f) P Q) ≫
          (e f).hom.app (P ⊗ Q) ≫ δ (pullback₀ f ⋙ Modules.sheafify X) P Q := by
        rw [Functor.Monoidal.δ_μ, Category.id_comp]
    _ = δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫
          (((e f).hom.app P ⊗ₘ (e f).hom.app Q) ≫ μ (pullback₀ f ⋙ Modules.sheafify X) P Q) ≫
            δ (pullback₀ f ⋙ Modules.sheafify X) P Q := by
        rw [← T]; simp only [Category.assoc]
    _ = δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫ ((e f).hom.app P ⊗ₘ (e f).hom.app Q) := by
        rw [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

lemma pf_ε_app (V : Y.Opens) (g : (𝟙_ Y.PresheafOfModules).obj (op V)) :
    (ε (pf f)).app (op V) g = (f.app V (show Γ(Y, V) from g) :
      ((pf f).obj (𝟙_ X.PresheafOfModules)).obj (op V)) := by
  let : (PresheafOfModules.restrictScalars
      (PresheafOfModules.ringCatHom (R := (TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj)
        f.c)).LaxMonoidal :=
    PresheafOfModules.restrictScalars_laxMonoidal
      (R := (TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) (S := Y.sheaf.obj) f.c
  change (ε (PresheafOfModules.restrictScalars
      (PresheafOfModules.ringCatHom (R := (TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj)
        f.c)) ≫
    (PresheafOfModules.restrictScalars
      (PresheafOfModules.ringCatHom (R := (TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj)
        f.c)).map
        (ε (PresheafOfModules.pushforward₀OfCommRingCat (TopologicalSpace.Opens.map f.base)
          X.sheaf.obj))).app
      (op V) g = _
  erw [show ε (PresheafOfModules.pushforward₀OfCommRingCat (TopologicalSpace.Opens.map f.base)
    X.sheaf.obj)
      = 𝟙 _ from rfl, CategoryTheory.Functor.map_id, Category.comp_id]
  erw [ModuleCat.restrictScalars_η]
  rfl

lemma pb₀_η_app_pb₀Section (V : Y.Opens) (g : (𝟙_ Y.PresheafOfModules).obj (op V)) :
    (η (pullback₀ f)).app (op (f ⁻¹ᵁ V)) (pb₀Section f (𝟙_ Y.PresheafOfModules) V g)
      = (f.app V (show Γ(Y, V) from g) : (𝟙_ X.PresheafOfModules).obj (op (f ⁻¹ᵁ V))) := by
  have h : η (pullback₀ f) = ((adj₀ f).homEquiv _ _).symm (ε (pf f)) :=
    Adjunction.leftAdjointOplaxMonoidal_η (adj₀ f)
  rw [h]
  erw [homEquiv_symm_app_pb₀Section f (ε (pf f)) V g]
  exact pf_ε_app f V g

lemma pb₀_ε_app (V : Y.Opens) (g : (𝟙_ Y.PresheafOfModules).obj (op V)) :
    (ε (pullback₀ f)).app (op (f ⁻¹ᵁ V)) (f.app V (show Γ(Y, V) from g) : (𝟙_
      X.PresheafOfModules).obj (op (f ⁻¹ᵁ V)))
      = pb₀Section f (𝟙_ Y.PresheafOfModules) V g := by
  have h1 := pb₀_η_app_pb₀Section f V g
  have h2 := congr($(Functor.Monoidal.η_ε (pullback₀ f)).app (op (f ⁻¹ᵁ V))
    (pb₀Section f (𝟙_ Y.PresheafOfModules) V g))
  change (ε (pullback₀ f)).app (op (f ⁻¹ᵁ V))
      ((η (pullback₀ f)).app (op (f ⁻¹ᵁ V)) (pb₀Section f (𝟙_ Y.PresheafOfModules) V g))
    = pb₀Section f (𝟙_ Y.PresheafOfModules) V g at h2
  rw [h1] at h2
  exact h2

lemma sheafify_ε_app {Z : Scheme.{u}} (W : Z.Opens) (c : Γ(𝟙_ Z.Modules, W)) :
    Scheme.Modules.Hom.app (ε (Modules.sheafify Z)) W c = shUnit (𝟙_ Z.PresheafOfModules) W c := by
  have h1 : Scheme.Modules.Hom.app (η (Modules.sheafify Z)) W (shUnit (𝟙_ Z.PresheafOfModules) W
    c) = c :=
    counit_app_shUnit (𝟙_ Z.Modules) W c
  have h2 := congr($(Functor.Monoidal.η_ε (Modules.sheafify Z)).app W (shUnit (𝟙_
    Z.PresheafOfModules) W c))
  change Scheme.Modules.Hom.app (ε (Modules.sheafify Z)) W
      (Scheme.Modules.Hom.app (η (Modules.sheafify Z)) W (shUnit (𝟙_ Z.PresheafOfModules) W c))
    = shUnit (𝟙_ Z.PresheafOfModules) W c at h2
  rw [h1] at h2
  exact h2


lemma pullback_ε_app_unitSection (V : Y.Opens) :
    Scheme.Modules.Hom.app (ε (Modules.pullback f)) (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ V))
      = pullbackLocalSection f (Modules.unitSection V) := by
  have : MorphismProperty.ContainsIdentities (C := Y.PresheafOfModules)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj) :=
    MorphismProperty.ContainsIdentities.inverseImage
      (P := (Opens.grothendieckTopology Y).W (A := AddCommGrpCat.{u}))
      (PresheafOfModules.toPresheaf (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
  let := SheafOfModules.presheafW_isMonoidal
    (J := Opens.grothendieckTopology Y) Y.sheaf.obj Y.ringCatSheaf.property
  have hε := Localization.Monoidal.functorMonoidalOfComp_ε (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)
  erw [hε, Functor.LaxMonoidal.comp_ε]
  change Scheme.Modules.Hom.app ((Modules.pullback f).map (η (Modules.sheafify Y))) (f ⁻¹ᵁ V)
    (Scheme.Modules.Hom.app ((e f).inv.app (𝟙_ Y.PresheafOfModules)) (f ⁻¹ᵁ V)
      (Scheme.Modules.Hom.app ((Modules.sheafify X).map (ε (pullback₀ f))) (f ⁻¹ᵁ V)
        (Scheme.Modules.Hom.app (ε (Modules.sheafify X)) (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ
          V))))) = _
  rw [sheafify_ε_app]
  have hmap : Scheme.Modules.Hom.app ((Modules.sheafify X).map (ε (pullback₀ f))) (f ⁻¹ᵁ V)
      (shUnit (𝟙_ X.PresheafOfModules) (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ V)))
      = shUnit ((pullback₀ f).obj (𝟙_ Y.PresheafOfModules)) (f ⁻¹ᵁ V)
          ((ε (pullback₀ f)).app (op (f ⁻¹ᵁ V))
            (show (𝟙_ X.PresheafOfModules).obj (op (f ⁻¹ᵁ V)) from Modules.unitSection (f ⁻¹ᵁ
              V))) :=
    sheafify_map_app_shUnit (ε (pullback₀ f)) (f ⁻¹ᵁ V) _
  have h1 : (ε (pullback₀ f)).app (op (f ⁻¹ᵁ V))
      (show (𝟙_ X.PresheafOfModules).obj (op (f ⁻¹ᵁ V)) from Modules.unitSection (f ⁻¹ᵁ V))
        = pb₀Section f (𝟙_ Y.PresheafOfModules) V (Modules.unitSection V) := by
    erw [← pb₀_ε_app f V (Modules.unitSection V)]
    congr 1
    exact ((f.app V).hom.map_one).symm
  erw [hmap, h1, e_inv_app_shUnit, ← pullbackLocalSection_app]
  congr 1
  exact counit_app_shUnit (𝟙_ Y.Modules) V (Modules.unitSection V)

theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection (V : Y.Opens) :
    (pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ V) (pullbackLocalSection f (Modules.unitSection V))
      = Modules.unitSection (f ⁻¹ᵁ V) := by
  rw [← pullback_ε_app_unitSection]
  change Scheme.Modules.Hom.app (ε (Modules.pullback f) ≫ (Functor.Monoidal.εIso
    (Modules.pullback f)).inv)
    (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ V)) = _
  rw [Functor.Monoidal.εIso_inv, Functor.Monoidal.ε_η]
  rfl

theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection' (V : Y.Opens) (g : Γ(𝟙_
    Y.Modules, V)) :
    ((pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ V)) (pullbackLocalSection f g) =
      (show Γ(𝟙_ X.Modules, f ⁻¹ᵁ V) from f.app V (show Γ(Y, V) from g)) := by
  have hg : (show Γ(Y, V) from g) • Modules.unitSection V = g := by
    change (show Γ(Y, V) from g) * 1 = (show Γ(Y, V) from g)
    exact mul_one _
  have key : ((pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ V))
      (pullbackLocalSection f ((show Γ(Y, V) from g) • Modules.unitSection V)) =
        (show Γ(𝟙_ X.Modules, f ⁻¹ᵁ V) from f.app V (show Γ(Y, V) from g)) := by
    rw [pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
      pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection]
    change f.app V (show Γ(Y, V) from g) * 1 = _
    rw [mul_one]
  rw [hg] at key
  exact key

end PullbackTensorSections

end AlgebraicGeometry.Scheme.Modules

end

with_weak_namespace AlgebraicGeometry.Scheme
open Modules in
with_weak_namespace _root_.AlgebraicGeometry.Scheme.Modules
theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
    {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso φ).hom.app (φ ⁻¹ᵁ U)
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ
        (AlgebraicGeometry.Scheme.Modules.unitSection U)) =
    AlgebraicGeometry.Scheme.Modules.unitSection (φ ⁻¹ᵁ U) :=
  PullbackTensorSections.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection φ U
end Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
