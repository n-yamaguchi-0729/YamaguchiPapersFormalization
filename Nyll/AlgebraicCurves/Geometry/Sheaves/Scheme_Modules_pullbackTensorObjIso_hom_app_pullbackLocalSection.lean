/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.PresheafInternalHom
import Nyll.SchemeTheory.Modules.SheafificationMonoidal
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PresheafPullbackMonoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.SchemeTheory.Modules.PullbackLocalSection
import Nyll.SchemeTheory.Modules.TensorSectionSheafification
import Nyll.SchemeTheory.Modules.TensorSectionMaps

/-!
# Scheme Modules pullback Tensor Obj Iso hom app pullback Local Section
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection

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

private abbrev _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.adj (Z : Scheme.{u})
  : Modules.sheafify Z ⊣
    SheafOfModules.toPMod Z.sheaf.obj Z.ringCatSheaf.property :=
  SheafOfModules.sheafifyAdj Z.sheaf.obj Z.ringCatSheaf.property
open _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections

/-- Forget a sheaf of modules on `Z` to its underlying presheaf of modules. -/
abbrev ι (Z : Scheme.{u}) : Z.Modules ⥤ Z.PresheafOfModules :=
  SheafOfModules.toPMod Z.sheaf.obj Z.ringCatSheaf.property

private abbrev _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.pf :
  X.PresheafOfModules ⥤ Y.PresheafOfModules :=
  PresheafOfModules.PullbackMonoidal.pf (TopologicalSpace.Opens.map f.base)
  (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c
open _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections

local instance : (pf f).LaxMonoidal :=
  PresheafOfModules.pushforward_laxMonoidal
    (F := TopologicalSpace.Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

/-- The pullback-pushforward adjunction for presheaves of modules along `f`. -/
abbrev adj₀ : pullback₀ f ⊣ pf f := PresheafOfModules.PullbackMonoidal.adj
  (TopologicalSpace.Opens.map f.base)
  (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

/-- The canonical isomorphism commuting sheafification with pullback along `f`. -/
abbrev e : Modules.sheafify Y ⋙ Modules.pullback f ≅ pullback₀ f ⋙ Modules.sheafify X :=
  SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom

/-- Pull back a presheaf section through the unit of the presheaf pullback adjunction. -/
def pb₀Section (P : Y.PresheafOfModules) (V : Y.Opens) (s : P.obj (op V)) :
    ((pullback₀ f).obj P).obj (op (f ⁻¹ᵁ V)) :=
  ((adj₀ f).unit.app P).app (op V) s

/-- Send a presheaf section to its sheafification through the sheafification unit. -/
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
    Scheme.Modules.Hom.app ((Modules.sheafify Z).map g) W (shUnit A W z) = shUnit A' W (g.app (op
      W) z) := by
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

lemma pb₀_δ_app_pb₀Section_tmul (P Q : Y.PresheafOfModules) (V : Y.Opens) (x : P.obj (op V)) (y :
  Q.obj (op V)) :
    (δ (pullback₀ f) P Q).app (op (f ⁻¹ᵁ V)) (pb₀Section f (P ⊗ Q) V (x ⊗ₜ[Γ(Y, V)] y)) =
      (pb₀Section f P V x ⊗ₜ[Γ(X, f ⁻¹ᵁ V)] pb₀Section f Q V y :
        TensorProduct (Γ(X, f ⁻¹ᵁ V))
          (((pullback₀ f).obj P).obj (op (f ⁻¹ᵁ V)))
          (((pullback₀ f).obj Q).obj (op (f ⁻¹ᵁ V)))) := by
  rw [pb₀_δ_eq]
  refine (homEquiv_symm_app_pb₀Section f
    (((adj₀ f).unit.app P ⊗ₘ (adj₀ f).unit.app Q) ≫ μ (pf f) _ _) V (x ⊗ₜ[Γ(Y, V)] y)).trans ?_
  change (μ (pf f) ((pullback₀ f).obj P) ((pullback₀ f).obj Q)).app (op V)
    ((((adj₀ f).unit.app P ⊗ₘ (adj₀ f).unit.app Q)).app (op V) (x ⊗ₜ[Γ(Y, V)] y)) = _
  erw [PresheafOfModules.PullbackMonoidal.tensorHom_app_tmul]
  erw [PresheafOfModules.PullbackMonoidal.pf_μ_app_tmul]
  rfl

lemma sheafify_δ_app_shUnit_tmul (A B : X.PresheafOfModules) (W : X.Opens) (a : A.obj (op W)) (b :
  B.obj (op W)) :
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
      = (δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫ μ (Modules.sheafify Y ⋙ Modules.pullback
        f) P Q) ≫
          (e f).hom.app (P ⊗ Q) ≫ δ (pullback₀ f ⋙ Modules.sheafify X) P Q := by
        rw [Functor.Monoidal.δ_μ, Category.id_comp]
    _ = δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫
          (((e f).hom.app P ⊗ₘ (e f).hom.app Q) ≫ μ (pullback₀ f ⋙ Modules.sheafify X) P Q) ≫
            δ (pullback₀ f ⋙ Modules.sheafify X) P Q := by
        rw [← T]; simp only [Category.assoc]
    _ = δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫ ((e f).hom.app P ⊗ₘ (e f).hom.app Q) := by
        rw [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

/-- Identify the sheafification of the tensor product of underlying presheaves with the tensor
product of the original sheaves. -/
def cmpIso (L M : Y.Modules) : (Modules.sheafify Y).obj ((ι Y).obj L ⊗ (ι Y).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M)).symm ≪≫
    (SheafOfModules.sheafifyCounitIso Y.sheaf.obj Y.ringCatSheaf.property L ⊗ᵢ
      SheafOfModules.sheafifyCounitIso Y.sheaf.obj Y.ringCatSheaf.property M)

lemma cmpIso_hom (L M : Y.Modules) :
    (cmpIso L M).hom = δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M) ≫
      ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M) := rfl

lemma tensorSections_eq (L M : Y.Modules) (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)) :
    Modules.tensorSections s t = Scheme.Modules.Hom.app (cmpIso L M).hom V
      (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op
        V)))) := rfl

lemma δ_sheafify_comp_pullback_eq (P Q : Y.PresheafOfModules) :
    δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q =
      (e f).hom.app (P ⊗ Q) ≫
        ((Modules.sheafify X).map (δ (pullback₀ f) P Q) ≫
          δ (Modules.sheafify X) ((pullback₀ f).obj P) ((pullback₀ f).obj Q)) ≫
        ((e f).inv.app P ⊗ₘ (e f).inv.app Q) := by
  rw [← Functor.OplaxMonoidal.comp_δ, ← Category.assoc, e_hom_app_tensor_comp_δ, Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app,
    MonoidalCategory.id_tensorHom_id, Category.comp_id]

lemma δ_sheafify_comp_pullback_app_shUnit_tmul (P Q : Y.PresheafOfModules) (V : Y.Opens)
    (x : P.obj (op V)) (y : Q.obj (op V)) :
    Scheme.Modules.Hom.app (δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q) (f ⁻¹ᵁ V)
      (pullbackLocalSection f (shUnit (P ⊗ Q) V (x ⊗ₜ[Γ(Y, V)] y))) =
      Modules.tensorSections (pullbackLocalSection f (shUnit P V x))
        (pullbackLocalSection f (shUnit Q V y)) := by
  let invTensor : Γ((Modules.sheafify X).obj ((pullback₀ f).obj P) ⊗
      (Modules.sheafify X).obj ((pullback₀ f).obj Q), f ⁻¹ᵁ V) →
      Γ((Modules.pullback f).obj ((Modules.sheafify Y).obj P) ⊗
        (Modules.pullback f).obj ((Modules.sheafify Y).obj Q), f ⁻¹ᵁ V) :=
    Scheme.Modules.Hom.app ((e f).inv.app P ⊗ₘ (e f).inv.app Q) (f ⁻¹ᵁ V)
  let shDelta : Γ((Modules.sheafify X).obj ((pullback₀ f).obj P ⊗ (pullback₀ f).obj Q), f ⁻¹ᵁ V) →
      Γ((Modules.sheafify X).obj ((pullback₀ f).obj P) ⊗
        (Modules.sheafify X).obj ((pullback₀ f).obj Q), f ⁻¹ᵁ V) :=
    Scheme.Modules.Hom.app (δ (Modules.sheafify X) ((pullback₀ f).obj P) ((pullback₀ f).obj Q)) (f
      ⁻¹ᵁ V)
  let shMap : Γ((Modules.sheafify X).obj ((pullback₀ f).obj (P ⊗ Q)), f ⁻¹ᵁ V) →
      Γ((Modules.sheafify X).obj ((pullback₀ f).obj P ⊗ (pullback₀ f).obj Q), f ⁻¹ᵁ V) :=
    Scheme.Modules.Hom.app ((Modules.sheafify X).map (δ (pullback₀ f) P Q)) (f ⁻¹ᵁ V)
  have hE := e_hom_app_pullbackLocalSection f (P ⊗ Q) V (x ⊗ₜ[Γ(Y, V)] y)
  have hMap := sheafify_map_app_shUnit (δ (pullback₀ f) P Q) (f ⁻¹ᵁ V)
    (pb₀Section f (P ⊗ Q) V (x ⊗ₜ[Γ(Y, V)] y))
  have hPB := pb₀_δ_app_pb₀Section_tmul f P Q V x y
  have hDelta := sheafify_δ_app_shUnit_tmul ((pullback₀ f).obj P) ((pullback₀ f).obj Q)
    (f ⁻¹ᵁ V) (pb₀Section f P V x) (pb₀Section f Q V y)
  have hInv := Modules.tensorHom_app_tensorSections ((e f).inv.app P) ((e f).inv.app Q)
    (shUnit ((pullback₀ f).obj P) (f ⁻¹ᵁ V) (pb₀Section f P V x))
    (shUnit ((pullback₀ f).obj Q) (f ⁻¹ᵁ V) (pb₀Section f Q V y))
  rw [δ_sheafify_comp_pullback_eq]
  change invTensor (shDelta (shMap (Scheme.Modules.Hom.app ((e f).hom.app (P ⊗ Q))
    (f ⁻¹ᵁ V) (pullbackLocalSection f (shUnit (P ⊗ Q) V (x ⊗ₜ[Γ(Y, V)] y)))))) = _
  refine (congrArg (fun z => invTensor (shDelta (shMap z))) hE).trans ?_
  refine (congrArg (fun z => invTensor (shDelta z)) hMap).trans ?_
  refine (congrArg (fun z => invTensor (shDelta (shUnit ((pullback₀ f).obj P ⊗
    (pullback₀ f).obj Q) (f ⁻¹ᵁ V) z))) hPB).trans ?_
  refine (congrArg invTensor hDelta).trans ?_
  refine hInv.trans ?_
  exact congrArg₂ (fun a : Γ((Modules.pullback f).obj ((Modules.sheafify Y).obj P), f ⁻¹ᵁ V) =>
      fun b : Γ((Modules.pullback f).obj ((Modules.sheafify Y).obj Q), f ⁻¹ᵁ V) =>
        Modules.tensorSections a b)
    (e_inv_app_shUnit f P V x) (e_inv_app_shUnit f Q V y)

theorem pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections (L M : Y.Modules) (V :
  Y.Opens)
    (s : Γ(L, V)) (t : Γ(M, V)) :
    ((pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V)) (pullbackLocalSection f
      (Modules.tensorSections s t)) =
      Modules.tensorSections (pullbackLocalSection f s) (pullbackLocalSection f t) := by
  have hnat := Functor.OplaxMonoidal.δ_natural (Modules.pullback f)
    ((adj Y).counit.app L) ((adj Y).counit.app M)
  have key := δ_sheafify_comp_pullback_app_shUnit_tmul f ((ι Y).obj L) ((ι Y).obj M) V s t
  calc ((pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V)) (pullbackLocalSection f
    (Modules.tensorSections s t))
      = Scheme.Modules.Hom.app (δ (Modules.pullback f) L M) (f ⁻¹ᵁ V)
          (Scheme.Modules.Hom.app ((Modules.pullback f).map ((adj Y).counit.app L ⊗ₘ (adj
            Y).counit.app M))
              (f ⁻¹ᵁ V)
            (Scheme.Modules.Hom.app ((Modules.pullback f).map
                (δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M))) (f ⁻¹ᵁ V)
              (pullbackLocalSection f (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
                ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))))) := by
        rw [tensorSections_eq, cmpIso_hom]
        have a1 := pullbackLocalSection_app f ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M)
          (Scheme.Modules.Hom.app (δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M)) V
            (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
              ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))))
        have a2 := pullbackLocalSection_app f (δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M))
          (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
            ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))
        change (pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V) (pullbackLocalSection f
          (Scheme.Modules.Hom.app ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M) V
            (Scheme.Modules.Hom.app (δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M)) V
              (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
                ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))))) = _
        refine (congrArg (fun w => (pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V) w)
          (a1.trans (congrArg (fun w => Scheme.Modules.Hom.app
            ((Modules.pullback f).map ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M)) (f ⁻¹ᵁ V) w)
              a2))).trans ?_
        rfl
    _ = Scheme.Modules.Hom.app ((Modules.pullback f).map ((adj Y).counit.app L) ⊗ₘ
            (Modules.pullback f).map ((adj Y).counit.app M)) (f ⁻¹ᵁ V)
          (Scheme.Modules.Hom.app (δ (Modules.pullback f) _ _) (f ⁻¹ᵁ V)
            (Scheme.Modules.Hom.app ((Modules.pullback f).map
                (δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M))) (f ⁻¹ᵁ V)
              (pullbackLocalSection f (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
                ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))))) :=
        (congr($(hnat.symm).app (f ⁻¹ᵁ V) _) :)
    _ = Scheme.Modules.Hom.app ((Modules.pullback f).map ((adj Y).counit.app L) ⊗ₘ
            (Modules.pullback f).map ((adj Y).counit.app M)) (f ⁻¹ᵁ V)
          (Scheme.Modules.Hom.app (δ (Modules.sheafify Y ⋙ Modules.pullback f) ((ι Y).obj L) ((ι
            Y).obj M))
              (f ⁻¹ᵁ V)
            (pullbackLocalSection f (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V
              ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))))) := by
        rw [Functor.OplaxMonoidal.comp_δ]
        rfl
    _ = Scheme.Modules.Hom.app ((Modules.pullback f).map ((adj Y).counit.app L) ⊗ₘ
            (Modules.pullback f).map ((adj Y).counit.app M)) (f ⁻¹ᵁ V)
          (Modules.tensorSections (pullbackLocalSection f (shUnit ((ι Y).obj L) V s))
            (pullbackLocalSection f (shUnit ((ι Y).obj M) V t))) := by rw [key]
    _ = Modules.tensorSections (pullbackLocalSection f s) (pullbackLocalSection f t) := by
        erw [Modules.tensorHom_app_tensorSections]
        have hL := (pullbackLocalSection_app f ((adj Y).counit.app L)
          (shUnit ((ι Y).obj L) V s)).symm.trans
            (congrArg (pullbackLocalSection f) (counit_app_shUnit L V s))
        have hM := (pullbackLocalSection_app f ((adj Y).counit.app M)
          (shUnit ((ι Y).obj M) V t)).symm.trans
            (congrArg (pullbackLocalSection f) (counit_app_shUnit M V t))
        exact congrArg₂ (fun a : Γ((Modules.pullback f).obj L, f ⁻¹ᵁ V) =>
          fun b : Γ((Modules.pullback f).obj M, f ⁻¹ᵁ V) => Modules.tensorSections a b) hL hM

end PullbackTensorSections

end AlgebraicGeometry.Scheme.Modules

end

open _root_.AlgebraicGeometry AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection
  {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⟶ Y) {L M : Y.Modules} {U : Y.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso φ L M).hom.app (φ ⁻¹ᵁ U)
        (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ
          (AlgebraicGeometry.Scheme.Modules.tensorSections s t)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ s)
        (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ t) :=
  PullbackTensorSections.pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections φ L M U s
    t
end Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
