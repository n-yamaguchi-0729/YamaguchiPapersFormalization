/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.PresheafInternalHom
import SchemeTheory.Modules.InternalHomSheaf
import SchemeTheory.Modules.SheafificationMonoidal
import SchemeTheory.Modules.Monoidal
import SchemeTheory.Modules.PresheafPullbackMonoidal
import SchemeTheory.Modules.PullbackMonoidal

/-!
# Duals of invertible sheaves of modules

Compatible local generators identify evaluation against the natural-family dual with the
structure sheaf. We compare this model with the categorical dual and prove its invertibility.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_dual

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory.Limits

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

namespace InvertibleDual

open _root_.Opposite
open _root_.PresheafOfModules.InternalHom
open _root_.TensorProduct

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

private noncomputable abbrev dual : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  ihomObj F (𝟙_ _)

/-- Evaluates a module presheaf tensor its natural-family dual by uncurrying the identity. -/
noncomputable abbrev ev : F ⊗ dual F ⟶ 𝟙_ _ := uncurry' F (𝟙 (dual F))

/-- A compatible generator with unique scalar coordinates on all objects below a fixed object. -/
structure TrivializationBelow (X₀ : Cᵒᵖ) where
  /-- The chosen generating section at each object below the fixed object. -/
  gen : ∀ {Y : Cᵒᵖ} (_ : X₀ ⟶ Y), F.obj Y
  /-- Restriction maps carry each chosen generator to the generator at the target. -/
  compat : ∀ {Y Z : Cᵒᵖ} (f : X₀ ⟶ Y) (g : Y ⟶ Z), F.map g (gen f) = gen (f ≫ g)
  /-- Each section has a unique scalar coefficient with respect to its chosen generator. -/
  bij : ∀ {Y : Cᵒᵖ} (f : X₀ ⟶ Y), Function.Bijective (fun a : R.obj Y => a • gen f)

variable {F} {X₀ : Cᵒᵖ} (D : TrivializationBelow F X₀)

namespace TrivializationBelow

/-- Restricts the compatible generator and its scalar coordinates to a smaller region. -/
noncomputable def restrictTo {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : TrivializationBelow F Y where
  gen g := D.gen (f ≫ g)
  compat g g' := by rw [D.compat, Category.assoc]
  bij g := D.bij (f ≫ g)

/-- The linear equivalence sending a scalar to its multiple of the chosen generator. -/
noncomputable def triv {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : R.obj Y ≃ₗ[R.obj Y] F.obj Y :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (R.obj Y) (F.obj Y) (D.gen f)) (D.bij f)

/-- The scalar coordinate of a section with respect to the chosen generator. -/
noncomputable def coord {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : F.obj Y →ₗ[R.obj Y] R.obj Y := (D.triv f).symm

lemma coord_smul_gen {Y : Cᵒᵖ} (f : X₀ ⟶ Y) (x : F.obj Y) : D.coord f x • D.gen f = x :=
  (D.triv f).apply_symm_apply x

lemma coord_gen_smul {Y : Cᵒᵖ} (f : X₀ ⟶ Y) (a : R.obj Y) : D.coord f (a • D.gen f) = a :=
  (D.triv f).symm_apply_apply a

@[scoped simp] lemma coord_gen {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : D.coord f (D.gen f) = 1 := by
  simpa using D.coord_gen_smul f 1

lemma coord_map {Y Z : Cᵒᵖ} (f : X₀ ⟶ Y) (g : Y ⟶ Z) (x : F.obj Y) :
    D.coord (f ≫ g) (F.map g x) = R.map g (D.coord f x) := by
  conv_lhs => rw [← D.coord_smul_gen f x]
  rw [PresheafOfModules.map_smul, D.compat]
  exact D.coord_gen_smul (f ≫ g) _

/-- The natural linear family extracting scalar coordinates from sections. -/
noncomputable def dualGen : (dual F).obj X₀ :=
  ⟨fun Y f => D.coord f, fun Y Z f g x => by
    change R.map g (D.coord f x) = D.coord (f ≫ g) (F.map g x)
    rw [D.coord_map]⟩

@[scoped simp] lemma dualGen_app {Y : Cᵒᵖ} (f : X₀ ⟶ Y) (x : F.obj Y) :
    (D.dualGen).1 f x = D.coord f x := rfl

lemma eq_smul_dualGen (φ : (dual F).obj X₀) :
    φ = (show R.obj X₀ from φ.1 (𝟙 X₀) (D.gen (𝟙 X₀))) • D.dualGen := by
  apply naturalFamilies_ext
  intro Y f x
  erw [InternalHom.smul_app, dualGen_app]
  conv_lhs => rw [← D.coord_smul_gen f x, LinearMap.map_smul]
  have h := InternalHom.naturality φ (𝟙 X₀) f (D.gen (𝟙 X₀))
  rw [D.compat, Category.id_comp] at h
  rw [← h]
  change D.coord f x * R.map f (φ.1 (𝟙 X₀) (D.gen (𝟙 X₀))) =
    R.map f (φ.1 (𝟙 X₀) (D.gen (𝟙 X₀))) * D.coord f x
  exact mul_comm _ _

/-- Sends a scalar to the corresponding multiple of the generator tensor its dual
coordinate family. -/
noncomputable def evInv : R.obj X₀ →ₗ[R.obj X₀] (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀) :=
  LinearMap.toSpanSingleton _ _ (D.gen (𝟙 X₀) ⊗ₜ D.dualGen)

omit D in
lemma ev_app_tmul (x : F.obj X₀) (φ : (dual F).obj X₀) :
    DFunLike.coe (α := (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀ :))
      (β := fun _ => (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
      ((ev F).app X₀).hom (x ⊗ₜ[R.obj X₀] φ) = φ.1 (𝟙 X₀) x :=
  uncurry'_app_tmul F (𝟙 (dual F)) x φ

lemma ev_evInv (a : R.obj X₀) :
    DFunLike.coe (α := (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀ :))
      (β := fun _ => (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
      ((ev F).app X₀).hom (D.evInv a) = a := by
  change (show (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀) →ₗ[R.obj X₀] R.obj X₀ from
      ((ev F).app X₀).hom) (a • (D.gen (𝟙 X₀) ⊗ₜ[R.obj X₀] D.dualGen)) = a
  rw [LinearMap.map_smul]
  erw [ev_app_tmul]
  rw [dualGen_app, coord_gen, smul_eq_mul, mul_one]

lemma evInv_ev (z : (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀)) :
    D.evInv (DFunLike.coe (α := (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀ :)) (β := fun _ =>
      (𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
        ((ev F).app X₀).hom z) = z := by
  let evMap : (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀) →ₗ[R.obj X₀] R.obj X₀ :=
    ((ev F).app X₀).hom
  change D.evInv (evMap z) = z
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | tmul x φ =>
    erw [ev_app_tmul]
    set d : R.obj X₀ := φ.1 (𝟙 X₀) (D.gen (𝟙 X₀)) with hd
    have hx : x = D.coord (𝟙 X₀) x • D.gen (𝟙 X₀) := (D.coord_smul_gen _ x).symm
    have hφ : φ = d • D.dualGen := D.eq_smul_dualGen φ
    have h1 : φ.1 (𝟙 X₀) x = D.coord (𝟙 X₀) x * d := by
      conv_lhs => rw [hx]
      rw [LinearMap.map_smul]
      exact smul_eq_mul (D.coord (𝟙 X₀) x) d
    rw [h1]
    conv_rhs => rw [hx, hφ, TensorProduct.smul_tmul_smul]
    rfl

theorem ev_app_bijective (D : TrivializationBelow F X₀) : Function.Bijective ((ev F).app X₀) :=
  Function.bijective_iff_has_inverse.2 ⟨D.evInv, D.evInv_ev, D.ev_evInv⟩

end TrivializationBelow

variable (F) in
theorem W_ev {J : GrothendieckTopology C} [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (hloc : ∀ (U : C), ∃ (S : Sieve U), S ∈ J U ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), S f → Nonempty (TrivializationBelow F (op V))) :
    J.W ((toPresheaf _).map (ev F)) := by
  have hsurj : Presheaf.IsLocallySurjective J ((toPresheaf _).map (ev F)) := by
    constructor
    intro U s
    obtain ⟨S, hS, hS'⟩ := hloc U
    refine J.superset_covering ?_ hS
    intro V i hi
    obtain ⟨D⟩ := hS' i hi
    obtain ⟨t, ht⟩ := D.ev_app_bijective.2 (((𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).presheaf.map i.op) s)
    exact ⟨t, ht⟩
  have hinj : Presheaf.IsLocallyInjective J ((toPresheaf _).map (ev F)) := by
    constructor
    intro U x y h
    obtain ⟨S, hS, hS'⟩ := hloc U.unop
    refine J.superset_covering ?_ hS
    intro V i hi
    obtain ⟨D⟩ := hS' i hi
    have nx := ConcreteCategory.congr_hom (((toPresheaf _).map (ev F)).naturality i.op) x
    have ny := ConcreteCategory.congr_hom (((toPresheaf _).map (ev F)).naturality i.op) y
    simp only [ConcreteCategory.comp_apply] at nx ny
    change (F ⊗ dual F).presheaf.map i.op x = (F ⊗ dual F).presheaf.map i.op y
    apply D.ev_app_bijective.1
    change ((toPresheaf _).map (ev F)).app _ ((F ⊗ dual F).presheaf.map i.op x) =
      ((toPresheaf _).map (ev F)).app _ ((F ⊗ dual F).presheaf.map i.op y)
    erw [nx, ny, h]
  exact J.W_of_isLocallyBijective _

end InvertibleDual

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

open TopologicalSpace Opposite
open PresheafOfModules.InvertibleDual

variable {X : Scheme.{u}}

/-- Restricts a pullback trivialization along an inclusion of open subsets. -/
noncomputable def trivializationOfLE {U V : X.Opens} (h : V ≤ U) (L : X.Modules)
    (e : (Modules.pullback U.ι).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    (Modules.pullback V.ι).obj L ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf :=
  (Modules.pullbackCongr (X.homOfLE_ι h).symm).app L ≪≫
    ((Modules.pullbackComp (X.homOfLE h) U.ι).symm).app L ≪≫
    (Modules.pullback (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)

/-- The sheaf of natural linear families from a module to the structure sheaf. -/
noncomputable def dualSheaf (L : X.Modules) : X.Modules where
  val := PresheafOfModules.InvertibleDual.dual L.val
  isSheaf := PresheafOfModules.isSheaf_ihomObj L.val _ (SheafOfModules.unit X.ringCatSheaf).isSheaf

variable (U : X.Opens)

/-- The identity map of ring sheaves viewed through the pushforward on an open subset. -/
noncomputable def restrictRingCatSheafHom : (U : Scheme.{u}).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (U : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

/-- Restricts module sheaves using the identity map on the restricted ring sheaf. -/
noncomputable def restrictFunctor' : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom U)

lemma restrictFunctor'_eq : restrictFunctor' U = Modules.restrictFunctor U.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (U.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- Identifies the explicit restriction functor with pullback along the open immersion. -/
noncomputable def restrictFunctor'IsoPullback : restrictFunctor' U ≅ Modules.pullback U.ι :=
  eqToIso (restrictFunctor'_eq U) ≪≫ restrictFunctorIsoPullback U.ι

variable {U} (L : X.Modules)

lemma image_preimage_of_le {V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

section

variable (e : (restrictFunctor' U).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

/-- The section obtained by sending one through the inverse of a restriction trivialization. -/
noncomputable def gen₀ (W : (U : Scheme.{u}).Opens) : L.val.obj (op (U.ι ''ᵁ W)) :=
  (e.inv.val.app (op W)).hom (1 : Γ(U, W))

lemma gen₀_spec (W : (U : Scheme.{u}).Opens) (b : Γ(X, U.ι ''ᵁ W)) :
    (e.inv.val.app (op W)).hom b = b • (show Γ(L, U.ι ''ᵁ W) from gen₀ L e W) := by
  have h := (e.inv.val.app (op W)).hom.map_smul b (1 : Γ(U, W))
  have hunit : (show Γ(U, W) from b) • (1 : Γ(U, W)) = b :=
    (smul_eq_mul (show Γ(U, W) from b) (1 : Γ(U, W))).trans (mul_one _)
  exact (congrArg (e.inv.val.app (op W)).hom hunit).symm.trans h

lemma gen₀_bijective (W : (U : Scheme.{u}).Opens) :
    Function.Bijective
      (fun b : Γ(X, U.ι ''ᵁ W) => b • (show Γ(L, U.ι ''ᵁ W) from gen₀ L e W)) := by
  have h : Function.Bijective ((e.inv.val.app (op W)).hom) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨(e.hom.val.app (op W)).hom, fun b => ?_, fun m => ?_⟩
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

/-- The compatible generators and unique scalar coordinates induced by a restriction
trivialization. -/
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

/-- The sieve of open subsets on which the module admits a compatible generator. -/
def trivSieve (V : X.Opens) : Sieve V where
  arrows W _ := Nonempty (TrivializationBelow L.val (op W))
  downward_closed {W W'} f hf g := by
    obtain ⟨D⟩ := hf
    exact ⟨D.restrictTo g.op⟩

lemma trivSieve_mem (hL : Scheme.Modules.IsInvertible L) (V : X.Opens) :
    trivSieve L V ∈ Opens.grothendieckTopology X V := by
  intro x hx
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hL.1 x
  refine ⟨V ⊓ U, homOfLE inf_le_left, ?_, ⟨hx, hxU⟩⟩
  let e' : (Modules.pullback (V ⊓ U).ι).obj L ≅ SheafOfModules.unit ((V ⊓ U : X.Opens) :
      Scheme.{u}).ringCatSheaf := trivializationOfLE inf_le_right L eU
  exact ⟨trivializationBelow L ((restrictFunctor'IsoPullback (V ⊓ U)).app L ≪≫ e')⟩

scoped instance isIso_sheafify_map_ev (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    IsIso ((Modules.sheafify X).map (ev (R := X.sheaf.obj) L.val)) := by
  have hW : (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map
      (ev (R := X.sheaf.obj) L.val)) :=
    W_ev (R := X.sheaf.obj) L.val (fun V => ⟨trivSieve L V, trivSieve_mem L Fact.out V,
      fun W i hi => hi⟩)
  have h : ((MorphismProperty.isomorphisms _).inverseImage
      (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)))
      (ev (R := X.sheaf.obj) L.val) := by
    rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)]
    exact hW
  exact h

/-- Identifies an invertible module tensor its natural-family dual sheaf with the unit module. -/
noncomputable def tensorDualSheafIso (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    L ⊗ dualSheaf L ≅ 𝟙_ X.Modules :=
  let e : (Modules.sheafify X).obj (L.val ⊗ dual L.val) ≅
      (Modules.sheafify X).obj (𝟙_ _) :=
    let f : (Modules.sheafify X).obj (L.val ⊗ dual (R := X.sheaf.obj) L.val) ⟶
        (Modules.sheafify X).obj (𝟙_ _) :=
      (Modules.sheafify X).map (ev (R := X.sheaf.obj) L.val)
    haveI : IsIso f := isIso_sheafify_map_ev L
    asIso f
  (Scheme.Modules.tensorIsoSheafify L (dualSheaf L)).symm ≪≫
    e ≪≫
    SheafOfModules.sheafifyUnitIso X.sheaf.obj X.ringCatSheaf.property

theorem isInvertible_dualSheaf (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    Scheme.Modules.IsInvertible (dualSheaf L) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := (Fact.out : Scheme.Modules.IsInvertible L).1 x
  refine ⟨U, hxU, ⟨?_⟩⟩
  exact (λ_ _).symm ≪≫ (eU.symm ⊗ᵢ Iso.refl _) ≪≫
    Functor.Monoidal.μIso (Modules.pullback U.ι) L (dualSheaf L) ≪≫
    (Modules.pullback U.ι).mapIso (tensorDualSheafIso L) ≪≫
    pullbackTensorUnitObjIso U.ι

end AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open TopologicalSpace Opposite
open PresheafOfModules.InvertibleDual

variable {X : Scheme.{u}}

variable (X) in
private noncomputable abbrev _root_.AlgebraicGeometry.Scheme.Modules.toPMod :
    X.Modules ⥤ X.PresheafOfModules :=
  SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

open _root_.AlgebraicGeometry.Scheme.Modules

/-- The natural-family dual formed from the canonical presheaf view of a module. -/
noncomputable def dualModel (L : X.Modules) : X.Modules where
  val := PresheafOfModules.InvertibleDual.dual (R := X.sheaf.obj) ((toPMod X).obj L)
  isSheaf := PresheafOfModules.isSheaf_ihomObj _ _ (SheafOfModules.unit X.ringCatSheaf).isSheaf

private noncomputable def identityRestrictionIso
    {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ RingCat.{u})
    (M : _root_.PresheafOfModules.{u} R) :
    (_root_.PresheafOfModules.restrictScalars (𝟙 R)).obj M ≅ M := by
  let app (U : Cᵒᵖ) :
      ((_root_.PresheafOfModules.restrictScalars (𝟙 R)).obj M).obj U ≅ M.obj U :=
    ModuleCat.restrictScalarsId'App (((𝟙 R : R ⟶ R).app U).hom)
      (show ((𝟙 R : R ⟶ R).app U).hom = RingHom.id (R.obj U) from RingCat.hom_id)
      (M.obj U)
  have happ (U : Cᵒᵖ) (x : M.obj U) : (app U).hom x = x :=
    ModuleCat.restrictScalarsId'App_hom_apply (((𝟙 R : R ⟶ R).app U).hom)
      (show ((𝟙 R : R ⟶ R).app U).hom = RingHom.id (R.obj U) from RingCat.hom_id)
      (M.obj U) x
  refine _root_.PresheafOfModules.isoMk
    (M₁ := (_root_.PresheafOfModules.restrictScalars (𝟙 R)).obj M)
    (M₂ := M) app ?_
  intro U V g
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (app V).hom (M.map g x) = M.map g ((app U).hom x)
  exact (happ V (M.map g x)).trans
    (congrArg (fun y : M.obj U => M.map g y) (happ U x).symm)

/-- Identifies the categorical dual with the sheafification of its natural-family model. -/
noncomputable def dualIsoSheafifyModel (L : X.Modules) :
    Scheme.Modules.dual L ≅ (Modules.sheafify X).obj ((toPMod X).obj (dualModel L)) := by
  let R : (X.Opens)ᵒᵖ ⥤ RingCat.{u} := X.ringCatSheaf.obj
  let F : X.PresheafOfModules := (toPMod X).obj L
  let H : X.PresheafOfModules ⥤ X.PresheafOfModules :=
    _root_.PresheafOfModules.ihomFunctor (R := X.sheaf.obj) F
  let eUnit : (toPMod X).obj (𝟙_ X.Modules) ≅ (𝟙_ X.PresheafOfModules) :=
    (toPMod X).mapIso (eqToIso (Scheme.Modules.tensorUnit_eq (X := X))) ≪≫
      identityRestrictionIso R (SheafOfModules.unit X.ringCatSheaf).val
  let eFamily : H.obj ((toPMod X).obj (𝟙_ X.Modules)) ≅ (dualModel L).val :=
    H.mapIso eUnit
  let eRestrict : (dualModel L).val ≅ (toPMod X).obj (dualModel L) :=
    (identityRestrictionIso R (dualModel L).val).symm
  change (Modules.sheafify X).obj (H.obj ((toPMod X).obj (𝟙_ X.Modules))) ≅
    (Modules.sheafify X).obj ((toPMod X).obj (dualModel L))
  exact (Modules.sheafify X).mapIso (eFamily ≪≫ eRestrict)

/-- Identifies the categorical dual with its natural-family dual sheaf via the
sheafification counit. -/
noncomputable def dualIsoModel (L : X.Modules) : Scheme.Modules.dual L ≅ dualModel L :=
  dualIsoSheafifyModel L ≪≫
    SheafOfModules.sheafifyCounitIso X.sheaf.obj X.ringCatSheaf.property (dualModel L)

end AlgebraicGeometry.Scheme.Modules

namespace PresheafOfModules.InvertibleDual.TrivializationBelow

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X : _root_.AlgebraicGeometry.Scheme.{u}}

/-- Views a compatible generator in the canonical presheaf presentation of a module sheaf. -/
noncomputable def toPMod
    {L : X.Modules} {X₀ : (X.Opens)ᵒᵖ} (D : TrivializationBelow (R := X.sheaf.obj) L.val X₀) :
    TrivializationBelow (R := X.sheaf.obj) ((toPMod X).obj L) X₀ where
  gen f := D.gen f
  compat f g := D.compat f g
  bij f := D.bij f

end PresheafOfModules.InvertibleDual.TrivializationBelow

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open TopologicalSpace Opposite
open PresheafOfModules.InvertibleDual

variable {X : Scheme.{u}}

scoped instance isIso_sheafify_map_ev_model (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    IsIso ((Modules.sheafify X).map (ev (R := X.sheaf.obj) ((toPMod X).obj L))) := by
  have hW : (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map
      (ev (R := X.sheaf.obj) ((toPMod X).obj L))) :=
    W_ev (R := X.sheaf.obj) ((toPMod X).obj L) (fun V => ⟨trivSieve L V,
      trivSieve_mem L Fact.out V, fun W i hi => by obtain ⟨D⟩ := hi; exact ⟨D.toPMod⟩⟩)
  have h : ((MorphismProperty.isomorphisms _).inverseImage
      (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)))
      (ev (R := X.sheaf.obj) ((toPMod X).obj L)) := by
    rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)]
    exact hW
  exact h

/-- Trivializes an invertible module tensor its natural-family dual model using evaluation. -/
noncomputable def tensorDualModelIso (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    L ⊗ dualModel L ≅ 𝟙_ X.Modules :=
  let e : (Modules.sheafify X).obj (((toPMod X).obj L) ⊗ dual ((toPMod X).obj L)) ≅
      (Modules.sheafify X).obj (𝟙_ _) :=
    let f : (Modules.sheafify X).obj
        (((toPMod X).obj L) ⊗ dual (R := X.sheaf.obj) ((toPMod X).obj L)) ⟶
        (Modules.sheafify X).obj (𝟙_ _) :=
      (Modules.sheafify X).map (ev (R := X.sheaf.obj) ((toPMod X).obj L))
    haveI : IsIso f := isIso_sheafify_map_ev_model L
    asIso f
  (Scheme.Modules.tensorIsoSheafify L (dualModel L)).symm ≪≫
    e ≪≫
    SheafOfModules.sheafifyUnitIso X.sheaf.obj X.ringCatSheaf.property

/-- Trivializes an invertible module tensor its categorical dual through the
natural-family model. -/
noncomputable def tensorDualIso (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    L ⊗ Scheme.Modules.dual L ≅ 𝟙_ X.Modules :=
  (Iso.refl L ⊗ᵢ dualIsoModel L) ≪≫ tensorDualModelIso L

theorem isInvertible_dual (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    Scheme.Modules.IsInvertible (Scheme.Modules.dual L) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := (Fact.out : Scheme.Modules.IsInvertible L).1 x
  refine ⟨U, hxU, ⟨?_⟩⟩
  exact (λ_ _).symm ≪≫ (eU.symm ⊗ᵢ Iso.refl _) ≪≫
    Functor.Monoidal.μIso (Modules.pullback U.ι) L (Scheme.Modules.dual L) ≪≫
    (Modules.pullback U.ι).mapIso (tensorDualIso L) ≪≫
    pullbackTensorUnitObjIso U.ι

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.dual
    {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible (AlgebraicGeometry.Scheme.Modules.dual L) ∧
      Nonempty (L ⊗ AlgebraicGeometry.Scheme.Modules.dual L ≅ 𝟙_ X.Modules) :=
  haveI : Fact (Scheme.Modules.IsInvertible L) := ⟨hL⟩
  ⟨isInvertible_dual L, ⟨tensorDualIso L⟩⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_dual
end ProofImplementation

namespace PresheafOfModules.PullbackMonoidal

attribute [-instance]
  pullback_monoidal
  isIso_δ

end PresheafOfModules.PullbackMonoidal

namespace PresheafOfModules

attribute [-instance]
  pushforward_laxMonoidal

end PresheafOfModules

namespace PresheafOfModules.PullbackMonoidal

attribute [-instance]
  isIso_η

end PresheafOfModules.PullbackMonoidal

namespace PresheafOfModules

attribute [-instance]
  free_monoidal
  restrictScalars_laxMonoidal

end PresheafOfModules

namespace PresheafOfModules.PullbackMonoidal

attribute [-instance]
  isIso_δ_gS

end PresheafOfModules.PullbackMonoidal

namespace PresheafOfModules

attribute [-instance]
  pullback_oplaxMonoidal

end PresheafOfModules

namespace PresheafOfModules.PullbackMonoidal

attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb

end PresheafOfModules.PullbackMonoidal

namespace PresheafOfModules

attribute [-instance]
  pullback_monoidal'

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

attribute [-instance]
  preservesBinaryProducts_opensMap
  pullback_monoidal
  sheafify_isLocalization'
  preservesTerminal_opensMap
  pullback₀_monoidal
  preservesFiniteProducts_opensMap
  sheafifyPullback_lifting

end AlgebraicGeometry.Scheme.Modules

attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
