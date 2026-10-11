/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_isUnit_transition_and_transition_face_mul_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.CechObstruction
import Nyll.SchemeTheory.Modules.PullbackLocalSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop

/-!
# Unit transition functions and the Čech cocycle identity

The transition functions of a module trivialisation are units and satisfy the cocycle identity.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivIsUnit

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace


universe u

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry
  (Scheme.Modules.pullback
    Scheme.Hom
    Scheme.Modules.Hom.comp_app
    Scheme.Modules.Hom
    Scheme
    Scheme.Modules.Hom.id_app
    Scheme.Modules.Hom.app
    Scheme.Hom.appTop
    Scheme.Opens.topIso_hom
    Scheme.homOfLE_homOfLE
    Scheme.homOfLE_app
    Scheme.Modules
    Scheme.Opens
    Scheme.Modules.CechTrivialisation
    Scheme.Modules.homEquiv_symm_app_pullbackLocalSection
    Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme
  (ringCatSheaf
    Modules.pullback
    Hom.id_app
    Hom
    Γ
    Modules.Hom.comp_app
    Hom.app
    topIso_hom
    Modules.Hom
    topIso
    Modules.Hom.id_app
    Modules.Hom.app
    Hom.appTop
    Opens.topIso_hom
    homOfLE_homOfLE
    Hom.comp_app
    homOfLE_app
    Modules
    Opens
    homOfLE_ι
    restrict
    PresheafOfModules
    OrderedAffineCover
    Modules.CechTrivialisation
    Modules.homEquiv_symm_app_pullbackLocalSection
    Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules
  (pullback
    presheaf
    Hom.comp_app
    Hom
    pseudofunctor_associativity
    Hom.id_app
    Hom.app
    pullbackCongr
    pullbackPushforwardAdjunction
    restrict
    map_smul
    pullbackComp
    pullbackUnitIso
    unitAutSection
    CechTrivialisation
    pullbackLocalSection
    pullbackLocalSection_app
    homEquiv_symm_app_pullbackLocalSection
    pullbackComp_hom_app_comp_pullbackUnitIso_hom)


open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry


variable {Y : Scheme.{u}}

/-- Evaluate an automorphism of the unit module on a section over an open subscheme. -/
noncomputable def uapp (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W :
      Scheme.{u}).ringCatSheaf)
    (x : (W : Scheme.{u}).presheaf.obj (op ⊤)) : (W : Scheme.{u}).presheaf.obj (op ⊤) :=
  (e.hom.val.app (op ⊤)).hom x

theorem unitAutSection_eq (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W :
      Scheme.{u}).ringCatSheaf) :
    unitAutSection W e = W.topIso.hom.hom (uapp W e 1) := rfl

theorem uapp_mul (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W :
      Scheme.{u}).ringCatSheaf)
    (x y : (W : Scheme.{u}).presheaf.obj (op ⊤)) : uapp W e (x * y) = x * uapp W e y :=
  ((e.hom.val.app (op ⊤)).hom).map_smul (show ((W : Scheme.{u}).ringCatSheaf.obj.obj (op ⊤)) from
    x) y

theorem uapp_trans (W : Y.Opens)
    (e e' : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W :
      Scheme.{u}).ringCatSheaf)
    (x : (W : Scheme.{u}).presheaf.obj (op ⊤)) : uapp W (e ≪≫ e') x = uapp W e' (uapp W e x) := by
  simp only [uapp, Iso.trans_hom, SheafOfModules.comp_val, PresheafOfModules.comp_app]
  rfl

theorem uapp_refl (W : Y.Opens) (x : (W : Scheme.{u}).presheaf.obj (op ⊤)) : uapp W (Iso.refl _)
  x = x := by
  simp only [uapp, Iso.refl_hom, SheafOfModules.id_val, PresheafOfModules.id_app]
  rfl

theorem unitAutSection_trans (W : Y.Opens)
    (e e' : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W :
      Scheme.{u}).ringCatSheaf) :
    unitAutSection W (e ≪≫ e') = unitAutSection W e * unitAutSection W e' := by
  rw [unitAutSection_eq, unitAutSection_eq, unitAutSection_eq, ← map_mul, uapp_trans, ← uapp_mul,
    mul_one]

theorem unitAutSection_refl (W : Y.Opens) :
    unitAutSection W (Iso.refl _) = 1 := by
  rw [unitAutSection_eq, uapp_refl, map_one]

theorem unitAutSection_symm_mul (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W :
      Scheme.{u}).ringCatSheaf) :
    unitAutSection W e.symm * unitAutSection W e = 1 := by
  rw [← unitAutSection_trans, Iso.symm_self_id, unitAutSection_refl]

theorem unitAutSection_mul_symm (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W :
      Scheme.{u}).ringCatSheaf) :
    unitAutSection W e * unitAutSection W e.symm = 1 := by
  rw [← unitAutSection_trans, Iso.self_symm_id, unitAutSection_refl]

theorem isUnit_unitAutSection (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W :
      Scheme.{u}).ringCatSheaf) :
    IsUnit (unitAutSection W e) :=
  ⟨⟨_, _, unitAutSection_mul_symm W e, unitAutSection_symm_mul W e⟩, rfl⟩

end AlgebraicGeometry.Scheme.Modules

namespace PV1TL

section coh


open _root_.AlgebraicGeometry.Scheme.Modules
open SchemeModulesCechTrivIsUnit.AlgebraicGeometry.Scheme.Modules


variable {T' T A' : Scheme.{u}}

lemma pullbackCongr_hom_app_eq {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (pullbackCongr H).hom.app N = eqToHom (by rw [H]) := by
  subst H
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, eqToHom_refl]

lemma pullbackCongr_inv_app_eq {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (pullbackCongr H).inv.app N = eqToHom (by rw [H]) := by
  subst H
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, eqToHom_refl]

lemma assoc_app {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app N) ≫
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj N) ≫ (pullbackComp (f ≫ g)
        h).hom.app N =
    (pullbackComp f (g ≫ h)).hom.app N ≫ eqToHom (by rw [Category.assoc]) := by
  have := NatTrans.congr_app (pseudofunctor_associativity f g h) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app,
    eqToHom_app] at this
  erw [Category.id_comp] at this
  exact (Iso.inv_comp_eq ((pullbackComp f (g ≫ h)).app N)).1 this

lemma assoc_app'' {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app N) =
      (pullbackComp f (g ≫ h)).hom.app N ≫ eqToHom (by rw [Category.assoc]) ≫ (pullbackComp (f ≫
        g) h).inv.app N ≫
        (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj N) := by
  let A : T'.Modules :=
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N)
  let B : T'.Modules :=
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback
      h).obj N))
  let C : T'.Modules :=
    (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N)
  let D : T'.Modules := (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N
  let E : T'.Modules := (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N
  let a : A ⟶ B := (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app N)
  let b : B ≅ C := (pullbackComp f g).app ((Scheme.Modules.pullback h).obj N)
  let c : C ≅ D := (pullbackComp (f ≫ g) h).app N
  let d : A ⟶ E := (pullbackComp f (g ≫ h)).hom.app N
  let e : E ⟶ D := eqToHom (by dsimp only [E, D]; rw [Category.assoc])
  have h1 : a ≫ b.hom ≫ c.hom = d ≫ e := assoc_app f g h N
  have h2 : (a ≫ b.hom) ≫ c.hom = d ≫ e :=
    (Category.assoc a b.hom c.hom).trans h1
  have h3 : a ≫ b.hom = (d ≫ e) ≫ c.inv := (Iso.eq_comp_inv c).2 h2
  have h4 : a = ((d ≫ e) ≫ c.inv) ≫ b.inv := (Iso.eq_comp_inv b).2 h3
  exact h4.trans ((Category.assoc (d ≫ e) c.inv b.inv).trans
    (Category.assoc d e (c.inv ≫ b.inv)))

lemma comp_congr_right (f : T' ⟶ T) {g g' : T ⟶ A'} (H : g = g') (N : A'.Modules) :
    (pullbackComp f g).inv.app N ≫ eqToHom (by rw [H]) ≫ (pullbackComp f g').hom.app N =
      eqToHom (by rw [H]) := by
  subst H
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    (pullbackComp f g).inv_hom_id_app N

lemma comp_congr_left {f f' : T' ⟶ T} (H : f = f') (g : T ⟶ A') (N : A'.Modules) :
    (pullbackComp f g).inv.app N ≫
        eqToHom (show (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N) =
          (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj N) by rw [H]) =
      eqToHom (by rw [H]) ≫ (pullbackComp f' g).inv.app N := by
  subst H
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

lemma congr_unit {f f' : T' ⟶ T} (H : f = f') :
    (pullbackCongr H).hom.app (SheafOfModules.unit T.ringCatSheaf) ≫ (pullbackUnitIso f').hom =
      (pullbackUnitIso f).hom := by
  subst H
  exact Category.id_comp (pullbackUnitIso f).hom

lemma congr_nat {f f' : T' ⟶ T} (H : f = f') {M N : T.Modules} (φ : M ⟶ N) :
    (pullbackCongr H).hom.app M ≫ (Scheme.Modules.pullback f').map φ =
      (Scheme.Modules.pullback f).map φ ≫ (pullbackCongr H).hom.app N := by
  subst H
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.comp_id]

end coh

end PV1TL

namespace PV1TL

open _root_.AlgebraicGeometry.Scheme.Modules
open SchemeModulesCechTrivIsUnit.AlgebraicGeometry.Scheme.Modules


section conj
variable {X Z : Scheme.{u}} (φ : X ⟶ Z)

/-- Regard a structure sheaf section as a section of the unit module. -/
def toU (U : Z.Opens) (g : Z.presheaf.obj (op U)) :
    Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), U) := g

theorem pullbackUnitIso_hom_app_pls (U : Z.Opens) (g : Z.presheaf.obj (op U)) :
    (pullbackUnitIso φ).hom.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ (toU U g)) =
      toU (φ ⁻¹ᵁ U) ((φ.app U).hom g) := by
  have h1 : (pullbackUnitIso φ).hom =
      ((pullbackPushforwardAdjunction φ).homEquiv _ _).symm
        (SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom) := rfl
  rw [h1]
  exact Scheme.Modules.homEquiv_symm_app_pullbackLocalSection φ
    (SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom) (toU U g)

theorem pullbackUnitIso_inv_app_one (U : Z.Opens) :
    (pullbackUnitIso φ).inv.app (φ ⁻¹ᵁ U) (toU (φ ⁻¹ᵁ U) 1) = pullbackLocalSection φ (toU U 1) := by
  have h := pullbackUnitIso_hom_app_pls φ U 1
  rw [map_one] at h
  erw [← h, ← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    Iso.hom_inv_id, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

end conj

variable {Y : Scheme.{u}}

/-- The structure sheaf section determined by an automorphism of the unit module. -/
noncomputable def uASm (W : Y.Opens)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) : Γ(Y, W) :=
  unitAutSection W E

section uasMod
variable (W : Y.Opens)
  (E E' : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
    (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf))

theorem uASm_trans : uASm W (E ≪≫ E') = uASm W E * uASm W E' := unitAutSection_trans W E E'

theorem isUnit_uASm : IsUnit (uASm W E) := isUnit_unitAutSection W E

theorem uASm_eq : uASm W E = W.topIso.hom.hom (uapp W E 1) := rfl

end uasMod

lemma presheaf_map_op_apply_eq {U V : Y.Opens} (f g : U ⟶ V) (x : Y.presheaf.obj (op V)) :
    (Y.presheaf.map f.op).hom x = (Y.presheaf.map g.op).hom x := by
  rw [Subsingleton.elim f g]

lemma presheaf_comp_apply_eq {U V V' W : Y.Opens} (f : V ⟶ U) (g : W ⟶ V) (f' : V' ⟶ U) (g' : W ⟶
  V')
    (x : Y.presheaf.obj (op U)) :
    (Y.presheaf.map f.op ≫ Y.presheaf.map g.op).hom x = (Y.presheaf.map f'.op ≫ Y.presheaf.map
      g'.op).hom x := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, Subsingleton.elim (g ≫ f) (g'
    ≫ f')]

theorem unitAutSection_conj {W W' : Y.Opens} (h' : W' ≤ W)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    uASm W' ((pullbackUnitIso (Y.homOfLE h')).symm ≪≫
        (Scheme.Modules.pullback (Y.homOfLE h')).mapIso E ≪≫ pullbackUnitIso (Y.homOfLE h')) =
      (Y.presheaf.map (homOfLE h').op).hom (uASm W E) := by
  have step : uapp W' (show @Iso ((W' : Scheme.{u}).Modules) _ _ _ from
      (pullbackUnitIso (Y.homOfLE h')).symm ≪≫
      (Scheme.Modules.pullback (Y.homOfLE h')).mapIso E ≪≫ pullbackUnitIso (Y.homOfLE h')) 1 =
      ((Y.homOfLE h').appTop).hom (uapp W E 1) :=
    (open _root_.AlgebraicGeometry.Scheme.Modules in
      pullbackUnitIso_conj_app_top_one_eq_appTop (Y.homOfLE h') E)
  rw [uASm_eq, uASm_eq, step]
  simp only [Scheme.Hom.appTop, Scheme.homOfLE_app, Scheme.Opens.topIso_hom]
  exact presheaf_comp_apply_eq _ _ _ _ _

end PV1TL

namespace PV1TL

open _root_.AlgebraicGeometry.Scheme.Modules
open SchemeModulesCechTrivIsUnit.AlgebraicGeometry.Scheme.Modules


section G
variable {Y V B : Scheme.{u}} (𝓜 : Y.Modules)

/-- Restrict a trivialisation along a factorisation of the scheme morphism. -/
noncomputable def genRestrict (ι : V ⟶ Y) (j : B ⟶ Y) (k : B ⟶ V) (e : k ≫ ι = j)
    (τ : (Scheme.Modules.pullback ι).obj 𝓜 ≅ (SheafOfModules.unit V.ringCatSheaf : V.Modules)) :
    (Scheme.Modules.pullback j).obj 𝓜 ≅ (SheafOfModules.unit B.ringCatSheaf : B.Modules) :=
  ((pullbackCongr e).app 𝓜).symm ≪≫ ((pullbackComp k ι).app 𝓜).symm ≪≫
    (Scheme.Modules.pullback k).mapIso τ ≪≫ pullbackUnitIso k

private theorem restrictIso_comp
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂) (α : F ⋙ G ≅ H)
    {M I : C₀} {B₀ B₁ J : C₁} {A₀ A₁ U : C₂}
    (a₀ : A₀ ≅ A₁) (a₁ : A₁ ≅ H.obj M) (c : A₀ ≅ G.obj B₀)
    (b₀ : B₀ ≅ B₁) (b₁ : B₁ ≅ F.obj M) (τ : M ≅ I)
    (ε : F.obj I ≅ J) (δ : G.obj J ≅ U) (η : H.obj I ≅ U)
    (hc : c.hom ≫ G.map b₀.hom ≫ G.map b₁.hom =
      a₀.hom ≫ a₁.hom ≫ α.inv.app M)
    (hu : α.hom.app I ≫ η.hom = G.map ε.hom ≫ δ.hom) :
    a₀ ≪≫ a₁ ≪≫ H.mapIso τ ≪≫ η =
      c ≪≫ G.mapIso (b₀ ≪≫ b₁ ≪≫ F.mapIso τ ≪≫ ε) ≪≫ δ := by
  have hn : α.inv.app M ≫ G.map (F.map τ.hom) =
      H.map τ.hom ≫ α.inv.app I := (α.inv.naturality τ.hom).symm
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc, reassoc_of% hn, ← hu, Iso.inv_hom_id_app_assoc]

theorem genRestrict_comp (ι : V ⟶ Y) (j : B ⟶ Y) (k : B ⟶ V) (e : k ≫ ι = j)
    (τ : (Scheme.Modules.pullback ι).obj 𝓜 ≅ (SheafOfModules.unit V.ringCatSheaf : V.Modules))
    {B' : Scheme.{u}} (q : B' ⟶ B) (j' : B' ⟶ Y) (e' : q ≫ j = j') (k' : B' ⟶ V) (Hk : q ≫ k = k')
    (e'' : k' ≫ ι = j') :
    genRestrict 𝓜 ι j' k' e'' τ =
      ((pullbackComp q j).app 𝓜 ≪≫ (pullbackCongr e').app 𝓜).symm ≪≫
        (Scheme.Modules.pullback q).mapIso (genRestrict 𝓜 ι j k e τ) ≪≫ pullbackUnitIso q := by
  subst e e' Hk
  have hc : (pullbackComp q (k ≫ ι)).inv.app 𝓜 ≫
      (Scheme.Modules.pullback q).map ((pullbackComp k ι).inv.app 𝓜) =
      (pullbackCongr e'').inv.app 𝓜 ≫
        (pullbackComp (q ≫ k) ι).inv.app 𝓜 ≫
          (pullbackComp q k).inv.app ((Scheme.Modules.pullback ι).obj 𝓜) := by
    rw [assoc_app'' q k ι 𝓜]
    simp only [Iso.inv_hom_id_app_assoc, pullbackCongr_inv_app_eq]
  exact restrictIso_comp (Scheme.Modules.pullback k) (Scheme.Modules.pullback q)
    (Scheme.Modules.pullback (q ≫ k)) (pullbackComp q k)
    ((pullbackCongr e'').app 𝓜).symm ((pullbackComp (q ≫ k) ι).app 𝓜).symm
    (((pullbackComp q (k ≫ ι)).app 𝓜) ≪≫
      (pullbackCongr (rfl : q ≫ (k ≫ ι) = q ≫ (k ≫ ι))).app 𝓜).symm
    ((pullbackCongr (rfl : k ≫ ι = k ≫ ι)).app 𝓜).symm
    ((pullbackComp k ι).app 𝓜).symm τ
    (pullbackUnitIso k) (pullbackUnitIso q) (pullbackUnitIso (q ≫ k))
    (by
      dsimp only [Iso.trans, Iso.symm, Iso.app]
      simpa only [pullbackCongr_inv_app_eq, eqToHom_refl,
        (Scheme.Modules.pullback q).map_id, Category.id_comp] using hc)
    (Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom q k)

end G

end PV1TL

namespace PV1TL

open _root_.AlgebraicGeometry.Scheme.Modules
open SchemeModulesCechTrivIsUnit.AlgebraicGeometry.Scheme.Modules


section isoAlgebra
variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

lemma conj_symm_trans_conj {M : C} {N U : D} {I : C} (κ : F.obj M ≅ N) (ε : F.obj I ≅ U) (Ra Rb :
  M ≅ I) :
    (κ.symm ≪≫ F.mapIso Ra ≪≫ ε).symm ≪≫ (κ.symm ≪≫ F.mapIso Rb ≪≫ ε) =
      ε.symm ≪≫ F.mapIso (Ra.symm ≪≫ Rb) ≪≫ ε := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv,
    Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]

lemma symm_trans_trans_symm_trans {M I : C} (Ra Rb Rc : M ≅ I) :
    (Ra.symm ≪≫ Rb) ≪≫ (Rb.symm ≪≫ Rc) = Ra.symm ≪≫ Rc := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

end isoAlgebra

variable {Y : Scheme.{u}}

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules} (τ : CechTrivialisation 𝒱 𝓜)

theorem restrict_eq_genRestrict {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) :
    τ.restrict h = genRestrict 𝓜 (𝒱.U a).ι W.ι (Y.homOfLE h) (Y.homOfLE_ι h) (τ a) := rfl

/-- The canonical comparison between successive pullbacks along open inclusions. -/
noncomputable def κiso (𝓜 : Y.Modules) {W W' : Y.Opens} (h' : W' ≤ W) :
    (Scheme.Modules.pullback (Y.homOfLE h')).obj ((Scheme.Modules.pullback W.ι).obj 𝓜) ≅
      (Scheme.Modules.pullback W'.ι).obj 𝓜 :=
  (pullbackComp (Y.homOfLE h') W.ι).app 𝓜 ≪≫ (pullbackCongr (Y.homOfLE_ι h')).app 𝓜

theorem restrict_trans {a : 𝒱.ι} {W W' : Y.Opens} (h : W ≤ 𝒱.U a) (h' : W' ≤ W) :
    τ.restrict (h'.trans h) =
      (κiso 𝓜 h').symm ≪≫
        (Scheme.Modules.pullback (Y.homOfLE h')).mapIso (τ.restrict h) ≪≫ pullbackUnitIso
          (Y.homOfLE h') := by
  rw [restrict_eq_genRestrict, restrict_eq_genRestrict]
  exact genRestrict_comp 𝓜 (𝒱.U a).ι W.ι (Y.homOfLE h) (Y.homOfLE_ι h) (τ a) (Y.homOfLE h') W'.ι
    (Y.homOfLE_ι h') (Y.homOfLE (h'.trans h)) (Scheme.homOfLE_homOfLE Y h' h) (Y.homOfLE_ι
      (h'.trans h))

/-- The transition section comparing two trivialisations on a common open subscheme. -/
noncomputable def θ (W : Y.Opens) (a b : 𝒱.ι) (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) : Γ(Y, W) :=
  uASm W ((τ.restrict ha).symm ≪≫ τ.restrict hb)

theorem transition_eq_θ (s : 𝒱.Idx 1) :
    τ.transition s = θ τ (𝒱.inter s) (s.1 0) (s.1 1) (𝒱.inter_le s 0) (𝒱.inter_le s 1) := rfl

theorem θ_res {W W' : Y.Opens} (h' : W' ≤ W) (a b : 𝒱.ι) (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    (Y.presheaf.map (homOfLE h').op).hom (θ τ W a b ha hb) = θ τ W' a b (h'.trans ha) (h'.trans
      hb) := by
  rw [θ, θ, restrict_trans τ ha h', restrict_trans τ hb h']
  exact (congrArg (uASm W')
    (conj_symm_trans_conj (Scheme.Modules.pullback (Y.homOfLE h'))
      (κiso 𝓜 h') (pullbackUnitIso (Y.homOfLE h'))
      (τ.restrict ha) (τ.restrict hb))).trans
        (unitAutSection_conj h' ((τ.restrict ha).symm ≪≫ τ.restrict hb)) |>.symm

theorem θ_mul (W : Y.Opens) (a b c : 𝒱.ι) (ha : W ≤ 𝒱.U a) (hb hb' : W ≤ 𝒱.U b) (hc : W ≤ 𝒱.U c) :
    θ τ W a b ha hb * θ τ W b c hb' hc = θ τ W a c ha hc := by
  rw [θ, θ, θ, show τ.restrict hb' = τ.restrict hb from rfl, ← uASm_trans]
  exact congrArg (uASm W)
    (symm_trans_trans_symm_trans (τ.restrict ha) (τ.restrict hb) (τ.restrict hc))

theorem isUnit_transition (s : 𝒱.Idx 1) : IsUnit (τ.transition s) := by
  rw [transition_eq_θ]; exact isUnit_uASm _ _

theorem cocycle (r : 𝒱.Idx 2) :
    (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 2)).op).hom (τ.transition (𝒱.face r 2)) *
        (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 0)).op).hom (τ.transition (𝒱.face r 0)) =
      (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 1)).op).hom (τ.transition (𝒱.face r 1))
        := by
  rw [transition_eq_θ, transition_eq_θ, transition_eq_θ, θ_res, θ_res, θ_res]
  exact θ_mul τ (𝒱.inter r) (r.1 0) (r.1 1) (r.1 2) _ _ _ _

end PV1TL

end AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivIsUnit

section PublicStatement

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace
universe u
open _root_.AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivIsUnit

namespace AlgebraicGeometry.Scheme.Modules.CechTrivialisation

theorem isUnit_transition_and_transition_face_mul_eq
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover) (𝓜 : Y.Modules)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) :
    (∀ s : 𝒱.Idx 1, IsUnit (τ.transition s)) ∧
    ∀ r : 𝒱.Idx 2,
      (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 2)).op).hom (τ.transition (𝒱.face r 2)) *
          (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 0)).op).hom (τ.transition (𝒱.face r
            0)) =
        (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 1)).op).hom (τ.transition (𝒱.face r 1)) :=
  ⟨PV1TL.isUnit_transition τ, PV1TL.cocycle τ⟩

end AlgebraicGeometry.Scheme.Modules.CechTrivialisation

end PublicStatement
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
