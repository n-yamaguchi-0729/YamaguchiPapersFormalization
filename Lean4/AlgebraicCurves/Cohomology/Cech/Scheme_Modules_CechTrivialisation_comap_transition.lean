/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_comap_transition.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Iso
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Picard.CechObstruction
import SchemeTheory.Modules.PullbackLocalSection
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom

/-!
# Scheme Modules Cech Trivialisation comap transition
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivComap


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace


universe u

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Hom.resLE_comp_ι morphismRestrict_ι
  Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme
  Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.resLE_map Scheme.Hom.appTop
  Scheme.Modules Scheme.Hom.resLE_app_top IsAffineHom Scheme.Modules.CechTrivialisation
  Scheme.Modules.homEquiv_symm_app_pullbackLocalSection
  Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Hom.resLE_comp_ι ringCatSheaf Modules.pullback
  Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom topIso Modules.Hom.id_app
  Modules.Hom.app Hom.resLE_map Hom.appTop Hom.comp_app Modules Opens homOfLE_ι
  Hom.resLE_app_top restrict PresheafOfModules OrderedAffineCover Modules.CechTrivialisation
  Modules.homEquiv_symm_app_pullbackLocalSection
  Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (pullback presheaf Hom.comp_app Hom
  pseudofunctor_associativity Hom.id_app Hom.app pullbackCongr pullbackPushforwardAdjunction
  restrict map_smul pullbackComp pullbackUnitIso unitAutSection CechTrivialisation
  CechTrivialisation.comap pullbackLocalSection pullbackLocalSection_app
  homEquiv_symm_app_pullbackLocalSection pullbackComp_hom_app_comp_pullbackUnitIso_hom)


open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry


variable {Y : Scheme.{u}}

/-- Evaluate a unit-module automorphism on a section over the whole restricted scheme. -/
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
  ((e.hom.val.app (op ⊤)).hom).map_smul (show ((W : Scheme.{u}).ringCatSheaf.obj.obj (op ⊤))
    from x) y

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
  rw [unitAutSection_eq, unitAutSection_eq, unitAutSection_eq, ← map_mul, uapp_trans, ←
    uapp_mul, mul_one]

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
open SchemeModulesCechTrivComap.AlgebraicGeometry.Scheme.Modules


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
    Category.id_comp, eqToHom_app] at this
  exact (Iso.inv_comp_eq ((pullbackComp f (g ≫ h)).app N)).1 this

lemma assoc_app'' {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app N) =
      (pullbackComp f (g ≫ h)).hom.app N ≫ eqToHom
        (by rw [Category.assoc]) ≫ (pullbackComp (f ≫ g) h).inv.app N ≫
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

lemma assoc_app' {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj N) ≫
      (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app N) =
    (pullbackComp (f ≫ g) h).hom.app N ≫ eqToHom
      (by rw [Category.assoc]) ≫ (pullbackComp f (g ≫ h)).inv.app N := by
  have h1 := assoc_app f g h N
  let α : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj
    ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) :=
    (Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app N)
  let β : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj
    ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) :=
    (pullbackComp f g).app ((Scheme.Modules.pullback h).obj N)
  let γ : (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) ≅
      (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N := (pullbackComp (f ≫ g) h).app N
  let δ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) ≅
      (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N := (pullbackComp f (g ≫ h)).app N
  let η : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N ≅ (Scheme.Modules.pullback ((f ≫ g) ≫
    h)).obj N :=
    eqToIso (by rw [Category.assoc])
  have h2 : α.symm ≪≫ β ≪≫ γ = δ ≪≫ η := Iso.ext h1
  change β.inv ≫ α.hom = γ.hom ≫ η.inv ≫ δ.inv
  have h3 := congrArg (fun E => γ.hom ≫ E.inv) h2
  simpa only [Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc] using h3

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
open SchemeModulesCechTrivComap.AlgebraicGeometry.Scheme.Modules


section G
variable {Y V B : Scheme.{u}} (𝓜 : Y.Modules)

/-- Restrict a local module trivialisation along a factorisation of its open immersion. -/
noncomputable def genRestrict (ι : V ⟶ Y) (j : B ⟶ Y) (k : B ⟶ V) (e : k ≫ ι = j)
    (τ : (Scheme.Modules.pullback ι).obj 𝓜 ≅ SheafOfModules.unit V.ringCatSheaf) :
    (Scheme.Modules.pullback j).obj 𝓜 ≅ SheafOfModules.unit B.ringCatSheaf :=
  ((pullbackCongr e).app 𝓜).symm ≪≫ ((pullbackComp k ι).app 𝓜).symm ≪≫
    (Scheme.Modules.pullback k).mapIso τ ≪≫ pullbackUnitIso k

theorem genRestrict_comp (ι : V ⟶ Y) (j : B ⟶ Y) (k : B ⟶ V) (e : k ≫ ι = j)
    (τ : (Scheme.Modules.pullback ι).obj 𝓜 ≅ SheafOfModules.unit V.ringCatSheaf)
    {B' : Scheme.{u}} (q : B' ⟶ B) (j' : B' ⟶ Y) (e' : q ≫ j = j') (k' : B' ⟶ V) (Hk : q ≫ k = k')
    (e'' : k' ≫ ι = j') :
    genRestrict 𝓜 ι j' k' e'' τ =
      ((pullbackComp q j).app 𝓜 ≪≫ (pullbackCongr e').app 𝓜).symm ≪≫
        (Scheme.Modules.pullback q).mapIso (genRestrict 𝓜 ι j k e τ) ≪≫ pullbackUnitIso q := by
  subst e e' Hk
  let U : V.Modules := SheafOfModules.unit V.ringCatSheaf
  let UB : B.Modules := SheafOfModules.unit B.ringCatSheaf
  let UB' : B'.Modules := SheafOfModules.unit B'.ringCatSheaf
  let t : (Scheme.Modules.pullback ι).obj 𝓜 ⟶ U := τ.hom
  let ε : (Scheme.Modules.pullback k).obj U ≅ UB := pullbackUnitIso k
  let ε' : (Scheme.Modules.pullback q).obj UB ≅ UB' := pullbackUnitIso q
  let ε'' : (Scheme.Modules.pullback (q ≫ k)).obj U ≅ UB' := pullbackUnitIso (q ≫ k)
  have natinv := (pullbackComp q k).inv.naturality t
  simp only [Functor.comp_map] at natinv
  have u : (pullbackComp q k).hom.app U ≫ ε''.hom =
      (Scheme.Modules.pullback q).map ε.hom ≫ ε'.hom :=
    Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom q k
  apply Iso.ext
  change (pullbackComp (q ≫ k) ι).inv.app 𝓜 ≫
      (Scheme.Modules.pullback (q ≫ k)).map t ≫ ε''.hom =
    (pullbackComp q (k ≫ ι)).inv.app 𝓜 ≫
      (Scheme.Modules.pullback q).map
        ((pullbackComp k ι).inv.app 𝓜 ≫ (Scheme.Modules.pullback k).map t ≫ ε.hom) ≫ ε'.hom
  simp only [Functor.map_comp, Category.assoc]
  erw [assoc_app'' q k ι 𝓜]
  simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [← reassoc_of% natinv]
  erw [← u]
  erw [Iso.inv_hom_id_app_assoc]
  rfl

end G

end PV1TL

namespace PV1TL

open _root_.AlgebraicGeometry.Scheme.Modules
open SchemeModulesCechTrivComap.AlgebraicGeometry.Scheme.Modules


section isoAlgebra2
variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

lemma pre_symm_trans_pre {M : C} {N U : D} {I : C} (P : N ≅ F.obj M) (ε : F.obj I ≅ U) (Ra Rb :
  M ≅ I) :
    (P ≪≫ F.mapIso Ra ≪≫ ε).symm ≪≫ (P ≪≫ F.mapIso Rb ≪≫ ε) =
      ε.symm ≪≫ F.mapIso (Ra.symm ≪≫ Rb) ≪≫ ε := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]

end isoAlgebra2

section GG
variable {Y Y' V B B' : Scheme.{u}} (𝓜 : Y.Modules)


theorem genRestrict_pullback (h : Y' ⟶ Y) (ι : V ⟶ Y) (j₁ : B ⟶ Y') (k : B ⟶ V) (e : k ≫ ι = j₁ ≫ h)
    (τ : (Scheme.Modules.pullback ι).obj 𝓜 ≅ SheafOfModules.unit V.ringCatSheaf)
    (k₂ : B' ⟶ B) (j₂ : B' ⟶ Y') (e₂ : k₂ ≫ j₁ = j₂) (e₃ : (k₂ ≫ k) ≫ ι = j₂ ≫ h) :
    genRestrict ((Scheme.Modules.pullback h).obj 𝓜) j₁ j₂ k₂ e₂
        ((pullbackComp j₁ h).app 𝓜 ≪≫ genRestrict 𝓜 ι (j₁ ≫ h) k e τ) =
      (pullbackComp j₂ h).app 𝓜 ≪≫ genRestrict 𝓜 ι (j₂ ≫ h) (k₂ ≫ k) e₃ τ := by
  subst e₂
  have key := genRestrict_comp 𝓜 ι (j₁ ≫ h) k e τ k₂ ((k₂ ≫ j₁) ≫ h)
    (by rw [Category.assoc]) (k₂ ≫ k) rfl e₃
  rw [key]
  let U : B.Modules := SheafOfModules.unit B.ringCatSheaf
  let U' : B'.Modules := SheafOfModules.unit B'.ringCatSheaf
  let F := Scheme.Modules.pullback k₂
  let t : (Scheme.Modules.pullback (j₁ ≫ h)).obj 𝓜 ≅ U :=
    genRestrict 𝓜 ι (j₁ ≫ h) k e τ
  let ε : F.obj U ≅ U' := pullbackUnitIso k₂
  let β := (pullbackComp k₂ j₁).app ((Scheme.Modules.pullback h).obj 𝓜)
  let γ := (pullbackComp (k₂ ≫ j₁) h).app 𝓜
  let δ := (pullbackComp k₂ (j₁ ≫ h)).app 𝓜
  let a := (pullbackComp j₁ h).hom.app 𝓜
  let c : (Scheme.Modules.pullback ((k₂ ≫ j₁) ≫ h)).obj 𝓜 ⟶
      (Scheme.Modules.pullback (k₂ ≫ j₁ ≫ h)).obj 𝓜 := eqToHom (by rw [Category.assoc])
  have A : β.inv ≫ F.map a = γ.hom ≫ c ≫ δ.inv := assoc_app' k₂ j₁ h 𝓜
  apply Iso.ext
  change β.inv ≫ F.map (a ≫ t.hom) ≫ ε.hom =
    γ.hom ≫ (pullbackCongr (by rw [Category.assoc])).inv.app 𝓜 ≫
      δ.inv ≫ F.map t.hom ≫ ε.hom
  rw [pullbackCongr_inv_app_eq]
  change β.inv ≫ F.map (a ≫ t.hom) ≫ ε.hom =
    γ.hom ≫ c ≫ δ.inv ≫ F.map t.hom ≫ ε.hom
  have hpost := congrArg
    (fun z : (Scheme.Modules.pullback (k₂ ≫ j₁)).obj ((Scheme.Modules.pullback h).obj 𝓜) ⟶
        F.obj ((Scheme.Modules.pullback (j₁ ≫ h)).obj 𝓜) => z ≫ F.map t.hom ≫ ε.hom) A
  rw [F.map_comp]
  simpa only [Category.assoc] using hpost

end GG

end PV1TL

namespace PV1TL

open _root_.AlgebraicGeometry.Scheme.Modules
open SchemeModulesCechTrivComap.AlgebraicGeometry.Scheme.Modules


section conjGeneral
variable {X Z : Scheme.{u}} (φ : X ⟶ Z)

/-- View a regular function as a section of the unit module. -/
def toU (U : Z.Opens) (g : Z.presheaf.obj (op U)) :
    Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), U) := g

theorem pullbackUnitIso_hom_app_pls (U : Z.Opens) (g : Z.presheaf.obj (op U)) :
    (pullbackUnitIso φ).hom.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ (toU U g)) =
      toU (φ ⁻¹ᵁ U) ((φ.app U).hom g) := by
  let L : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let N : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let k : L ⟶ (Scheme.Modules.pushforward φ).obj N :=
    SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom
  exact Scheme.Modules.homEquiv_symm_app_pullbackLocalSection φ k (toU U g)

theorem pullbackUnitIso_inv_app_one (U : Z.Opens) :
    (pullbackUnitIso φ).inv.app (φ ⁻¹ᵁ U) (toU (φ ⁻¹ᵁ U) 1) = pullbackLocalSection φ (toU U 1) := by
  have h := pullbackUnitIso_hom_app_pls φ U 1
  rw [map_one] at h
  let L : X.Modules := (Scheme.Modules.pullback φ).obj (SheafOfModules.unit Z.ringCatSheaf)
  let N : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let e : L ≅ N := pullbackUnitIso φ
  let s : Γ(L, φ ⁻¹ᵁ U) := pullbackLocalSection φ (toU U 1)
  have h' : e.hom.app (φ ⁻¹ᵁ U) s = toU (φ ⁻¹ᵁ U) 1 := h
  have he : e.inv.app (φ ⁻¹ᵁ U) (e.hom.app (φ ⁻¹ᵁ U) s) = s :=
    congrArg (fun k : L ⟶ L => k.app (φ ⁻¹ᵁ U) s) e.hom_inv_id
  exact (congrArg (fun z : Γ(N, φ ⁻¹ᵁ U) => e.inv.app (φ ⁻¹ᵁ U) z) h').symm.trans he

end conjGeneral

variable {Y : Scheme.{u}}

/-- The function determined by a unit-module automorphism on an open subscheme. -/
noncomputable def uASm (W : Y.Opens)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) : Γ(Y, W) :=
  unitAutSection W E

theorem uASm_eq (W : Y.Opens)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    uASm W E = W.topIso.hom.hom (uapp W E 1) := rfl

theorem uASm_conj_general {Y' : Scheme.{u}} {W : Y.Opens} {W'' : Y'.Opens}
    (q : (W'' : Scheme.{u}) ⟶ (W : Scheme.{u}))
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    uASm W'' ((pullbackUnitIso q).symm ≪≫ (Scheme.Modules.pullback q).mapIso E ≪≫
      pullbackUnitIso q) =
      W''.topIso.hom.hom (q.appTop.hom (uapp W E 1)) := by
  have step : uapp W'' (show @Iso ((W'' : Scheme.{u}).Modules) _ _ _ from
      (pullbackUnitIso q).symm ≪≫ (Scheme.Modules.pullback q).mapIso E ≪≫ pullbackUnitIso q) 1 =
      (q.appTop).hom (uapp W E 1) := by
    let L : (W : Scheme.{u}).Modules := SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf
    let N : (W'' : Scheme.{u}).Modules := SheafOfModules.unit (W'' : Scheme.{u}).ringCatSheaf
    let F := Scheme.Modules.pullback q
    let P : (W'' : Scheme.{u}).Modules := F.obj L
    let e : P ≅ N := pullbackUnitIso q
    let E' : L ≅ L := E
    let V : (W'' : Scheme.{u}).Opens := q ⁻¹ᵁ ⊤
    let one : Γ(N, V) := toU V 1
    let s : Γ(P, V) := pullbackLocalSection q (toU ⊤ 1)
    let t : Γ(L, ⊤) := E'.hom.app ⊤ (toU ⊤ 1)
    have hi : e.inv.app V one = s := pullbackUnitIso_inv_app_one q ⊤
    have hm : (F.map E'.hom).app V s = pullbackLocalSection q t :=
      (pullbackLocalSection_app q E'.hom (toU ⊤ 1)).symm
    have hh : e.hom.app V (pullbackLocalSection q t) = toU V ((q.app ⊤).hom t) :=
      pullbackUnitIso_hom_app_pls q ⊤ t
    have hc : e.hom.app V ((F.map E'.hom).app V (e.inv.app V one)) =
        toU V ((q.app ⊤).hom t) :=
      (congrArg (fun z : Γ(P, V) => e.hom.app V ((F.map E'.hom).app V z)) hi).trans
        ((congrArg (fun z : Γ(P, V) => e.hom.app V z) hm).trans hh)
    exact hc
  rw [uASm_eq, step]

theorem uASm_conj_resLE {Y' : Scheme.{u}} (h : Y' ⟶ Y) {W : Y.Opens} {W'' : Y'.Opens} (c : W'' ≤
  h ⁻¹ᵁ W)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    uASm W'' ((pullbackUnitIso (h.resLE W W'' c)).symm ≪≫
        (Scheme.Modules.pullback (h.resLE W W'' c)).mapIso E ≪≫ pullbackUnitIso (h.resLE W W'' c)) =
      (Y'.presheaf.map (homOfLE c).op).hom ((h.app W).hom (uASm W E)) := by
  rw [uASm_conj_general, uASm_eq, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [CategoryTheory.comp_apply, CategoryTheory.Iso.inv_hom_id_apply]
  rfl

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules} (τ : CechTrivialisation 𝒱 𝓜)

theorem restrict_eq_genRestrict {a : 𝒱.ι} {W : Y.Opens} (hx : W ≤ 𝒱.U a) :
    τ.restrict hx = genRestrict 𝓜 (𝒱.U a).ι W.ι (Y.homOfLE hx) (Y.homOfLE_ι hx) (τ a) := rfl

variable {Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h]

theorem comap_apply_eq (a : 𝒱.ι) :
    τ.comap h a = (pullbackComp (h ⁻¹ᵁ 𝒱.U a).ι h).app 𝓜 ≪≫
      genRestrict 𝓜 (𝒱.U a).ι ((h ⁻¹ᵁ 𝒱.U a).ι ≫ h) (h ∣_ 𝒱.U a) (morphismRestrict_ι h (𝒱.U a))
        (τ a) := by
  rfl

theorem comap_restrict_eq_genRestrict (a : 𝒱.ι) {W'' : Y'.Opens} (hx' : W'' ≤ (𝒱.comap h).U a) :
    (τ.comap h).restrict hx' =
      genRestrict ((Scheme.Modules.pullback h).obj 𝓜) (h ⁻¹ᵁ 𝒱.U a).ι W''.ι (Y'.homOfLE hx')
        (Y'.homOfLE_ι hx')
        (τ.comap h a) := rfl

/-- Compare restriction of a pullback module with pullback of its restriction along resLE. -/
noncomputable def Piso (𝓜 : Y.Modules) {W : Y.Opens} {W'' : Y'.Opens} (c : W'' ≤ h ⁻¹ᵁ W) :
    (Scheme.Modules.pullback W''.ι).obj ((Scheme.Modules.pullback h).obj 𝓜) ≅
      (Scheme.Modules.pullback (h.resLE W W'' c)).obj ((Scheme.Modules.pullback W.ι).obj 𝓜) :=
  (pullbackComp W''.ι h).app 𝓜 ≪≫
    ((pullbackComp (h.resLE W W'' c) W.ι).app 𝓜 ≪≫ (pullbackCongr (Scheme.Hom.resLE_comp_ι h
      c)).app 𝓜).symm

theorem comap_restrict (a : 𝒱.ι) {W : Y.Opens} (hx : W ≤ 𝒱.U a) {W'' : Y'.Opens} (c : W'' ≤ h ⁻¹ᵁ W)
    (hx' : W'' ≤ (𝒱.comap h).U a) :
    (τ.comap h).restrict hx' =
      Piso h 𝓜 c ≪≫ (Scheme.Modules.pullback (h.resLE W W'' c)).mapIso (τ.restrict hx) ≪≫
        pullbackUnitIso (h.resLE W W'' c) := by
  have e₃ : (Y'.homOfLE hx' ≫ h ∣_ 𝒱.U a) ≫ (𝒱.U a).ι = W''.ι ≫ h := Scheme.Hom.resLE_comp_ι h hx'
  have Hk : h.resLE W W'' c ≫ Y.homOfLE hx = Y'.homOfLE hx' ≫ h ∣_ 𝒱.U a := by
    rw [Scheme.Hom.resLE_map]; rfl
  have step1 : (τ.comap h).restrict hx' =
      genRestrict ((Scheme.Modules.pullback h).obj 𝓜) (h ⁻¹ᵁ 𝒱.U a).ι W''.ι (Y'.homOfLE hx')
        (Y'.homOfLE_ι hx')
        ((pullbackComp (h ⁻¹ᵁ 𝒱.U a).ι h).app 𝓜 ≪≫
          genRestrict 𝓜 (𝒱.U a).ι ((h ⁻¹ᵁ 𝒱.U a).ι ≫ h) (h ∣_ 𝒱.U a) (morphismRestrict_ι h (𝒱.U
            a)) (τ a)) := by
    rw [comap_restrict_eq_genRestrict, comap_apply_eq]
  have step2 := genRestrict_pullback 𝓜 h (𝒱.U a).ι (h ⁻¹ᵁ 𝒱.U a).ι (h ∣_ 𝒱.U a)
    (morphismRestrict_ι h (𝒱.U a)) (τ a)
      (Y'.homOfLE hx') W''.ι (Y'.homOfLE_ι hx') e₃
  have step3 := genRestrict_comp 𝓜 (𝒱.U a).ι W.ι (Y.homOfLE hx) (Y.homOfLE_ι hx) (τ a) (h.resLE
    W W'' c) (W''.ι ≫ h)
      (Scheme.Hom.resLE_comp_ι h c) (Y'.homOfLE hx' ≫ h ∣_ 𝒱.U a) Hk e₃
  rw [step1]
  refine step2.trans ?_
  refine (congrArg (fun e => (pullbackComp W''.ι h).app 𝓜 ≪≫ e) step3).trans ?_
  rw [restrict_eq_genRestrict]
  exact (Iso.trans_assoc _ _ _).symm

theorem comap_transition (s : 𝒱.Idx 1) :
    (τ.comap h).transition s =
      (Y'.presheaf.map (homOfLE (𝒱.comap_inter_le h s)).op).hom ((h.app (𝒱.inter s)).hom
        (τ.transition s)) := by
  have e0 := comap_restrict τ h (s.1 0) (𝒱.inter_le s 0) (𝒱.comap_inter_le h s) ((𝒱.comap
    h).inter_le s 0)
  have e1 := comap_restrict τ h (s.1 1) (𝒱.inter_le s 1) (𝒱.comap_inter_le h s) ((𝒱.comap
    h).inter_le s 1)
  let W : Y.Opens := 𝒱.inter s
  let W' : Y'.Opens := (𝒱.comap h).inter (show (𝒱.comap h).Idx 1 from s)
  let c : W' ≤ h ⁻¹ᵁ W := 𝒱.comap_inter_le h s
  let F := Scheme.Modules.pullback (h.resLE W W' c)
  let U : (W : Scheme.{u}).Modules := SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf
  let U' : (W' : Scheme.{u}).Modules := SheafOfModules.unit (W' : Scheme.{u}).ringCatSheaf
  let M : (W : Scheme.{u}).Modules := (Scheme.Modules.pullback W.ι).obj 𝓜
  let M' : (W' : Scheme.{u}).Modules :=
    (Scheme.Modules.pullback W'.ι).obj ((Scheme.Modules.pullback h).obj 𝓜)
  let Ra : M ≅ U := τ.restrict (𝒱.inter_le s 0)
  let Rb : M ≅ U := τ.restrict (𝒱.inter_le s 1)
  let P : M' ≅ F.obj M := Piso h 𝓜 c
  let ε : F.obj U ≅ U' := pullbackUnitIso (h.resLE W W' c)
  let R'a : M' ≅ U' := (τ.comap h).restrict ((𝒱.comap h).inter_le s 0)
  let R'b : M' ≅ U' := (τ.comap h).restrict ((𝒱.comap h).inter_le s 1)
  have e0' : R'a = P ≪≫ F.mapIso Ra ≪≫ ε := e0
  have e1' : R'b = P ≪≫ F.mapIso Rb ≪≫ ε := e1
  have he : R'a.symm ≪≫ R'b = ε.symm ≪≫ F.mapIso (Ra.symm ≪≫ Rb) ≪≫ ε :=
    (congrArg (fun k : M' ≅ U' => k.symm ≪≫ R'b) e0').trans
      ((congrArg (fun k : M' ≅ U' => (P ≪≫ F.mapIso Ra ≪≫ ε).symm ≪≫ k) e1').trans
        (pre_symm_trans_pre F P ε Ra Rb))
  exact (congrArg (fun k : U' ≅ U' => uASm W' k) he).trans
    (uASm_conj_resLE h c (Ra.symm ≪≫ Rb))

end PV1TL

theorem _root_.AlgebraicGeometry.Scheme.Modules.CechTrivialisation.comap_transition
    {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h] (𝒱 : Y.OrderedAffineCover) (𝓜 : Y.Modules)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) (s : 𝒱.Idx 1) :
    (τ.comap h).transition s =
      (Y'.presheaf.map (homOfLE (𝒱.comap_inter_le h s)).op).hom ((h.app (𝒱.inter s)).hom
        (τ.transition s)) :=
  PV1TL.comap_transition τ h s
end AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivComap
end ProofImplementation

attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
