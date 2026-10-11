/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_nonempty_iso_unit_of_forall_transition_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Tactic.Choose
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.CechObstruction
import Nyll.SchemeTheory.Modules.PullbackLocalSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top

/-!
# Scheme Modules Cech Trivialisation nonempty iso unit of forall transition eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivIsoUnitAll

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace L5G
namespace UA
open AlgebraicGeometry.Scheme.Modules

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

end L5G.UA

open L5G.UA

namespace L5G

section coh


open _root_.AlgebraicGeometry.Scheme.Modules


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
      (pullbackComp f (g ≫ h)).hom.app N ≫ eqToHom
        (by rw [Category.assoc]) ≫ (pullbackComp (f ≫ g) h).inv.app N ≫
        (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj N) := by
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
  have h3 : α.symm = δ ≪≫ η ≪≫ γ.symm ≪≫ β.symm := by
    calc α.symm = (α.symm ≪≫ β ≪≫ γ) ≪≫ (γ.symm ≪≫ β.symm) := by simp
      _ = (δ ≪≫ η) ≪≫ (γ.symm ≪≫ β.symm) := by rw [h2]
      _ = δ ≪≫ η ≪≫ γ.symm ≪≫ β.symm := by simp
  have h4 := congrArg Iso.hom h3
  simpa [α, β, γ, δ, η, eqToIso] using h4

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
  subst H; simp

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

end L5G

namespace L5G

open _root_.AlgebraicGeometry.Scheme.Modules


section conj
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

end conj

variable {Y : Scheme.{u}}

/-- The function determined by a unit-module automorphism on an open subscheme. -/
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

lemma presheaf_comp_apply_eq {U V V' W : Y.Opens} (f : V ⟶ U) (g : W ⟶ V) (f' : V' ⟶ U) (g' : W
  ⟶ V')
    (x : Y.presheaf.obj (op U)) :
    (Y.presheaf.map f.op ≫ Y.presheaf.map g.op).hom x = (Y.presheaf.map f'.op ≫ Y.presheaf.map
      g'.op).hom x := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, Subsingleton.elim (g ≫ f)
    (g' ≫ f')]

theorem unitAutSection_conj {W W' : Y.Opens} (h' : W' ≤ W)
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    uASm W' ((pullbackUnitIso (Y.homOfLE h')).symm ≪≫
        (Scheme.Modules.pullback (Y.homOfLE h')).mapIso E ≪≫ pullbackUnitIso (Y.homOfLE h')) =
      (Y.presheaf.map (homOfLE h').op).hom (uASm W E) := by
  have step : uapp W' (show @Iso ((W' : Scheme.{u}).Modules) _ _ _ from
      (pullbackUnitIso (Y.homOfLE h')).symm ≪≫
      (Scheme.Modules.pullback (Y.homOfLE h')).mapIso E ≪≫ pullbackUnitIso (Y.homOfLE h')) 1 =
      ((Y.homOfLE h').appTop).hom (uapp W E 1) := by
    let q := Y.homOfLE h'
    let L : (W : Scheme.{u}).Modules := SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf
    let N : (W' : Scheme.{u}).Modules := SheafOfModules.unit (W' : Scheme.{u}).ringCatSheaf
    let F := Scheme.Modules.pullback q
    let P : (W' : Scheme.{u}).Modules := F.obj L
    let e : P ≅ N := pullbackUnitIso q
    let E' : L ≅ L := E
    let V : (W' : Scheme.{u}).Opens := q ⁻¹ᵁ ⊤
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
  rw [uASm_eq, uASm_eq, step]
  simp only [Scheme.Hom.appTop, Scheme.homOfLE_app, Scheme.Opens.topIso_hom]
  exact presheaf_comp_apply_eq _ _ _ _ _

end L5G

namespace L5G

open _root_.AlgebraicGeometry.Scheme.Modules


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

end L5G

namespace L5G

open _root_.AlgebraicGeometry.Scheme.Modules


section isoAlgebra
variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

lemma conj_symm_trans_conj {M : C} {N U : D} {I : C} (κ : F.obj M ≅ N) (ε : F.obj I ≅ U) (Ra Rb
  : M ≅ I) :
    (κ.symm ≪≫ F.mapIso Ra ≪≫ ε).symm ≪≫ (κ.symm ≪≫ F.mapIso Rb ≪≫ ε) =
      ε.symm ≪≫ F.mapIso (Ra.symm ≪≫ Rb) ≪≫ ε := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv,
    Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]

lemma symm_trans_trans_symm_trans {M I : C} (Ra Rb Rc : M ≅ I) :
    (Ra.symm ≪≫ Rb) ≪≫ (Rb.symm ≪≫ Rc) = Ra.symm ≪≫ Rc := by
  simp

end isoAlgebra

variable {Y : Scheme.{u}}

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules} (τ : CechTrivialisation 𝒱 𝓜)

theorem restrict_eq_genRestrict {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) :
    τ.restrict h = genRestrict 𝓜 (𝒱.U a).ι W.ι (Y.homOfLE h) (Y.homOfLE_ι h) (τ a) := rfl

/-- Compare iterated pullback along an open inclusion with pullback to the smaller open. -/
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

/-- The function comparing two local trivialisations on a common open subset. -/
noncomputable def θ (W : Y.Opens) (a b : 𝒱.ι) (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) : Γ(Y, W) :=
  uASm W ((τ.restrict ha).symm ≪≫ τ.restrict hb)

theorem transition_eq_θ (s : 𝒱.Idx 1) :
    τ.transition s = θ τ (𝒱.inter s) (s.1 0) (s.1 1) (𝒱.inter_le s 0) (𝒱.inter_le s 1) := rfl

theorem θ_res {W W' : Y.Opens} (h' : W' ≤ W) (a b : 𝒱.ι) (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    (Y.presheaf.map (homOfLE h').op).hom (θ τ W a b ha hb) = θ τ W' a b (h'.trans ha) (h'.trans
      hb) := by
  let U : (W : Scheme.{u}).Modules := SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf
  let U' : (W' : Scheme.{u}).Modules := SheafOfModules.unit (W' : Scheme.{u}).ringCatSheaf
  let M : (W : Scheme.{u}).Modules := (Scheme.Modules.pullback W.ι).obj 𝓜
  let M' : (W' : Scheme.{u}).Modules := (Scheme.Modules.pullback W'.ι).obj 𝓜
  let F := Scheme.Modules.pullback (Y.homOfLE h')
  let κ : F.obj M ≅ M' := κiso 𝓜 h'
  let ε : F.obj U ≅ U' := pullbackUnitIso (Y.homOfLE h')
  let Ra : M ≅ U := τ.restrict ha
  let Rb : M ≅ U := τ.restrict hb
  let R'a : M' ≅ U' := τ.restrict (h'.trans ha)
  let R'b : M' ≅ U' := τ.restrict (h'.trans hb)
  have ha' : R'a = κ.symm ≪≫ F.mapIso Ra ≪≫ ε := restrict_trans τ ha h'
  have hb' : R'b = κ.symm ≪≫ F.mapIso Rb ≪≫ ε := restrict_trans τ hb h'
  have he : R'a.symm ≪≫ R'b = ε.symm ≪≫ F.mapIso (Ra.symm ≪≫ Rb) ≪≫ ε :=
    (congrArg (fun k : M' ≅ U' => k.symm ≪≫ R'b) ha').trans
      ((congrArg (fun k : M' ≅ U' => (κ.symm ≪≫ F.mapIso Ra ≪≫ ε).symm ≪≫ k) hb').trans
        (conj_symm_trans_conj F κ ε Ra Rb))
  exact (unitAutSection_conj h' (Ra.symm ≪≫ Rb)).symm.trans
    (congrArg (fun k : U' ≅ U' => uASm W' k) he.symm)

theorem θ_mul (W : Y.Opens) (a b c : 𝒱.ι) (ha : W ≤ 𝒱.U a) (hb hb' : W ≤ 𝒱.U b) (hc : W ≤ 𝒱.U c) :
    θ τ W a b ha hb * θ τ W b c hb' hc = θ τ W a c ha hc := by
  let U : (W : Scheme.{u}).Modules := SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf
  let M : (W : Scheme.{u}).Modules := (Scheme.Modules.pullback W.ι).obj 𝓜
  let Ra : M ≅ U := τ.restrict ha
  let Rb : M ≅ U := τ.restrict hb
  let Rc : M ≅ U := τ.restrict hc
  exact (uASm_trans W (Ra.symm ≪≫ Rb) (Rb.symm ≪≫ Rc)).symm.trans
    (congrArg (fun k : U ≅ U => uASm W k) (symm_trans_trans_symm_trans Ra Rb Rc))

theorem isUnit_transition (s : 𝒱.Idx 1) : IsUnit (τ.transition s) := by
  rw [transition_eq_θ]; exact isUnit_uASm _ _

theorem cocycle (r : 𝒱.Idx 2) :
    (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 2)).op).hom (τ.transition (𝒱.face r 2)) *
        (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 0)).op).hom (τ.transition (𝒱.face r 0)) =
      (Y.presheaf.map (homOfLE (𝒱.inter_le_inter_face r 1)).op).hom (τ.transition (𝒱.face r 1))
        := by
  rw [transition_eq_θ, transition_eq_θ, transition_eq_θ, θ_res, θ_res, θ_res]
  exact θ_mul τ (𝒱.inter r) (r.1 0) (r.1 1) (r.1 2) _ _ _ _

end L5G

namespace L5G

open _root_.AlgebraicGeometry.Scheme.Modules
open UA


variable {Y : Scheme.{u}}

section localAgree
variable (W : Y.Opens)

theorem eq_refl_of_uASm_eq_one
    (E : @Iso ((W : Scheme.{u}).Modules) _ (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf))
    (h : uASm W E = 1) : E = Iso.refl _ := by
  have h1 : uapp W E 1 = 1 := by
    rw [uASm_eq] at h
    have h2 := congrArg W.topIso.inv.hom h
    rw [map_one, ← CommRingCat.comp_apply, Iso.hom_inv_id] at h2
    exact h2
  apply Iso.ext
  apply (SheafOfModules.unit ((W : Scheme.{u}).ringCatSheaf)).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  let f : (op ⊤ : ((W : Scheme.{u}).Opens)ᵒᵖ) ⟶ V := (homOfLE (le_top (a := V.unop))).op
  have H : ∀ (s t : (SheafOfModules.unit ((W : Scheme.{u}).ringCatSheaf)).sections),
      s.val (op ⊤) = t.val (op ⊤) → s.val V = t.val V := by
    intro s t hst
    rw [← PresheafOfModules.sections_property s f, ← PresheafOfModules.sections_property t f, hst]
  apply H
  exact h1

end localAgree

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules} (τ : CechTrivialisation 𝒱 𝓜)

theorem restrict_congr_idx {a a' : 𝒱.ι} (e : a = a') {W : Y.Opens} (ha : W ≤ 𝒱.U a) (ha' : W ≤
  𝒱.U a') :
    τ.restrict ha = τ.restrict ha' := by
  subst e; rfl

/-- The increasing one-simplex associated to two strictly ordered cover indices. -/
def pair {a b : 𝒱.ι} (hab : a < b) : 𝒱.Idx 1 :=
  ⟨![a, b], Fin.strictMono_iff_lt_succ.2 (fun i => by
    fin_cases i
    simpa using hab)⟩

theorem pair_zero {a b : 𝒱.ι} (hab : a < b) : (pair (𝒱 := 𝒱) hab).1 0 = a := rfl
theorem pair_one {a b : 𝒱.ι} (hab : a < b) : (pair (𝒱 := 𝒱) hab).1 1 = b := rfl

theorem le_inter_pair {a b : 𝒱.ι} (hab : a < b) {W : Y.Opens} (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    W ≤ 𝒱.inter (pair hab) := by
  refine le_iInf fun j => ?_
  fin_cases j
  · exact ha
  · exact hb

theorem restrict_eq_of_lt (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1)
    {a b : 𝒱.ι} (hab : a < b) {W : Y.Opens} (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    τ.restrict ha = τ.restrict hb := by
  have hW := le_inter_pair hab ha hb
  have key := θ_res τ hW ((pair hab).1 0) ((pair hab).1 1) (𝒱.inter_le _ 0) (𝒱.inter_le _ 1)
  rw [← transition_eq_θ, h1, map_one] at key
  have E := eq_refl_of_uASm_eq_one W _ key.symm
  have E' : τ.restrict (hW.trans (𝒱.inter_le (pair hab) 1)) = τ.restrict (hW.trans (𝒱.inter_le
    (pair hab) 0)) := by
    let U : (W : Scheme.{u}).Modules := SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf
    let M : (W : Scheme.{u}).Modules := (Scheme.Modules.pullback W.ι).obj 𝓜
    let Ra : M ≅ U := τ.restrict (hW.trans (𝒱.inter_le (pair hab) 0))
    let Rb : M ≅ U := τ.restrict (hW.trans (𝒱.inter_le (pair hab) 1))
    have he : Ra.inv ≫ Rb.hom = 𝟙 U := congrArg Iso.hom E
    exact Iso.ext (((Iso.inv_comp_eq Ra).mp he).trans (Category.comp_id Ra.hom))
  rw [restrict_congr_idx τ (pair_zero hab) _ ha, restrict_congr_idx τ (pair_one hab) _ hb] at E'
  exact E'.symm

theorem restrict_indep (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1)
    {a b : 𝒱.ι} {W : Y.Opens} (ha : W ≤ 𝒱.U a) (hb : W ≤ 𝒱.U b) :
    τ.restrict ha = τ.restrict hb := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact restrict_eq_of_lt τ h1 hab ha hb
  · rfl
  · exact (restrict_eq_of_lt τ h1 hba hb ha).symm

theorem mapIso_pullbackUnitIso_trans {W W' : Y.Opens} (h' : W' ≤ W) :
    (Scheme.Modules.pullback (Y.homOfLE h')).mapIso (pullbackUnitIso W.ι) ≪≫ pullbackUnitIso
      (Y.homOfLE h') =
      κiso (SheafOfModules.unit Y.ringCatSheaf) h' ≪≫ pullbackUnitIso W'.ι := by
  let L : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let U : (W : Scheme.{u}).Modules := SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf
  let U' : (W' : Scheme.{u}).Modules := SheafOfModules.unit (W' : Scheme.{u}).ringCatSheaf
  let q := Y.homOfLE h'
  let F := Scheme.Modules.pullback q
  let e : (Scheme.Modules.pullback W.ι).obj L ≅ U := pullbackUnitIso W.ι
  let ε : F.obj U ≅ U' := pullbackUnitIso q
  let δ : (Scheme.Modules.pullback W'.ι).obj L ≅ U' := pullbackUnitIso W'.ι
  let b := (pullbackComp q W.ι).hom.app L
  let c := (pullbackCongr (Y.homOfLE_ι h')).hom.app L
  have hu : b ≫ (pullbackUnitIso (q ≫ W.ι)).hom = F.map e.hom ≫ ε.hom :=
    Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom q W.ι
  have hc : c ≫ δ.hom = (pullbackUnitIso (q ≫ W.ι)).hom :=
    congr_unit (T' := (W' : Scheme)) (T := Y) (Y.homOfLE_ι h')
  apply Iso.ext
  exact hu.symm.trans
    ((congrArg (fun k : (Scheme.Modules.pullback (q ≫ W.ι)).obj L ⟶ U' => b ≫ k) hc.symm).trans
      (Category.assoc b c δ.hom).symm)

variable (𝒱) in
/-- Open subsets contained in at least one member of the ordered affine cover. -/
def Sub : Type u := {W : Y.Opens // ∃ a : 𝒱.ι, W ≤ 𝒱.U a}

/-- Choose a cover member containing an open subset subordinate to the cover. -/
noncomputable def ch (i : Sub 𝒱) : 𝒱.ι := i.2.choose

theorem le_ch (i : Sub 𝒱) : i.1 ≤ 𝒱.U (ch i) := i.2.choose_spec

theorem iSup_sub_eq_top : ⨆ i : Sub 𝒱, i.1 = ⊤ := by
  rw [eq_top_iff, ← 𝒱.iSup_eq_top]
  exact iSup_le fun a => le_iSup_of_le (⟨𝒱.U a, a, le_rfl⟩ : Sub 𝒱) le_rfl

theorem sub_basisLike (i j : Sub 𝒱) :
    i.1 ⊓ j.1 ≤ ⨆ (k : {k : Sub 𝒱 // k.1 ≤ i.1 ⊓ j.1}), k.1.1 :=
  le_iSup_of_le (⟨⟨i.1 ⊓ j.1, ch i, inf_le_left.trans (le_ch i)⟩, le_rfl⟩ : {k : Sub 𝒱 // k.1 ≤
    i.1 ⊓ j.1})
    le_rfl

/-- Compare the module with the unit module after pullback to a subordinate open subset. -/
noncomputable def eSub (i : Sub 𝒱) :
    (Scheme.Modules.pullback i.1.ι).obj 𝓜 ≅
      (Scheme.Modules.pullback i.1.ι).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  τ.restrict (le_ch i) ≪≫ (pullbackUnitIso i.1.ι).symm

theorem eSub_compat (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1) (i j : Sub 𝒱) (h : j.1 ≤ i.1) :
    (Scheme.Modules.pullback (Y.homOfLE h)).mapIso (eSub τ i) =
      ((Scheme.Modules.pullbackComp (Y.homOfLE h) i.1.ι).app 𝓜 ≪≫
          (Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app 𝓜) ≪≫
        eSub τ j ≪≫
        ((Scheme.Modules.pullbackComp (Y.homOfLE h) i.1.ι).app (SheafOfModules.unit
          Y.ringCatSheaf) ≪≫
          (Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app (SheafOfModules.unit
            Y.ringCatSheaf)).symm := by
  let Wi : Y.Opens := i.1
  let Wj : Y.Opens := j.1
  let hij : Wj ≤ Wi := h
  let q := Y.homOfLE hij
  let F := Scheme.Modules.pullback q
  let L : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let Ui : (Wi : Scheme.{u}).Modules := SheafOfModules.unit (Wi : Scheme.{u}).ringCatSheaf
  let Uj : (Wj : Scheme.{u}).Modules := SheafOfModules.unit (Wj : Scheme.{u}).ringCatSheaf
  let Mi : (Wi : Scheme.{u}).Modules := (Scheme.Modules.pullback Wi.ι).obj 𝓜
  let Mj : (Wj : Scheme.{u}).Modules := (Scheme.Modules.pullback Wj.ι).obj 𝓜
  let Ki : (Wi : Scheme.{u}).Modules := (Scheme.Modules.pullback Wi.ι).obj L
  let Kj : (Wj : Scheme.{u}).Modules := (Scheme.Modules.pullback Wj.ι).obj L
  let Ra : Mi ≅ Ui := τ.restrict (le_ch i)
  let Rb : Mj ≅ Uj := τ.restrict (le_ch j)
  let a : F.obj Mi ≅ Mj := κiso 𝓜 hij
  let b : F.obj Ki ≅ Kj := κiso L hij
  let c : Ki ≅ Ui := pullbackUnitIso Wi.ι
  let d : Kj ≅ Uj := pullbackUnitIso Wj.ι
  let ε : F.obj Ui ≅ Uj := pullbackUnitIso q
  have hr : a.symm ≪≫ F.mapIso Ra ≪≫ ε = Rb :=
    (restrict_trans τ (le_ch i) hij).symm.trans
      (restrict_indep τ h1 (hij.trans (le_ch i)) (le_ch j))
  have hres : F.mapIso Ra = a ≪≫ Rb ≪≫ ε.symm := by
    apply Iso.ext
    have hx := congrArg (fun k : Mj ⟶ Uj => a.hom ≫ k ≫ ε.inv)
      (congrArg (fun k : Mj ≅ Uj => k.hom) hr)
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using hx
  have hu : F.mapIso c ≪≫ ε = b ≪≫ d := mapIso_pullbackUnitIso_trans (Y := Y) hij
  have hunit : F.mapIso c.symm = ε ≪≫ d.symm ≪≫ b.symm := by
    have hx := congrArg (fun k : F.obj Ki ≅ Uj => ε ≪≫ k.symm) hu
    have hmap : F.mapIso c.symm = (F.mapIso c).symm := F.mapIso_symm c
    refine hmap.trans ?_
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
      Iso.hom_inv_id_assoc] using congrArg (fun k : F.obj Ui ≅ F.obj Ki => k.hom) hx
  have hfinal : F.mapIso (Ra ≪≫ c.symm) = a ≪≫ (Rb ≪≫ d.symm) ≪≫ b.symm := by
    apply Iso.ext
    have hx := congrArg (fun k : F.obj Mi ≅ F.obj Ki => k.hom)
      ((F.mapIso_trans Ra c.symm).trans (congrArg₂ Iso.trans hres hunit))
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using hx
  exact hfinal

theorem main (h1 : ∀ s : 𝒱.Idx 1, τ.transition s = 1) :
    Nonempty (𝓜 ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  obtain ⟨f, -, -⟩ :=
    Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top 𝓜
      (SheafOfModules.unit Y.ringCatSheaf) (fun i : Sub 𝒱 => i.1) iSup_sub_eq_top sub_basisLike
      (eSub τ) (eSub_compat τ h1)
  exact ⟨f⟩

end L5G

end AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivIsoUnitAll

section PublicStatement

open
  _root_.CategoryTheory
  _root_.CategoryTheory.Limits
  _root_.AlgebraicGeometry
  _root_.Opposite
  _root_.TopologicalSpace
universe u
open _root_.AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivIsoUnitAll.L5G.UA
open _root_.AlgebraicCurves.Cohomology.Cech.Proofs.SchemeModulesCechTrivIsoUnitAll

namespace AlgebraicGeometry.Scheme.Modules.CechTrivialisation

theorem nonempty_iso_unit_of_forall_transition_eq_one
    {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    (h : ∀ s : 𝒱.Idx 1, τ.transition s = 1) :
    Nonempty (𝓜 ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  exact L5G.main τ h

end AlgebraicGeometry.Scheme.Modules.CechTrivialisation

end PublicStatement
end ProofImplementation

attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
