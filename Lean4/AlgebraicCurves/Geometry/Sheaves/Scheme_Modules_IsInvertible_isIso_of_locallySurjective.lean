/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_locallySurjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.Functor
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Tactic.DefEqTransformations

/-!
# Locally surjective maps between invertible module sheaves

A locally surjective morphism between invertible module sheaves is an isomorphism,
using unit-module maps under local trivializations and a covering criterion.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_isIso_of_locallySurjective

universe u v

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite

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

variable {X : Scheme.{u}}

/-- Restricts a given trivialization to a smaller open subset. -/
def lbF_restrictTrivOfLE {L : X.Modules} {U W : X.Opens} (h : W ≤ U)
    (e : (Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    L.restrict W.ι ≅ (SheafOfModules.unit W.toScheme.ringCatSheaf : W.toScheme.Modules) :=
  (restrictFunctorCongr (X.homOfLE_ι h).symm).app L ≪≫
    (restrictFunctorComp (X.homOfLE h) U.ι).app L ≪≫
    (restrictFunctor (X.homOfLE h)).mapIso ((restrictFunctorIsoPullback U.ι).app L ≪≫ e) ≪≫
    (restrictFunctorIsoPullback (X.homOfLE h)).app _ ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)

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

variable {W : Scheme.{u}}

/-- The structure sheaf as a module over itself. -/
abbrev lbF_unitModule (W : Scheme.{u}) : W.Modules := SheafOfModules.unit W.ringCatSheaf

local notation "𝒪[" W "]" => lbF_unitModule W

/-- Views a section of the structure sheaf as a section of its unit module. -/
def lbF_toSec (U : W.Opens) : Γ(W, U) → Γ(𝒪[W], U) := fun r ↦ r

/-- Views a section of the unit module as a section of the structure sheaf. -/
def lbF_ofSec (U : W.Opens) : Γ(𝒪[W], U) → Γ(W, U) := fun m ↦ m

@[scoped simp] lemma lbF_ofSec_toSec (U : W.Opens) (r : Γ(W, U)) : lbF_ofSec U (lbF_toSec U r) = r
    := rfl
@[scoped simp] lemma lbF_toSec_ofSec (U : W.Opens) (m : Γ(𝒪[W], U)) : lbF_toSec U (lbF_ofSec U m) =
    m := rfl
lemma lbF_ofSec_injective (U : W.Opens) : Function.Injective (lbF_ofSec (W := W) U) := fun _ _ h ↦ h

lemma lbF_ofSec_map (U V : W.Opens) (i : V ≤ U) (m : Γ(𝒪[W], U)) :
    lbF_ofSec V ((𝒪[W]).presheaf.map (homOfLE i).op m) = W.presheaf.map (homOfLE i).op (lbF_ofSec U
        m) :=
  rfl

lemma lbF_ofSec_app_smul (ψ : 𝒪[W] ⟶ 𝒪[W]) (U : W.Opens) (r : Γ(W, U)) (m : Γ(𝒪[W], U)) :
    lbF_ofSec U (ψ.app U (r • m)) = r * lbF_ofSec U (ψ.app U m) :=
  congrArg (lbF_ofSec U) (Modules.Hom.app_smul ψ r m)

lemma lbF_smul_toSec_one (U : W.Opens) (r : Γ(W, U)) : r • lbF_toSec U 1 = lbF_toSec U r :=
  mul_one r

theorem lbF_unitEndo_isIso_of_locallySurjective (ψ : 𝒪[W] ⟶ 𝒪[W])
    (hψ : ∀ (U : W.Opens) (s : Γ(𝒪[W], U)), ∀ x ∈ U, ∃ (V : W.Opens) (i : V ≤ U),
      x ∈ V ∧ (𝒪[W]).presheaf.map (homOfLE i).op s ∈ Set.range (ψ.app V)) :
    IsIso ψ := by
  let c : ∀ U : W.Opens, Γ(W, U) := fun U ↦ lbF_ofSec U (ψ.app U (lbF_toSec U 1))
  have hmul : ∀ (U : W.Opens) (m : Γ(𝒪[W], U)), lbF_ofSec U (ψ.app U m) = lbF_ofSec U m * c U :=
    fun U m ↦ by
    have := lbF_ofSec_app_smul ψ U (lbF_ofSec U m) (lbF_toSec U 1)
    rw [lbF_smul_toSec_one] at this
    exact this
  have hres : ∀ (U V : W.Opens) (i : V ≤ U), W.presheaf.map (homOfLE i).op (c U) = c V :=
    fun U V i ↦ by
    have nat := congrArg (fun g ↦ lbF_ofSec V (g (lbF_toSec U 1))) (ψ.mapPresheaf.naturality
        (homOfLE i).op)
    simp only [Modules.mapPresheaf_app, Opposite.unop_op] at nat
    change lbF_ofSec V (ψ.app V ((𝒪[W]).presheaf.map (homOfLE i).op (lbF_toSec U 1))) =
      lbF_ofSec V ((𝒪[W]).presheaf.map (homOfLE i).op (ψ.app U (lbF_toSec U 1))) at nat
    rw [lbF_ofSec_map] at nat
    have h1 : (𝒪[W]).presheaf.map (homOfLE i).op (lbF_toSec U 1) = lbF_toSec V 1 :=
      congrArg (lbF_toSec V) (map_one (W.presheaf.map (homOfLE i).op).hom)
    rw [h1] at nat
    exact nat.symm
  have hunit : ∀ U : W.Opens, IsUnit (c U) := fun U ↦ by
    apply W.toLocallyRingedSpace.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    obtain ⟨V, i, hxV, t, ht⟩ := hψ U (lbF_toSec U 1) x hx
    have ht' : lbF_ofSec V t * c V = 1 := by
      rw [← hmul V t, ht, lbF_ofSec_map]
      exact map_one (W.presheaf.map (homOfLE i).op).hom
    have hcV : IsUnit (c V) := ⟨⟨c V, lbF_ofSec V t, (mul_comm _ _).trans ht', ht'⟩, rfl⟩
    rw [← hres U V i] at hcV
    have := hcV.map (W.presheaf.germ V x hxV).hom
    rwa [TopCat.Presheaf.germ_res_apply] at this
  rw [Modules.Hom.isIso_iff_isIso_app]
  intro U
  obtain ⟨u, hu⟩ := hunit U
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro m₁ m₂ h
    apply lbF_ofSec_injective U
    have h' : lbF_ofSec U m₁ * u = lbF_ofSec U m₂ * u := by
      rw [hu, ← hmul, ← hmul]
      exact congrArg _ h
    exact (Units.mul_left_inj u).mp h'
  · intro s
    refine ⟨lbF_toSec U (lbF_ofSec U s * ↑u⁻¹), lbF_ofSec_injective U ?_⟩
    rw [hmul, lbF_ofSec_toSec, ← hu, Units.inv_mul_cancel_right]

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

variable {X : Scheme.{u}}

theorem lbF_isIso_of_isIso_app_of_iSup_eq_top {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {ι :
  Type v}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ (i : ι) (V : X.Opens), V ≤ U i → IsIso (φ.app V)) : IsIso φ := by
  have cover : ∀ x : X, ∃ i, x ∈ U i := fun x ↦
    TopologicalSpace.Opens.mem_iSup.mp (by rw [hU]; trivial)
  let F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := ⟨M.presheaf, M.isSheaf⟩
  let G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := ⟨N.presheaf, N.isSheaf⟩
  let ψ : F ⟶ G := ⟨φ.mapPresheaf⟩
  have : (Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u}) :=
    inferInstance
  have hψ : IsIso ψ := by
    refine (Sheaf.isLocallyBijective_iff_isIso ψ).mp ⟨?_, ?_⟩
    · refine ⟨fun {W} x y hxy p hp ↦ ?_⟩
      obtain ⟨i, hi⟩ := cover p
      refine ⟨W.unop ⊓ U i, homOfLE inf_le_left, ?_, hp, hi⟩
      have hiso := h i (W.unop ⊓ U i) inf_le_right
      apply (ConcreteCategory.bijective_of_isIso (φ.app (W.unop ⊓ U i))).1
      change φ.mapPresheaf.app _ (M.presheaf.map _ x) = φ.mapPresheaf.app _ (M.presheaf.map _ y)
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact congrArg _ hxy
    · refine ⟨fun {W} s p hp ↦ ?_⟩
      obtain ⟨i, hi⟩ := cover p
      refine ⟨W ⊓ U i, homOfLE inf_le_left, ?_, hp, hi⟩
      have hiso := h i (W ⊓ U i) inf_le_right
      obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso (φ.app (W ⊓ U i))).2
        (N.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op s)
      exact ⟨t, ht⟩
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  have : IsIso ((sheafToPresheaf _ _).map ψ) := inferInstance
  have : IsIso (ψ.hom.app (Opposite.op V)) := by
    change IsIso (((sheafToPresheaf _ _).map ψ).app (Opposite.op V))
    infer_instance
  exact this

namespace IsInvertible
open _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible
end IsInvertible
open scoped _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible in
theorem IsInvertible.isIso_of_locallySurjective' {L L' : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L') (φ : L ⟶ L')
    (hφ : ∀ (U : X.Opens) (s : Γ(L', U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ L'.presheaf.map (homOfLE i).op s ∈ Set.range (φ.app V)) : IsIso φ := by
  choose U₁ hxU₁ e₁ using hL.exists_trivialization
  choose U₂ hxU₂ e₂ using hL'.exists_trivialization
  let W : X → X.Opens := fun x ↦ U₁ x ⊓ U₂ x
  have hcover : ⨆ x, W x = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU₁ x, hxU₂ x⟩
  apply lbF_isIso_of_isIso_app_of_iSup_eq_top φ W hcover
  intro x V hV
  let Wx : X.Opens := W x
  let a : L.restrict Wx.ι ≅ lbF_unitModule Wx.toScheme :=
    lbF_restrictTrivOfLE (inf_le_left : Wx ≤ U₁ x) (e₁ x).some
  let b : L'.restrict Wx.ι ≅ lbF_unitModule Wx.toScheme :=
    lbF_restrictTrivOfLE (inf_le_right : Wx ≤ U₂ x) (e₂ x).some
  let φW : L.restrict Wx.ι ⟶ L'.restrict Wx.ι := (restrictFunctor Wx.ι).map φ
  let ψ : lbF_unitModule Wx.toScheme ⟶ lbF_unitModule Wx.toScheme := a.inv ≫ φW ≫ b.hom
  have ha : ∀ (U' : Wx.toScheme.Opens) (m : Γ(L.restrict Wx.ι, U')),
      a.inv.app U' (a.hom.app U' m) = m := fun U' m ↦ by
    have := congrArg (fun g ↦ _root_.AlgebraicGeometry.Scheme.Modules.Hom.app g U' m) a.hom_inv_id
    simp only [_root_.AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
        _root_.AlgebraicGeometry.Scheme.Modules.Hom.id_app] at this
    exact this
  have hb : ∀ (U' : Wx.toScheme.Opens) (m : Γ(lbF_unitModule Wx.toScheme, U')),
      b.hom.app U' (b.inv.app U' m) = m := fun U' m ↦ by
    have := congrArg (fun g ↦ _root_.AlgebraicGeometry.Scheme.Modules.Hom.app g U' m) b.inv_hom_id
    simp only [_root_.AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
        _root_.AlgebraicGeometry.Scheme.Modules.Hom.id_app] at this
    exact this
  have hψ : ∀ (U' : Wx.toScheme.Opens) (s : Γ(lbF_unitModule Wx.toScheme, U')), ∀ y ∈ U',
      ∃ (V' : Wx.toScheme.Opens) (i : V' ≤ U'), y ∈ V' ∧
        (lbF_unitModule Wx.toScheme).presheaf.map (homOfLE i).op s ∈ Set.range (ψ.app V') := by
    intro U' s y hy
    have hy' : y.1 ∈ Wx.ι ''ᵁ U' := ⟨y, hy, rfl⟩
    let eU₂ := L'.restrictAppIso Wx.ι U'
    let sU : Γ(L', Wx.ι ''ᵁ U') := eU₂.hom (b.inv.app U' s)
    obtain ⟨V₀, i₀, hyV₀, t₀, ht₀⟩ := hφ (Wx.ι ''ᵁ U') sU y.1 hy'
    let V' : Wx.toScheme.Opens := Wx.ι ⁻¹ᵁ V₀
    have i : V' ≤ U' := by
      intro z hz
      obtain ⟨z', hz', hzz'⟩ := i₀ hz
      have : z' = z := Subtype.ext hzz'
      exact this ▸ hz'
    have hyV' : y ∈ V' := hyV₀
    have hle : Wx.ι ''ᵁ V' ≤ V₀ := Wx.ι.image_preimage_le V₀
    let tV : Γ(L.restrict Wx.ι, V') :=
      (L.restrictAppIso Wx.ι V').inv (L.presheaf.map (homOfLE hle).op t₀)
    refine ⟨V', i, hyV', a.hom.app V' tV, ?_⟩
    have hEval : ψ.app V' (a.hom.app V' tV) =
        b.hom.app V' (φW.app V' (a.inv.app V' (a.hom.app V' tV))) := by
      dsimp only [ψ]
      rw [_root_.AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
        _root_.AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
      simp only [ConcreteCategory.comp_apply]
    have haa := congrArg
      (fun q : Γ(L.restrict Wx.ι, V') => b.hom.app V' (φW.app V' q)) (ha V' tV)
    refine (hEval.trans haa).trans ?_
    let eV₂ := L'.restrictAppIso Wx.ι V'
    let bV : Γ(L'.restrict Wx.ι, V') → Γ(lbF_unitModule Wx.toScheme, V') :=
      fun q => b.hom.app V' q
    have hrestrict : φW.app V' tV =
        eV₂.inv (φ.app (Wx.ι ''ᵁ V') (L.presheaf.map (homOfLE hle).op t₀)) := by
      rfl
    have nat := congrArg (fun g ↦ g t₀) (φ.mapPresheaf.naturality (homOfLE hle).op)
    simp only [mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
    have hn : φ.app (Wx.ι ''ᵁ V') (L.presheaf.map (homOfLE hle).op t₀) =
        L'.presheaf.map (homOfLE hle).op (L'.presheaf.map (homOfLE i₀).op sU) :=
      nat.trans (congrArg (fun q : Γ(L', V₀) => L'.presheaf.map (homOfLE hle).op q) ht₀)
    have hlocal : φW.app V' tV =
        eV₂.inv (L'.presheaf.map (homOfLE hle).op (L'.presheaf.map (homOfLE i₀).op sU)) :=
      hrestrict.trans (congrArg (fun q : Γ(L', Wx.ι ''ᵁ V') => eV₂.inv q) hn)
    refine (congrArg bV hlocal).trans ?_
    have hmaps : L'.presheaf.map (homOfLE hle).op (L'.presheaf.map (homOfLE i₀).op sU) =
        L'.presheaf.map (Wx.ι.opensFunctor.map (homOfLE i)).op sU := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      exact congrFun (congrArg (fun k ↦ ⇑(ConcreteCategory.hom (L'.presheaf.map k)))
        (Subsingleton.elim _ _)) sU
    have hmap : (L'.restrict Wx.ι).presheaf.map (homOfLE i).op (eU₂.inv sU) =
        eV₂.inv (L'.presheaf.map (Wx.ι.opensFunctor.map (homOfLE i)).op sU) := by
      have H := congrArg
        (fun q : Γ(L', Wx.ι ''ᵁ U') ⟶ Γ(L'.restrict Wx.ι, V') => q sU)
        (restrictAppIso_inv_map (f := Wx.ι) L' (homOfLE i).op)
      simp only [ConcreteCategory.comp_apply] at H
      exact H
    have hcancel : eU₂.inv sU = b.inv.app U' s := by
      have H := congrArg
        (fun q : Γ(L'.restrict Wx.ι, U') ⟶ Γ(L'.restrict Wx.ι, U') => q (b.inv.app U' s))
        eU₂.hom_inv_id
      simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at H
      exact H
    have hcomp : eV₂.inv (L'.presheaf.map (homOfLE hle).op
        (L'.presheaf.map (homOfLE i₀).op sU)) =
        (L'.restrict Wx.ι).presheaf.map (homOfLE i).op (b.inv.app U' s) :=
      (congrArg (fun q : Γ(L', Wx.ι ''ᵁ V') => eV₂.inv q) hmaps).trans
        (hmap.symm.trans (congrArg
          (fun q : Γ(L'.restrict Wx.ι, U') => (L'.restrict Wx.ι).presheaf.map (homOfLE i).op q)
              hcancel))
    refine (congrArg bV hcomp).trans ?_
    have natb := congrArg (fun g ↦ g s) (b.inv.mapPresheaf.naturality (homOfLE i).op)
    simp only [mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at natb
    dsimp only [bV]
    rw [← natb]
    have hId := congrArg
      (fun k : lbF_unitModule Wx.toScheme ⟶ lbF_unitModule Wx.toScheme => k.app V')
      b.inv_hom_id
    rw [_root_.AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
      _root_.AlgebraicGeometry.Scheme.Modules.Hom.id_app] at hId
    have H := congrArg
      (fun q : Γ(lbF_unitModule Wx.toScheme, V') ⟶ Γ(lbF_unitModule Wx.toScheme, V') =>
        q ((lbF_unitModule Wx.toScheme).presheaf.map (homOfLE i).op s)) hId
    simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at H
    beta_reduce at H ⊢
    dsimp only [_root_.AlgebraicGeometry.Scheme.Opens] at H ⊢
    exact H
  have : IsIso ψ := lbF_unitEndo_isIso_of_locallySurjective ψ hψ
  have hφW : IsIso φW := by
    have : φW = a.hom ≫ ψ ≫ b.inv := by simp [ψ]
    rw [this]
    infer_instance
  have hV' : Wx.ι ''ᵁ (Wx.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hV
  rw [← hV']
  change IsIso (φW.app (Wx.ι ⁻¹ᵁ V))
  infer_instance

end AlgebraicGeometry.Scheme.Modules

end

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_locallySurjective
    {X : Scheme.{u}} {L L' : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (hL' : Scheme.Modules.IsInvertible L') (φ : L ⟶ L')
    (hφ : ∀ (U : X.Opens) (s : Γ(L', U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ L'.presheaf.map (homOfLE i).op s ∈ Set.range (φ.app V)) : IsIso φ :=
  AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_locallySurjective' hL hL' φ hφ
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_isIso_of_locallySurjective
end ProofImplementation
