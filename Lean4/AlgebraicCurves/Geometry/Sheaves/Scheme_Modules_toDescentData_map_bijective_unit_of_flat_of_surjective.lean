/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_unit_of_flat_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.Functor
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Forget
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sieves.Basic
import Mathlib.CategoryTheory.Sites.Sieves.Presieve
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Set
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Descent of endomorphisms of the unit module

The fpqc sheaf property of functions gives descent of endomorphisms through pullback.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_toDescentData_map_bijective_unit_of_flat_of_surjective

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.CategoryTheory.Bicategory
open _root_.TopologicalSpace

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace HomDescO
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

/-- The pseudofunctor of modules used for descent. -/
abbrev MOD : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  (AlgebraicGeometry.Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

variable {X Y Z : Scheme.{u}}

private local instance pushforwardRightAdjoint (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint

example (f : X ⟶ Y) : IsIso (SheafOfModules.pullbackObjUnitToUnit.{u}
    (F := Opens.map f.base) f.toRingCatSheafHom) :=
  (Scheme.Modules.pullbackUnitIso f).isIso_hom

/-- The unit module of a scheme. -/
abbrev OO (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The natural unit morphism into the pushforward of the unit module. -/
abbrev uu (f : X ⟶ Y) : OO Y ⟶ (Scheme.Modules.pushforward f).obj (OO X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- The pullback of the unit module is the unit module. -/
def ee (f : X ⟶ Y) : (Scheme.Modules.pullback f).obj (OO Y) ≅ OO X :=
  Scheme.Modules.pullbackUnitIso f

lemma homEquiv_ee_hom (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (ee f).hom = uu f := by
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (F := Opens.map f.base) f.toRingCatSheafHom

lemma homEquiv_conjugate {C D : Type*} [Category C] [Category D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) {c : C} {d : D} (f : L₁.obj c ⟶ d) :
    adj₂.homEquiv c d (α.app c ≫ f) = adj₁.homEquiv c d f ≫ (conjugateEquiv adj₁ adj₂ α).app d := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  have h1 := unit_conjugateEquiv adj₁ adj₂ α c
  have h2 := (conjugateEquiv adj₁ adj₂ α).naturality f
  erw [← reassoc_of% h1, ← h2]
  try simp only [Category.assoc]
  try rfl

lemma conjugateEquiv_pullbackComp_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackComp f g).hom = (Scheme.Modules.pushforwardComp f g).inv := by
  have h := conjugateEquiv_comm (adj₁ := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (adj₂ := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (α := (Scheme.Modules.pullbackComp f g).hom) (β := (Scheme.Modules.pullbackComp f g).inv)
    (Scheme.Modules.pullbackComp f g).inv_hom_id
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact (Iso.comp_hom_eq_id _).mp h

lemma uu_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    uu (f ≫ g) ≫ (Scheme.Modules.pushforwardComp f g).inv.app (OO X) =
      uu g ≫ (Scheme.Modules.pushforward g).map (uu f) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp only [Scheme.Modules.Hom.comp_app]
  rfl

lemma pullbackComp_hom_app_ee (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app (OO Z) ≫ (ee (f ≫ g)).hom =
      (Scheme.Modules.pullback f).map (ee g).hom ≫ (ee f).hom := by
  have step1 : (((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _)
        ((Scheme.Modules.pullback f).map (ee g).hom ≫ (ee f).hom) =
      uu g ≫ (Scheme.Modules.pushforward g).map (uu f) := by
    rw [Adjunction.comp_homEquiv]
    change ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
        ((Scheme.Modules.pullback f).map (ee g).hom ≫ (ee f).hom)) = _
    rw [Adjunction.homEquiv_naturality_left, homEquiv_ee_hom, Adjunction.homEquiv_naturality_right,
      homEquiv_ee_hom]
  have step2 : (((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _)
        ((Scheme.Modules.pullbackComp f g).hom.app (OO Z) ≫ (ee (f ≫ g)).hom) =
      uu (f ≫ g) ≫ (Scheme.Modules.pushforwardComp f g).inv.app (OO X) := by
    rw [homEquiv_conjugate (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) _
      (Scheme.Modules.pullbackComp f g).hom, conjugateEquiv_pullbackComp_hom, homEquiv_ee_hom]
  exact (((Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _).injective
    (step2.trans ((uu_comp f g).trans step1.symm))

/-- A unit-module endomorphism evaluated on the global unit section. -/
def evalOne (X : Scheme.{u}) (ψ : OO X ⟶ OO X) : Γ(X, ⊤) :=
  ((OO X).unitHomEquiv ψ).val (op ⊤)

lemma evalOne_eq_app (X : Scheme.{u}) (ψ : OO X ⟶ OO X) :
    evalOne X ψ = (ψ.app ⊤ : Γ(X, ⊤) → Γ(X, ⊤)) (1 : Γ(X, ⊤)) := rfl

lemma sections_evalTop_bijective (M : X.Modules) :
    Function.Bijective (fun s : SheafOfModules.sections M => s.val (op ⊤)) := by
  constructor
  · intro s t h
    apply Subtype.ext
    funext U
    have hs := s.property ((homOfLE (le_top : U.unop ≤ ⊤)).op : op ⊤ ⟶ U)
    have ht := t.property ((homOfLE (le_top : U.unop ≤ ⊤)).op : op ⊤ ⟶ U)
    rw [← hs, ← ht]
    exact congr_arg _ h
  · intro a
    refine ⟨⟨fun U => M.val.presheaf.map ((homOfLE (le_top : U.unop ≤ ⊤)).op : op ⊤ ⟶ U) a, ?_⟩, ?_⟩
    · intro U V i
      change M.val.presheaf.map i (M.val.presheaf.map _ a) = M.val.presheaf.map _ a
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
    · change M.val.presheaf.map _ a = a
      have : ((homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op : op ⊤ ⟶ op ⊤) = 𝟙 _ := Subsingleton.elim _
        _
      rw [this, CategoryTheory.Functor.map_id]
      rfl

lemma evalOne_bijective (X : Scheme.{u}) : Function.Bijective (evalOne X) :=
  (sections_evalTop_bijective (OO X)).comp (OO X).unitHomEquiv.bijective

lemma uu_app_apply (g : X ⟶ Y) (U : Y.Opens) (x : Γ(Y, U)) :
    (Scheme.Modules.Hom.app (uu g) U : Γ(Y, U) → Γ(X, g ⁻¹ᵁ U)) x = g.app U x := rfl

lemma evalOne_conj_pullback (g : X ⟶ Y) (ψ : OO Y ⟶ OO Y) :
    evalOne X ((ee g).inv ≫ (Scheme.Modules.pullback g).map ψ ≫ (ee g).hom) = g.appTop (evalOne Y
      ψ) := by
  generalize hχdef : ((ee g).inv ≫ (Scheme.Modules.pullback g).map ψ ≫ (ee g).hom) = χ
  have hχ : (ee g).hom ≫ χ = (Scheme.Modules.pullback g).map ψ ≫ (ee g).hom := by
    rw [← hχdef]
    simp only [Iso.hom_inv_id_assoc]
  have H : uu g ≫ (Scheme.Modules.pushforward g).map χ = ψ ≫ uu g := by
    have := congr_arg ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _) hχ
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left, homEquiv_ee_hom]
      at this
    exact this
  have H1 := congr_arg (fun κ => (Scheme.Modules.Hom.app κ ⊤ : Γ(Y, ⊤) → Γ(X, g ⁻¹ᵁ ⊤)) (1 : Γ(Y,
    ⊤))) H
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at H1
  rw [evalOne_eq_app, evalOne_eq_app]
  have hunit : (Scheme.Modules.Hom.app (uu g) ⊤ : Γ(Y, ⊤) → Γ(X, g ⁻¹ᵁ ⊤)) (1 : Γ(Y, ⊤)) = (1 :
    Γ(X, g ⁻¹ᵁ ⊤)) :=
    (uu_app_apply g ⊤ (1 : Γ(Y, ⊤))).trans (map_one (g.app ⊤).hom)
  exact (congrArg (fun a : Γ(X, g ⁻¹ᵁ ⊤) => χ.app (g ⁻¹ᵁ ⊤) a) hunit).symm.trans
    (H1.trans (uu_app_apply g ⊤ (ψ.app ⊤ (1 : Γ(Y, ⊤)))))

lemma evalOne_conj_pullHom (p₂ : Y ⟶ Z) (g : X ⟶ Y) (p₁ : X ⟶ Z) (w : g ≫ p₂ = p₁)
    (φ : (Scheme.Modules.pullback p₂).obj (OO Z) ⟶ (Scheme.Modules.pullback p₂).obj (OO Z)) :
    evalOne X ((ee p₁).inv ≫
      (((Scheme.Modules.pullbackCongr w.symm).hom.app _ ≫ (Scheme.Modules.pullbackComp g
        p₂).inv.app _) ≫
        (Scheme.Modules.pullback g).map φ ≫
        ((Scheme.Modules.pullbackComp g p₂).hom.app _ ≫ (Scheme.Modules.pullbackCongr w).hom.app
          _)) ≫
      (ee p₁).hom) = g.appTop (evalOne Y ((ee p₂).inv ≫ φ ≫ (ee p₂).hom)) := by
  subst w
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp,
    Category.comp_id]
  rw [← evalOne_conj_pullback g]
  have E1 := pullbackComp_hom_app_ee g p₂
  have E1' : (ee (g ≫ p₂)).hom = (Scheme.Modules.pullbackComp g p₂).inv.app _ ≫
      ((Scheme.Modules.pullback g).map (ee p₂).hom ≫ (ee g).hom) := by
    rw [← cancel_epi ((Scheme.Modules.pullbackComp g p₂).hom.app (OO Z))]
    erw [Iso.hom_inv_id_app_assoc]
    exact E1
  have E1'' : (ee (g ≫ p₂)).inv = ((ee g).inv ≫ (Scheme.Modules.pullback g).map (ee p₂).inv) ≫
      (Scheme.Modules.pullbackComp g p₂).hom.app _ := by
    rw [← cancel_mono (ee (g ≫ p₂)).hom, Iso.inv_hom_id, E1']
    simp only [Category.assoc]
    erw [Iso.hom_inv_id_app_assoc]
    erw [Iso.map_inv_hom_id_assoc]
    exact (ee g).inv_hom_id.symm
  rw [E1', E1'']
  simp only [Category.assoc, Functor.map_comp]
  erw [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]
  try rfl

theorem modMapComp'_eq {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (s : a ⟶ b) (t : b ⟶ d) (M : MOD.obj
  a) :
    (MOD.mapComp' s t (s ≫ t) rfl).hom.toNatTrans.app M = (MOD.mapComp s t).hom.toNatTrans.app M :=
      by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem modMapComp'_eq_inv {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (s : a ⟶ b) (t : b ⟶ d) (M :
  MOD.obj a) :
    (MOD.mapComp' s t (s ≫ t) rfl).inv.toNatTrans.app M = (MOD.mapComp s t).inv.toNatTrans.app M :=
      by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem modMapComp'_hom_app (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg) (L : Z.Modules) :
    (MOD.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app L =
    (Scheme.Modules.pullbackCongr h.symm).hom.app L ≫ (Scheme.Modules.pullbackComp f g).inv.app L
      := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  exact modMapComp'_eq g.op.toLoc f.op.toLoc L

theorem modMapComp'_inv_app (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg) (L : Z.Modules) :
    (MOD.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app L =
    (Scheme.Modules.pullbackComp f g).hom.app L ≫ (Scheme.Modules.pullbackCongr h).hom.app L := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id]
  exact modMapComp'_eq_inv g.op.toLoc f.op.toLoc L

/-- Global sections viewed as a presheaf of types. -/
abbrev ΓType : Scheme.{u}ᵒᵖ ⥤ Type u := Scheme.Γ ⋙ CategoryTheory.forget CommRingCat

/-- The affine line represents global sections. -/
def yonedaA1IsoΓType :
    yoneda.obj (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))) ≅ ΓType.{u} :=
  NatIso.ofComponents
    (fun X => Equiv.toIso (((AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).trans
      (Equiv.funUnique PUnit.{u + 1} _))))
    (by
      intro X X' f
      ext g
      exact AffineSpace.toSpecMvPolyIntEquiv_comp PUnit.{u + 1} f.unop g default)

lemma ΓType_isSheaf : Presieve.IsSheaf Scheme.fpqcTopology ΓType.{u} :=
  Presieve.isSheaf_iso Scheme.fpqcTopology yonedaA1IsoΓType
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

/-- Global sections on schemes over a fixed base. -/
abbrev ΓOver (Y : Scheme.{u}) : (Over Y)ᵒᵖ ⥤ Type u := (Over.forget Y).op ⋙ ΓType

lemma ΓOver_isSheaf (Y : Scheme.{u}) : Presieve.IsSheaf (Scheme.fpqcTopology.over Y) (ΓOver Y) :=
  (Over.forget Y).op_comp_isSheaf_of_types (Scheme.fpqcTopology.over Y) Scheme.fpqcTopology
    ⟨ΓType, (isSheaf_iff_isSheaf_of_type _ _).2 ΓType_isSheaf⟩

lemma ΓOver_isSheafFor {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [QuasiCompact q] [Flat q] [Surjective q] :
    Presieve.IsSheafFor (ΓOver Y) (Presieve.ofArrows (X := Over.mk (𝟙 Y)) (fun _ : Unit => Over.mk
      q)
      (fun _ : Unit => Over.homMk q)) := by
  refine (ΓOver_isSheaf Y).isSheafFor _ ?_
  rw [GrothendieckTopology.mem_over_iff]
  refine Scheme.fpqcTopology.superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fpqcPrecoverage q))
  rw [Sieve.generate_le_iff]
  rintro Z g ⟨⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨Over.mk q, Over.homMk (𝟙 _) (by simp), Over.homMk q, ⟨()⟩, by ext; simp⟩

/-- The section corresponding to an endomorphism of a pulled-back unit module. -/
def theta {Y : Scheme.{u}} (T : Over Y)
    (φ : (Scheme.Modules.pullback T.hom).obj (OO Y) ⟶ (Scheme.Modules.pullback T.hom).obj (OO Y)) :
    Γ(T.left, ⊤) :=
  evalOne T.left ((ee T.hom).inv ≫ φ ≫ (ee T.hom).hom)

lemma theta_bijective {Y : Scheme.{u}} (T : Over Y) : Function.Bijective (theta T) :=
  (evalOne_bijective T.left).comp (Iso.homCongr (ee T.hom) (ee T.hom)).bijective

lemma evalOne_conj_pullHom' {Y₀ X₁ X₂ : Scheme.{u}} (p₂ : X₂ ⟶ Y₀) (g : X₁ ⟶ X₂) (p₁ : X₁ ⟶ Y₀)
    (w : g ≫ p₂ = p₁)
    (φ : (Scheme.Modules.pullback p₂).obj (OO Y₀) ⟶ (Scheme.Modules.pullback p₂).obj (OO Y₀)) :
    evalOne X₁ ((ee p₁).inv ≫
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := MOD) (M₁ := OO Y₀) (M₂ := OO Y₀)
        (f₁ := p₂) (f₂ := p₂) φ g p₁ p₁ w w) ≫ (ee p₁).hom) =
      g.appTop (evalOne X₂ ((ee p₂).inv ≫ φ ≫ (ee p₂).hom)) := by
  rw [← evalOne_conj_pullHom p₂ g p₁ w φ]
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  rw [modMapComp'_hom_app g p₂ p₁ w, modMapComp'_inv_app g p₂ p₁ w]
  rfl

/-- Endomorphisms of pulled-back unit modules are global sections. -/
def thetaIso (Y : Scheme.{u}) : MOD.presheafHom (OO Y) (OO Y) ≅ ΓOver Y :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (Equiv.ofBijective (theta T.unop) (theta_bijective T.unop)))
    (by
      intro T₂ T₁ f
      ext φ
      exact evalOne_conj_pullHom' T₂.unop.hom f.unop.left T₁.unop.hom (Over.w f.unop) φ)

end AlgebraicGeometry.Scheme.Modules.HomDescO

open AlgebraicGeometry.Scheme.Modules.HomDescO in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_unit_of_flat_of_surjective
    {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [QuasiCompact q] [Flat q] [Surjective q] :
    Function.Bijective
      ((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).map :
          (SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) → _) := by
  exact (Pseudofunctor.bijective_toDescentData_map_iff
    (F := MOD) (f := fun _ : Unit => q) (OO Y) (OO Y)).2
      (Presieve.isSheafFor_iso (thetaIso Y).symm (ΓOver_isSheafFor q))
end
end Scheme_Modules_toDescentData_map_bijective_unit_of_flat_of_surjective
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
