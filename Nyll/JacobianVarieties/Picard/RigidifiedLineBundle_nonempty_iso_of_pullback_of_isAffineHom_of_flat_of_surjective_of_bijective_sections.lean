/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_of_isAffineHom_of_flat_of_surjective_of_bijective_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729

Finite-flat compatible-isomorphism assembly. The existing checked reflection
proof below is retained verbatim and uses the actual invertible-sheaf hom
bijectivity theorem. No open-cover condition or global FullyFaithful structure
is assumed. Upstream Mathlib and Anthropic FLT notices remain in the imported
maintained sources.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Mathlib.Tactic.CategoryTheory.Reassoc
import Nyll.SchemeTheory.CategoryTheory.DescentComparison
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_canonical_pullback_leg_relation
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_toDescentData_map_bijective_of_openCover
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Picard.RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq
import Nyll.AlgebraicCurves.Geometry.Picard.RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app

import Mathlib.Util.WithWeakNamespace

/-!
# Reflection of rigidified line-bundle isomorphisms

Compatible isomorphisms after affine faithfully flat pullback descend to the original
rigidified line bundles, using the bijectivity of global sections.
-/


noncomputable section FiniteNativeDescentReflection

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pseudofunctor

namespace JacobianVarieties.Picard.Proofs.NativeDescentReflection

/-- Lift the two arrows of an actual descent isomorphism using the existing
invertible-sheaf hom descent theorem, then reflect both inverse equations. -/
theorem nonempty_iso_of_descent_iso
    {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (L₁ L₂ : Y.Modules)
    (h₁ : Scheme.Modules.IsInvertible L₁) (h₂ : Scheme.Modules.IsInvertible L₂)
    (e : ((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
      (fun _ : Unit => q)).obj L₁) ≅
      ((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).obj L₂)) :
    Nonempty (L₁ ≅ L₂) := by
  let F : Y.Modules ⥤
      ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData
        (fun _ : Unit => q) :=
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
      (fun _ : Unit => q)
  have hbij (L M : Y.Modules)
      (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M) :
      Function.Bijective (F.map : (L ⟶ M) → (F.obj L ⟶ F.obj M)) :=
    Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
      q L M hL hM
  obtain ⟨f, hf⟩ := (hbij L₁ L₂ h₁ h₂).2 e.hom
  obtain ⟨g, hg⟩ := (hbij L₂ L₁ h₂ h₁).2 e.inv
  refine ⟨⟨f, g, (hbij L₁ L₁ h₁ h₁).1 ?_, (hbij L₂ L₂ h₂ h₂).1 ?_⟩⟩
  · exact (F.map_comp f g).trans
      ((congrArg₂ (fun a b => a ≫ b) hf hg).trans
        (e.hom_inv_id.trans (F.map_id L₁).symm))
  · exact (F.map_comp g f).trans
      ((congrArg₂ (fun a b => a ≫ b) hg hf).trans
        (e.inv_hom_id.trans (F.map_id L₂).symm))


open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_toDescentData_map_bijective_of_openCover.AlgebraicGeometry.Scheme.Modules

/-- Assemble the actual compatible pullback isomorphism before specializing
the affine, flat and surjective map to the finite base change. The existing
finite-flat reflection owner supplies all four required hom-map facts. -/
theorem nonempty_iso_of_compatible_pullback_iso
    {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (sq : Unit → Unit → ChosenPullback q q)
    (sq₃ : ∀ i j k : Unit, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L₁ L₂ : Y.Modules)
    (h₁ : Scheme.Modules.IsInvertible L₁) (h₂ : Scheme.Modules.IsInvertible L₂)
    (e : (HomZar.Mdl.map q.op.toLoc).toFunctor.obj L₁ ≅
      (HomZar.Mdl.map q.op.toLoc).toFunctor.obj L₂)
    (comm : ∀ i j : Unit,
      (HomZar.Mdl.map (sq i j).p₁.op.toLoc).toFunctor.map e.hom ≫
          ((DescentData'.fromDescentDataFunctor HomZar.Mdl sq sq₃).obj
            ((HomZar.Mdl.toDescentData (fun _ : Unit => q)).obj L₂)).hom i j =
        ((DescentData'.fromDescentDataFunctor HomZar.Mdl sq sq₃).obj
          ((HomZar.Mdl.toDescentData (fun _ : Unit => q)).obj L₁)).hom i j ≫
            (HomZar.Mdl.map (sq i j).p₂.op.toLoc).toFunctor.map e.hom) :
    Nonempty (L₁ ≅ L₂) := by
  let ξ : (HomZar.Mdl.toDescentData (fun _ : Unit => q)).obj L₁ ≅
      (HomZar.Mdl.toDescentData (fun _ : Unit => q)).obj L₂ :=
    _root_.CategoryTheory.Pseudofunctor.DescentComparison.isoOfChosenOverlap
      HomZar.Mdl (fun _ : Unit => q) sq sq₃ L₁ L₂ (fun _ => e) comm
  exact nonempty_iso_of_descent_iso q L₁ L₂ h₁ h₂ ξ

end JacobianVarieties.Picard.Proofs.NativeDescentReflection

end FiniteNativeDescentReflection

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.AffineIsoDescent

open _root_.AlgebraicCurves.Geometry.Picard.Proofs
open
  RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq.AlgebraicGeometry.Scheme.Modules
  (unitModule)

universe u v


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.pseudofunctor
  Surjective
  Scheme.Modules.pullback
  Scheme.Pullback.range_fst
  Spec
  Scheme
  Flat
  Scheme.Modules.pullbackCongr
  Scheme.Modules
  IsAffineHom
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  RelPicard.RigidifiedLineBundle
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap
  Scheme.TwoAffineOpenCover.algebraOfHom
  RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
  RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq
  Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
  Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (
  Modules.pseudofunctor
  ringCatSheaf
  Modules.pullback
  Γ
  Pullback.range_fst
  Modules.pullbackCongr
  Modules
  Modules.pullbackComp
  Modules.IsInvertible
  Modules.pullbackUnitIso
  TwoAffineOpenCover
  TwoAffineOpenCover.specMap
  TwoAffineOpenCover.algebraOfHom
  Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
  Modules.pullbackComp_pullbackCongr_pasteSquares_app)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (
  pseudofunctor
  pullback
  pullbackCongr
  pullbackComp
  IsInvertible
  pullbackUnitIso
  IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
  pullbackComp_pullbackCongr_pasteSquares_app)


open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry


variable {X₀ X₁ X₂ X₃ : Scheme.{u}}

/-- Pullback comparison induced by a specified equality of composite scheme morphisms. -/
noncomputable def τ (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m)
    : pullback g ⋙ pullback f ≅ pullback m :=
  pullbackComp f g ≪≫ pullbackCongr e

theorem τ_hom_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).hom.app M = (pullbackComp f g).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e
  rfl

theorem τ_inv_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).inv.app M = eqToHom (by rw [e]) ≫ (pullbackComp f g).inv.app M := by
  subst e
  rfl

/-- The pullback isomorphism attached to a commutative square of schemes. -/
noncomputable def sqIso {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) : pullback g ⋙ pullback f ≅ pullback k ⋙ pullback h :=
  pullbackComp f g ≪≫ pullbackCongr e ≪≫ (pullbackComp h k).symm

theorem sqIso_hom_app {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) (M : Z.Modules) :
    (sqIso e).hom.app M = (τ f g (h ≫ k) e).hom.app M ≫ (τ h k (h ≫ k) rfl).inv.app M := by
  simp only [sqIso, τ, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    NatTrans.comp_app, pullbackCongr, eqToIso_refl, Iso.refl_inv,
    Category.id_comp, Category.assoc]

section Route

variable {X X₀' X₁' Y Y₀ Y₁ : Scheme.{u}}
  (a : X₀' ⟶ X₁') (b : X₁' ⟶ X) (d : X₀' ⟶ X) (e : a ≫ b = d)
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s : Y ⟶ X)
  (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
  (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s)

include e G E F in
theorem route_comm : s₀ ≫ d = m ≫ s := by
  rw [← e, ← Category.assoc, E, Category.assoc, F, ← Category.assoc, G]

theorem route (M : X.Modules) :
    (sqIso E).hom.app ((pullback b).obj M) ≫ (pullback r).map ((sqIso F).hom.app M) ≫
        (τ r p m G).hom.app ((pullback s).obj M) =
      (pullback s₀).map ((τ a b d e).hom.app M) ≫
        (τ s₀ d (m ≫ s) (route_comm a b d e s₀ s₁ s r p m G E F)).hom.app M ≫
          (τ m s (m ≫ s) rfl).inv.app M := by
  exact (AlgebraicGeometry.Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app
    a b d e s₀ s₁ s r p m G E F
    (route_comm a b d e s₀ s₁ s r p m G E F) M).trans
    (congrArg (fun k => (pullback s₀).map ((τ a b d e).hom.app M) ≫ k)
      (sqIso_hom_app (route_comm a b d e s₀ s₁ s r p m G E F) M))

end Route

section Head

variable {X X₀' X₁' X₂' Y Y₀ Y₁ Y₂ : Scheme.{u}}
  (a₁ : X₀' ⟶ X₁') (b₁ : X₁' ⟶ X) (a₂ : X₀' ⟶ X₂') (b₂ : X₂' ⟶ X) (d : X₀' ⟶ X)
  (e₁ : a₁ ≫ b₁ = d) (e₂ : a₂ ≫ b₂ = d)
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s₂ : Y₂ ⟶ X₂') (s : Y ⟶ X)
  (r₁ : Y₀ ⟶ Y₁) (p₁ : Y₁ ⟶ Y) (r₂ : Y₀ ⟶ Y₂) (p₂ : Y₂ ⟶ Y) (m : Y₀ ⟶ Y)
  (G₁ : r₁ ≫ p₁ = m) (G₂ : r₂ ≫ p₂ = m)
  (E₁ : s₀ ≫ a₁ = r₁ ≫ s₁) (F₁ : s₁ ≫ b₁ = p₁ ≫ s) (E₂ : s₀ ≫ a₂ = r₂ ≫ s₂) (F₂ : s₂ ≫ b₂ = p₂ ≫ s)

theorem head (M : X.Modules) :
    (pullback s₀).map ((τ a₁ b₁ d e₁).hom.app M ≫ (τ a₂ b₂ d e₂).inv.app M) ≫
      (sqIso E₂).hom.app ((pullback b₂).obj M) ≫ (pullback r₂).map ((sqIso F₂).hom.app M) ≫
        (τ r₂ p₂ m G₂).hom.app ((pullback s).obj M) =
      (sqIso E₁).hom.app ((pullback b₁).obj M) ≫ (pullback r₁).map ((sqIso F₁).hom.app M) ≫
        (τ r₁ p₁ m G₁).hom.app ((pullback s).obj M) := by
  have h₁ := route a₁ b₁ d e₁ s₀ s₁ s r₁ p₁ m G₁ E₁ F₁ M
  have h₂ := route a₂ b₂ d e₂ s₀ s₂ s r₂ p₂ m G₂ E₂ F₂ M
  have h₂' := (Iso.inv_comp_eq ((pullback s₀).mapIso ((τ a₂ b₂ d e₂).app M))).mpr h₂
  simp only [Functor.map_comp, Category.assoc]
  exact (congrArg (fun k => (pullback s₀).map ((τ a₁ b₁ d e₁).hom.app M) ≫ k) h₂').trans h₁.symm

end Head

section HeadRaw

variable {X X₀' X₁' X₂' : Scheme.{u}}
  (a₁ : X₀' ⟶ X₁') (b₁ : X₁' ⟶ X) (a₂ : X₀' ⟶ X₂') (b₂ : X₂' ⟶ X) (d : X₀' ⟶ X)
  (e₁ : a₁ ≫ b₁ = d) (e₂ : a₂ ≫ b₂ = d)

theorem τ_hom_app_comp_τ_inv_app (M : X.Modules) :
    (τ a₁ b₁ d e₁).hom.app M ≫ (τ a₂ b₂ d e₂).inv.app M =
      (pullbackComp a₁ b₁).hom.app M ≫ (pullbackCongr e₁).hom.app M ≫
        (pullbackCongr e₂.symm).hom.app M ≫
        (pullbackComp a₂ b₂).inv.app M := by
  subst e₁
  simp only [τ, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, pullbackCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.id_comp,
    eqToIso.inv, eqToIso.hom]

variable {Y Y₀ Y₁ Y₂ : Scheme.{u}}
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s₂ : Y₂ ⟶ X₂') (s : Y ⟶ X)
  (r₁ : Y₀ ⟶ Y₁) (p₁ : Y₁ ⟶ Y) (r₂ : Y₀ ⟶ Y₂) (p₂ : Y₂ ⟶ Y) (m : Y₀ ⟶ Y)
  (G₁ : r₁ ≫ p₁ = m) (G₂ : r₂ ≫ p₂ = m)
  (E₁ : s₀ ≫ a₁ = r₁ ≫ s₁) (F₁ : s₁ ≫ b₁ = p₁ ≫ s) (E₂ : s₀ ≫ a₂ = r₂ ≫ s₂) (F₂ : s₂ ≫ b₂ = p₂ ≫ s)

theorem head' (M : X.Modules) :
    (pullback s₀).map ((pullbackComp a₁ b₁).hom.app M ≫ (pullbackCongr e₁).hom.app M ≫
        (pullbackCongr e₂.symm).hom.app M ≫ (pullbackComp a₂ b₂).inv.app M) ≫
      (sqIso E₂).hom.app ((pullback b₂).obj M) ≫ (pullback r₂).map ((sqIso F₂).hom.app M) ≫
        (τ r₂ p₂ m G₂).hom.app ((pullback s).obj M) =
      (sqIso E₁).hom.app ((pullback b₁).obj M) ≫ (pullback r₁).map ((sqIso F₁).hom.app M) ≫
        (τ r₁ p₁ m G₁).hom.app ((pullback s).obj M) := by
  have h := head a₁ b₁ a₂ b₂ d e₁ e₂ s₀ s₁ s₂ s r₁ p₁ r₂ p₂ m G₁ G₂ E₁ F₁ E₂ F₂ M
  rw [τ_hom_app_comp_τ_inv_app] at h
  exact h

end HeadRaw

end AlgebraicGeometry.Scheme.Modules

noncomputable section
namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.pseudofunctor
  Surjective
  Scheme.Modules.pullback
  Scheme.Pullback.range_fst
  Spec
  Scheme
  Flat
  Scheme.Modules.pullbackCongr
  Scheme.Modules
  IsAffineHom
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  RelPicard.RigidifiedLineBundle
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap
  Scheme.TwoAffineOpenCover.algebraOfHom
  RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
  RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq
  Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
  Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  baseChangeSnd
  rigSection
  postComp
  baseChangeSnd_comp
  rigSection_baseChangeSnd
  RigidifiedLineBundle
  RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
  RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq)

namespace DescentAux

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry


open NeronModelInfra

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))

lemma isPullback_baseChangeSnd_snd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 := by
  have big : IsPullback (baseChangeSnd c ψ ≫ pullback.fst c t) (pullback.snd c t') c (ψ.1 ≫ t) := by
    rw [ψ.2, show baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' from
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)]
    exact IsPullback.of_hasPullback c t'
  exact big.of_right ((pullback.lift_snd _ _ _)) (IsPullback.of_hasPullback c t)

lemma isPullback_baseChangeSnd {X U V W : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of R)}
    {uS : U ⟶ Spec (CommRingCat.of R)} {vS : V ⟶ Spec (CommRingCat.of R)}
    {wS : W ⟶ Spec (CommRingCat.of R)}
    (u : SchemeHomOver uS x) (v : SchemeHomOver vS x)
    (a : SchemeHomOver wS uS) (b : SchemeHomOver wS vS)
    (h : IsPullback a.1 b.1 u.1 v.1) :
    IsPullback (baseChangeSnd c a) (baseChangeSnd c b) (baseChangeSnd c u) (baseChangeSnd c v) := by
  have hbig : IsPullback (pullback.snd c wS ≫ a.1) (baseChangeSnd c b) u.1
      (pullback.snd c vS ≫ v.1) :=
    (isPullback_baseChangeSnd_snd c b).flip.paste_horiz h
  have hbig' : IsPullback (baseChangeSnd c a ≫ pullback.snd c uS) (baseChangeSnd c b) u.1
      (baseChangeSnd c v ≫ pullback.snd c x) := by
    rw [show baseChangeSnd c a ≫ pullback.snd c uS = pullback.snd c wS ≫ a.1
        from pullback.lift_snd _ _ _,
      show baseChangeSnd c v ≫ pullback.snd c x = pullback.snd c vS ≫ v.1
        from pullback.lift_snd _ _ _]
    exact hbig
  refine hbig'.of_right ?_ (isPullback_baseChangeSnd_snd c u).flip
  rw [baseChangeSnd_comp, baseChangeSnd_comp]
  congr 1
  exact Subtype.ext h.w

/-- The structure map of the fibre product of two schemes over the same base. -/
abbrev strMap₁₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    pullback ψ₁.1 ψ₂.1 ⟶ Spec (CommRingCat.of R) :=
  pullback.fst ψ₁.1 ψ₂.1 ≫ t₁

/-- The first fibre-product projection as a morphism over the base. -/
def pr₁ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t₁ :=
  ⟨pullback.fst ψ₁.1 ψ₂.1, rfl⟩

/-- The second fibre-product projection as a morphism over the base. -/
def pr₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t₂ :=
  ⟨pullback.snd ψ₁.1 ψ₂.1, by
    have h2 : pullback.snd ψ₁.1 ψ₂.1 ≫ ψ₂.1 ≫ t = pullback.snd ψ₁.1 ψ₂.1 ≫ t₂ := by rw [ψ₂.2]
    have h1 : pullback.fst ψ₁.1 ψ₂.1 ≫ ψ₁.1 ≫ t = pullback.fst ψ₁.1 ψ₂.1 ≫ t₁ := by rw [ψ₁.2]
    change pullback.snd ψ₁.1 ψ₂.1 ≫ t₂ = pullback.fst ψ₁.1 ψ₂.1 ≫ t₁
    rw [← h2, ← h1, ← Category.assoc, ← pullback.condition, Category.assoc]⟩

@[scoped simp] lemma pr₁_val {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (pr₁ ψ₁ ψ₂).1 = pullback.fst ψ₁.1 ψ₂.1 := rfl

@[scoped simp] lemma pr₂_val {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (pr₂ ψ₁ ψ₂).1 = pullback.snd ψ₁.1 ψ₂.1 := rfl

lemma postComp_pr₁_eq_postComp_pr₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    postComp ψ₁ (pr₁ ψ₁ ψ₂) = postComp ψ₂ (pr₂ ψ₁ ψ₂) :=
  Subtype.ext pullback.condition

/-- The chosen pullback square after base change to the curve. -/
def chosenPullback {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    ChosenPullback (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) where
  pullback := Limits.pullback c (strMap₁₂ ψ₁ ψ₂)
  p₁ := baseChangeSnd c (pr₁ ψ₁ ψ₂)
  p₂ := baseChangeSnd c (pr₂ ψ₁ ψ₂)
  condition := by
    rw [baseChangeSnd_comp, baseChangeSnd_comp, postComp_pr₁_eq_postComp_pr₂]
  isLimit := (isPullback_baseChangeSnd c ψ₁ ψ₂ (pr₁ ψ₁ ψ₂) (pr₂ ψ₁ ψ₂)
    (IsPullback.of_hasPullback ψ₁.1 ψ₂.1)).isLimit
  p := baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂))
  hp₁ := baseChangeSnd_comp c _ _

@[scoped simp] lemma chosenPullback_p₁ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (chosenPullback c ψ₁ ψ₂).p₁ = baseChangeSnd c (pr₁ ψ₁ ψ₂) := rfl

@[scoped simp] lemma chosenPullback_p₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (chosenPullback c ψ₁ ψ₂).p₂ = baseChangeSnd c (pr₂ ψ₁ ψ₂) := rfl

/-- The chosen triple overlap for the repeated base-changed morphism. -/
def chosenPullback₃ {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    ChosenPullback₃ (chosenPullback c ψ ψ) (chosenPullback c ψ ψ) (chosenPullback c ψ ψ) where
  chosenPullback := chosenPullback c (pr₂ ψ ψ) (pr₁ ψ ψ)
  p := baseChangeSnd c (postComp (postComp ψ (pr₁ ψ ψ)) (pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)))
  p₁ := baseChangeSnd c (postComp (pr₁ ψ ψ) (pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)))
  p₃ := baseChangeSnd c (postComp (pr₂ ψ ψ) (pr₂ (pr₂ ψ ψ) (pr₁ ψ ψ)))
  l :=
    { f := baseChangeSnd c
        ⟨pullback.lift ((pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)).1 ≫ (pr₁ ψ ψ).1)
            ((pr₂ (pr₂ ψ ψ) (pr₁ ψ ψ)).1 ≫ (pr₂ ψ ψ).1)
          (by
            have hT₂ : pullback.fst ψ.1 ψ.1 ≫ ψ.1 = pullback.snd ψ.1 ψ.1 ≫ ψ.1 := pullback.condition
            have hT₃ : pullback.fst (pullback.snd ψ.1 ψ.1) (pullback.fst ψ.1 ψ.1)
                ≫ pullback.snd ψ.1 ψ.1 =
                pullback.snd (pullback.snd ψ.1 ψ.1) (pullback.fst ψ.1 ψ.1) ≫ pullback.fst ψ.1 ψ.1 :=
              pullback.condition
            simp only [pr₁_val, pr₂_val, Category.assoc]
            rw [hT₂, ← Category.assoc, hT₃, Category.assoc, hT₂]),
         by
          simp only [pr₁_val, pr₂_val]
          rw [← Category.assoc, pullback.lift_fst, Category.assoc]
          rfl⟩
      f_p₁ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₁ ψ ψ) = _
        erw [baseChangeSnd_comp]; congr 1; exact Subtype.ext (pullback.lift_fst _ _ _)
      f_p₂ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₂ ψ ψ) = _
        erw [baseChangeSnd_comp]; congr 1; exact Subtype.ext (pullback.lift_snd _ _ _)
      f_p := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (postComp ψ (pr₁ ψ ψ)) = _
        erw [baseChangeSnd_comp]; congr 1
        exact Subtype.ext (by
          change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ ψ.1
              = (pullback.fst _ _ ≫ pullback.fst _ _) ≫ ψ.1
          rw [pullback.lift_fst_assoc, Category.assoc]
          rfl) }
  hp₁ := by
    change baseChangeSnd c (pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)) ≫ baseChangeSnd c (pr₁ ψ ψ) = _
    erw [baseChangeSnd_comp]
  hp₃ := by
    change baseChangeSnd c (pr₂ (pr₂ ψ ψ) (pr₁ ψ ψ)) ≫ baseChangeSnd c (pr₂ ψ ψ) = _
    erw [baseChangeSnd_comp]

end AlgebraicGeometry.RelPicard.DescentAux

attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂



end

attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂


noncomputable section
namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.pseudofunctor
  Surjective
  Scheme.Modules.pullback
  Scheme.Pullback.range_fst
  Spec
  Scheme
  Flat
  Scheme.Modules.pullbackCongr
  Scheme.Modules
  IsAffineHom
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  RelPicard.RigidifiedLineBundle
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap
  Scheme.TwoAffineOpenCover.algebraOfHom
  RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
  RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq
  Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
  Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  baseChangeSnd
  rigSection
  postComp
  baseChangeSnd_comp
  rigSection_baseChangeSnd
  RigidifiedLineBundle
  RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
  RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq)

namespace DescentAux

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry



open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.Scheme.Modules
open AffineIsoDescent.AlgebraicGeometry.Scheme.Modules


variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

/-- An invertible sheaf together with a chosen trivialization along the rigidifying section. -/
structure RigData {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) where
  /-- The underlying sheaf of modules on the base-changed curve. -/
  L : (Limits.pullback c t).Modules
  /-- Invertibility of the underlying sheaf. -/
  isInvertible : Scheme.Modules.IsInvertible L
  /-- The chosen trivialization along the section. -/
  α : (Scheme.Modules.pullback (rigSection c t ε)).obj L ≅
    unitModule T

namespace RigData

variable {c ε} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

/-- Compatibility of a sheaf morphism with the chosen rigidifications. -/
def Compat (A B : RigData c ε t) (φ : A.L ⟶ B.L) : Prop :=
  (Scheme.Modules.pullback (rigSection c t ε)).map φ ≫ B.α.hom = A.α.hom

lemma Compat.id (A : RigData c ε t) : Compat A A (𝟙 A.L) := by
  change (Scheme.Modules.pullback (rigSection c t ε)).map (𝟙 A.L) ≫ A.α.hom = A.α.hom
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

lemma Compat.comp {A B D : RigData c ε t} {φ : A.L ⟶ B.L} {ψ : B.L ⟶ D.L} (hφ : Compat A B φ)
    (hψ : Compat B D ψ) : Compat A D (φ ≫ ψ) := by
  simp only [Compat, Functor.map_comp, Category.assoc] at *
  rw [hψ, hφ]

lemma compat_iff_mapIso (A B : RigData c ε t) (φ : A.L ≅ B.L) :
    Compat A B φ.hom ↔ (Scheme.Modules.pullback (rigSection c t ε)).mapIso φ ≪≫ B.α = A.α := by
  constructor
  · intro h
    apply Iso.ext
    exact h
  · intro h
    exact congrArg Iso.hom h

lemma Compat.inv {A B : RigData c ε t} {φ : A.L ≅ B.L} (h
    : Compat A B φ.hom) : Compat B A φ.inv := by
  simp only [Compat] at *
  rw [← h, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Transport rigidification data across an isomorphism of the underlying sheaves. -/
def ofIso (A : RigData c ε t) (L' : (Limits.pullback c t).Modules) (e : L' ≅ A.L)
    (hL' : Scheme.Modules.IsInvertible L') : RigData c ε t where
  L := L'
  isInvertible := hL'
  α := (Scheme.Modules.pullback (rigSection c t ε)).mapIso e ≪≫ A.α

lemma ofIso_compat_iff {A B : RigData c ε t} {LA LB : (Limits.pullback c t).Modules}
    (eA : LA ≅ A.L) (eB : LB ≅ B.L)
    (hA : Scheme.Modules.IsInvertible LA) (hB : Scheme.Modules.IsInvertible LB) (φ : LA ⟶ LB) :
    Compat (A.ofIso LA eA hA) (B.ofIso LB eB hB) φ ↔ Compat A B (eA.inv ≫ φ ≫ eB.hom) := by
  simp only [Compat, ofIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  constructor
  · intro h
    rw [h, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  · intro h
    rw [← cancel_epi ((Scheme.Modules.pullback (rigSection c t ε)).map eA.inv), ← Category.assoc,
      ← Functor.map_comp] at *
    exact h.trans
      (((Scheme.Modules.pullback (rigSection c t ε)).mapIso eA).inv_hom_id_assoc A.α.hom).symm

/-- Pullback along the section commutes with base change. -/
def rigNatIso {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    Scheme.Modules.pullback (baseChangeSnd c ψ) ⋙ Scheme.Modules.pullback (rigSection c t' ε) ≅
      Scheme.Modules.pullback (rigSection c t ε) ⋙ Scheme.Modules.pullback ψ.1 :=
  Scheme.Modules.pullbackComp (rigSection c t' ε) (baseChangeSnd c ψ) ≪≫
    Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε ψ) ≪≫
    (Scheme.Modules.pullbackComp ψ.1 (rigSection c t ε)).symm

/-- Pull back the sheaf and its rigidification along a morphism over the base. -/
def pb (A : RigData c ε t) {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    RigData c ε t' where
  L := (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A.L
  isInvertible := A.isInvertible.pullback _
  α := (rigNatIso ψ).app A.L ≪≫ (Scheme.Modules.pullback ψ.1).mapIso A.α ≪≫
    Scheme.Modules.pullbackUnitIso ψ.1

@[scoped simp] lemma pb_L (A : RigData c ε t) {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) : (A.pb ψ).L
        = (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A.L := rfl

lemma Compat.pb {A B : RigData c ε t} {φ : A.L ⟶ B.L} (h : Compat A B φ) {T' : Scheme.{u}}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    Compat (A.pb ψ) (B.pb ψ) ((Scheme.Modules.pullback (baseChangeSnd c ψ)).map φ) := by
  let F : (Limits.pullback c t).Modules ⥤ T.Modules := Scheme.Modules.pullback (rigSection c t ε)
  let G : (Limits.pullback c t').Modules ⥤ T'.Modules := Scheme.Modules.pullback (rigSection c t' ε)
  let P : (Limits.pullback c t).Modules ⥤ (Limits.pullback c t').Modules :=
    Scheme.Modules.pullback (baseChangeSnd c ψ)
  let Q : T.Modules ⥤ T'.Modules := Scheme.Modules.pullback ψ.1
  let η : P ⋙ G ≅ F ⋙ Q := rigNatIso ψ
  let U : T.Modules := unitModule T
  let V : T'.Modules := SheafOfModules.unit T'.ringCatSheaf
  let a : F.obj A.L ⟶ U := A.α.hom
  let b : F.obj B.L ⟶ U := B.α.hom
  let u : Q.obj U ≅ V := Scheme.Modules.pullbackUnitIso ψ.1
  let x : G.obj (P.obj A.L) ⟶ Q.obj (F.obj A.L) := η.hom.app A.L
  let y : G.obj (P.obj B.L) ⟶ Q.obj (F.obj B.L) := η.hom.app B.L
  have hn : G.map (P.map φ) ≫ y = x ≫ Q.map (F.map φ) := η.hom.naturality φ
  have h' : F.map φ ≫ b = a := h
  have hq : Q.map (F.map φ) ≫ Q.map b = Q.map a :=
    (Q.map_comp (F.map φ) b).symm.trans (congrArg Q.map h')
  change G.map (P.map φ) ≫ (y ≫ Q.map b ≫ u.hom) = x ≫ Q.map a ≫ u.hom
  have hn' := congrArg
    (fun k : G.obj (P.obj A.L) ⟶ Q.obj (F.obj B.L) => k ≫ Q.map b ≫ u.hom) hn
  have hq' := congrArg
    (fun k : Q.obj (F.obj A.L) ⟶ Q.obj U => x ≫ k ≫ u.hom) hq
  simp only [Category.assoc] at hn' hq'
  exact hn'.trans hq'

end RigData

attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L


end AlgebraicGeometry.RelPicard.DescentAux

attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L


attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L


attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L

end

attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L


noncomputable section
namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.pseudofunctor
  Surjective
  Scheme.Modules.pullback
  Scheme.Pullback.range_fst
  Spec
  Scheme
  Flat
  Scheme.Modules.pullbackCongr
  Scheme.Modules
  IsAffineHom
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  RelPicard.RigidifiedLineBundle
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap
  Scheme.TwoAffineOpenCover.algebraOfHom
  RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
  RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq
  Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
  Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  baseChangeSnd
  rigSection
  postComp
  baseChangeSnd_comp
  rigSection_baseChangeSnd
  RigidifiedLineBundle
  RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
  RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq)

namespace DescentAux

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry


open NeronModelInfra CategoryTheory.Pseudofunctor

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

namespace RigData
variable {c ε} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

/-- Retain a chosen rigidification of a rigidified line bundle. -/
def ofRLB (M : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L
        ≅ unitModule T) :
    RigData c ε t := ⟨M.L, M.isInvertible, α⟩

/-- Forget the choice of rigidification, retaining its existence. -/
def toRLB (A : RigData c ε t) : RigidifiedLineBundle c ε t := ⟨A.L, A.isInvertible, ⟨A.α⟩⟩

lemma exists_compat_iso (A B : RigData c ε t) (h : Nonempty (A.L ≅ B.L)) :
    ∃ φ : A.L ≅ B.L, Compat A B φ.hom := by
  obtain ⟨φ, hφ⟩ := RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
    R c ε t A.toRLB B.toRLB A.α B.α h.some
  exact ⟨φ, (compat_iff_mapIso A B φ).mpr hφ⟩

lemma compat_iso_unique
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (A B : RigData c ε t) (φ ψ : A.L ≅ B.L) (hφ : Compat A B φ.hom) (hψ : Compat A B ψ.hom)
    : φ = ψ :=
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq
    R c ε hH0 t
    A.toRLB B.toRLB A.α B.α φ ψ ((compat_iff_mapIso A B φ).mp hφ) ((compat_iff_mapIso A B ψ).mp hψ)

lemma compat_hom_unique
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (A B : RigData c ε t) (φ ψ : A.L ⟶ B.L) [IsIso φ] [IsIso ψ]
    (hφ : Compat A B φ) (hψ : Compat A B ψ) :
    φ = ψ :=
  congrArg Iso.hom (compat_iso_unique hH0 A B (asIso φ) (asIso ψ) hφ hψ)

end RigData

attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L


@[scoped simp] lemma chosenPullback_p {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (chosenPullback c ψ₁ ψ₂).p = baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)) := rfl

/-- The chosen triple overlap for three morphisms over the base. -/
def chosenPullback₃' {T T₁ T₂ T₃ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    {t₃ : T₃ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) (ψ₃ : SchemeHomOver t₃ t) :
    ChosenPullback₃ (chosenPullback c ψ₁ ψ₂) (chosenPullback c ψ₂ ψ₃) (chosenPullback c ψ₁ ψ₃) where
  chosenPullback := chosenPullback c (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)
  p := baseChangeSnd c (postComp (postComp ψ₁ (pr₁ ψ₁ ψ₂)) (pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)))
  p₁ := baseChangeSnd c (postComp (pr₁ ψ₁ ψ₂) (pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)))
  p₃ := baseChangeSnd c (postComp (pr₂ ψ₂ ψ₃) (pr₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)))
  l :=
    { f := baseChangeSnd c
        ⟨pullback.lift ((pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)).1 ≫ (pr₁ ψ₁ ψ₂).1)
            ((pr₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)).1 ≫ (pr₂ ψ₂ ψ₃).1)
          (by
            have h₁₂ : pullback.fst ψ₁.1 ψ₂.1 ≫ ψ₁.1 = pullback.snd ψ₁.1 ψ₂.1 ≫ ψ₂.1
              := pullback.condition
            have h₂₃ : pullback.fst ψ₂.1 ψ₃.1 ≫ ψ₂.1 = pullback.snd ψ₂.1 ψ₃.1 ≫ ψ₃.1
              := pullback.condition
            have h' : pullback.fst (pullback.snd ψ₁.1 ψ₂.1) (pullback.fst ψ₂.1 ψ₃.1)
                ≫ pullback.snd ψ₁.1 ψ₂.1 =
                pullback.snd (pullback.snd ψ₁.1 ψ₂.1) (pullback.fst ψ₂.1 ψ₃.1)
                  ≫ pullback.fst ψ₂.1 ψ₃.1 :=
              pullback.condition
            simp only [pr₁_val, pr₂_val, Category.assoc]
            rw [h₁₂, ← Category.assoc, h', Category.assoc, h₂₃]),
         by
          simp only [pr₁_val, pr₂_val]
          rw [← Category.assoc, pullback.lift_fst, Category.assoc]
          rfl⟩
      f_p₁ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₁ ψ₁ ψ₃) = _
        erw [baseChangeSnd_comp]; congr 1; exact Subtype.ext (pullback.lift_fst _ _ _)
      f_p₂ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₂ ψ₁ ψ₃) = _
        erw [baseChangeSnd_comp]; congr 1; exact Subtype.ext (pullback.lift_snd _ _ _)
      f_p := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₃)) = _
        erw [baseChangeSnd_comp]; congr 1
        exact Subtype.ext (by
          change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ ψ₁.1
              = (pullback.fst _ _ ≫ pullback.fst _ _) ≫ ψ₁.1
          rw [pullback.lift_fst_assoc, Category.assoc]
          rfl) }
  hp₁ := by
    change baseChangeSnd c (pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) ≫ baseChangeSnd c (pr₁ ψ₁ ψ₂) = _
    erw [baseChangeSnd_comp]
  hp₃ := by
    change baseChangeSnd c (pr₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) ≫ baseChangeSnd c (pr₂ ψ₂ ψ₃) = _
    erw [baseChangeSnd_comp]

lemma exists_mem_range_baseChangeSnd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {ι : Type u} {U : ι → Scheme.{u}} {uS : ∀ i, U i ⟶ Spec (CommRingCat.of R)}
    (f : ∀ i, SchemeHomOver (uS i) t)
    (hf : ∀ x : T, ∃ i, x ∈ Set.range (f i).1.base) (y : ↥(Limits.pullback c t)) :
    ∃ i, y ∈ Set.range (baseChangeSnd c (f i)).base := by
  obtain ⟨i, z, hz⟩ := hf ((pullback.snd c t).base y)
  refine ⟨i, ?_⟩
  have H := isPullback_baseChangeSnd_snd c (f i)
  have hy : y ∈ Set.range (pullback.fst (pullback.snd c t) (f i).1).base := by
    have h := Scheme.Pullback.range_fst (pullback.snd c t) (f i).1
    have hy' : y ∈ (pullback.snd c t).base ⁻¹' Set.range (f i).1.base := ⟨z, hz⟩
    rw [← h] at hy'
    exact hy'
  obtain ⟨w, hw⟩ := hy
  refine ⟨H.isoPullback.inv.base w, ?_⟩
  rw [← hw, ← H.isoPullback_inv_fst]
  rfl

section MODsec

/-- The scheme-module pseudofunctor with the adjunction data forgotten. -/
abbrev MOD : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

theorem modMap_toFunctor {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ((MOD).map g.op.toLoc).toFunctor = Scheme.Modules.pullback g := rfl

theorem modMapComp'_eq_mapComp_app {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u : a ⟶ b) (v : b ⟶ d)
    (M : (MOD).obj a) :
    ((MOD).mapComp' u v (u ≫ v) rfl).hom.toNatTrans.app M
        = ((MOD).mapComp u v).hom.toNatTrans.app M := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem modMapComp'_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules)
    (fg : X ⟶ Z)
    (h : f ≫ g = fg) :
    ((MOD).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app L =
      (Scheme.Modules.pullbackCongr h.symm).hom.app L
        ≫ (Scheme.Modules.pullbackComp f g).inv.app L := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  exact modMapComp'_eq_mapComp_app g.op.toLoc f.op.toLoc L

theorem modMapComp'_inv_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules)
    (fg : X ⟶ Z)
    (h : f ≫ g = fg) :
    ((MOD).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app L =
      (Scheme.Modules.pullbackComp f g).hom.app L ≫ (Scheme.Modules.pullbackCongr h).hom.app L := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id]
  have h2 :
      ((MOD).mapComp' g.op.toLoc f.op.toLoc (g.op.toLoc ≫ f.op.toLoc) rfl).inv.toNatTrans.app L
        =
      ((MOD).mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app L := by
    rw [Pseudofunctor.mapComp'_eq_mapComp]
  exact h2

/-- The canonical transition morphism on a chosen overlap. -/
def transHom₂ {X₁ X₂ S : Scheme.{u}} (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S) (cp : ChosenPullback q₁ q₂)
    (L : S.Modules) :
    ((MOD).map cp.p₁.op.toLoc).toFunctor.obj (((MOD).map q₁.op.toLoc).toFunctor.obj L) ⟶
      ((MOD).map cp.p₂.op.toLoc).toFunctor.obj (((MOD).map q₂.op.toLoc).toFunctor.obj L) :=
  _root_.AlgebraicCurves.Geometry.Sheaves.DescentComparison.canonicalTransition
    q₁ q₂ cp.p cp.p₁ cp.p₂ cp.hp₁ cp.hp₂ L

theorem transHom₂_eq_fourfold {X₁ X₂ S : Scheme.{u}}
    (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S) (cp : ChosenPullback q₁ q₂) (L : S.Modules) :
    transHom₂ q₁ q₂ cp L =
      (Scheme.Modules.pullbackComp cp.p₁ q₁).hom.app L ≫
      (Scheme.Modules.pullbackCongr cp.hp₁).hom.app L ≫
      (Scheme.Modules.pullbackCongr cp.hp₂.symm).hom.app L ≫
      (Scheme.Modules.pullbackComp cp.p₂ q₂).inv.app L := by
  exact _root_.AlgebraicCurves.Geometry.Sheaves.DescentComparison.canonicalTransition_eq_fourfold
    q₁ q₂ cp.p cp.p₁ cp.p₂ cp.hp₁ cp.hp₂ L

scoped instance isIso_transHom₂ {X₁ X₂ S : Scheme.{u}} (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S)
    (cp : ChosenPullback q₁ q₂)
    (L : S.Modules) : IsIso (transHom₂ q₁ q₂ cp L) := by
  rw [transHom₂_eq_fourfold]
  exact IsIso.comp_isIso' (NatIso.hom_app_isIso _ _) (IsIso.comp_isIso' (NatIso.hom_app_isIso _ _)
    (IsIso.comp_isIso' (NatIso.hom_app_isIso _ _) (NatIso.inv_app_isIso _ _)))

theorem fromDescentData_toDescentData_obj {S : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}}
    (g : ∀ i, X i ⟶ S)
    (sq : ∀ i j, ChosenPullback (g i) (g j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L : S.Modules) (i : ι) :
    ((DescentData'.fromDescentDataFunctor (MOD) sq sq₃).obj (((MOD).toDescentData g).obj L)).obj i =
      ((MOD).map (g i).op.toLoc).toFunctor.obj L := rfl

theorem fromDescentData_toDescentData_hom {S : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}}
    (g : ∀ i, X i ⟶ S)
    (sq : ∀ i j, ChosenPullback (g i) (g j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L : S.Modules) (i j : ι) :
    ((DescentData'.fromDescentDataFunctor (MOD) sq sq₃).obj (((MOD).toDescentData g).obj L)).hom i j
        =
      transHom₂ (g i) (g j) (sq i j) L := by
  dsimp only [transHom₂,
    _root_.AlgebraicCurves.Geometry.Sheaves.DescentComparison.canonicalTransition]
  exact _root_.CategoryTheory.Pseudofunctor.DescentComparison.chosen_canonical_overlap_hom
    MOD g sq sq₃ L i j

end MODsec

attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_transHom₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L


section bridge

variable {c ε}
variable {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
  {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
  {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t)

lemma bc_pr₁_comp : baseChangeSnd c (pr₁ ψ₁ ψ₂) ≫ baseChangeSnd c ψ₁
    = baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)) :=
  baseChangeSnd_comp c _ _

lemma bc_pr₂_comp : baseChangeSnd c (pr₂ ψ₁ ψ₂) ≫ baseChangeSnd c ψ₂
    = baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)) := by
  rw [baseChangeSnd_comp, ← postComp_pr₁_eq_postComp_pr₂]

lemma pr₁_comp_val : (pr₁ ψ₁ ψ₂).1 ≫ ψ₁.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 := rfl

lemma pr₂_comp_val : (pr₂ ψ₁ ψ₂).1 ≫ ψ₂.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 := pullback.condition.symm

variable (c) in
/-- The canonical transition morphism on the base-changed overlap. -/
def rawHom (L : (Limits.pullback c t).Modules) :
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj
        ((Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj L) ⟶
      (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj
          ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj L) :=
  transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) (chosenPullback c ψ₁ ψ₂) L

theorem transHom₂_eq_rawHom (L : (Limits.pullback c t).Modules) :
    transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) (chosenPullback c ψ₁ ψ₂) L
        = rawHom c ψ₁ ψ₂ L := rfl

scoped instance isIso_rawHom (L : (Limits.pullback c t).Modules) : IsIso (rawHom c ψ₁ ψ₂ L) := by
  exact isIso_transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂)
    (chosenPullback c ψ₁ ψ₂) L

/-- The pullback comparison along a leg of the rigidifying-section square. -/
def legIso {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t)
    (ρ : SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t')
    (G : ρ.1 ≫ ψ.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1)
    (L : (Limits.pullback c t).Modules) :
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).obj
            ((Scheme.Modules.pullback (baseChangeSnd c ρ)).obj
              ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L)) ≅
      (Scheme.Modules.pullback (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1).obj
          ((Scheme.Modules.pullback (rigSection c t ε)).obj L) :=
  (RigData.rigNatIso (c := c) (ε := ε) ρ).app
      ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L) ≪≫
    (Scheme.Modules.pullback ρ.1).mapIso ((RigData.rigNatIso (c := c) (ε := ε) ψ).app L) ≪≫
      (Scheme.Modules.τ ρ.1 ψ.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 G).app
          ((Scheme.Modules.pullback (rigSection c t ε)).obj L)

lemma map_map_eq_legIso_conj {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t)
    (ρ : SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t') (G : ρ.1 ≫ ψ.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1)
    (A₁ A₂ : RigData c ε t)
    (φ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A₁.L
        ⟶ (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A₂.L)
    (hφ : RigData.Compat (A₁.pb ψ) (A₂.pb ψ) φ) :
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map
        ((Scheme.Modules.pullback (baseChangeSnd c ρ)).map φ) =
      (legIso ψ₁ ψ₂ ψ ρ G A₁.L).hom ≫ (Scheme.Modules.pullback (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1).map
          (A₁.α.hom ≫ A₂.α.inv) ≫
        (legIso ψ₁ ψ₂ ψ ρ G A₂.L).inv := by
  let Z : Scheme.{u} := Limits.pullback c t
  let Z' : Scheme.{u} := Limits.pullback c t'
  let W : Scheme.{u} := Limits.pullback ψ₁.1 ψ₂.1
  let ZW : Scheme.{u} := Limits.pullback c (strMap₁₂ ψ₁ ψ₂)
  let F : Z.Modules ⥤ T.Modules := Scheme.Modules.pullback (rigSection c t ε)
  let F' : Z'.Modules ⥤ T'.Modules := Scheme.Modules.pullback (rigSection c t' ε)
  let FW : ZW.Modules ⥤ W.Modules := Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)
  let P : Z.Modules ⥤ Z'.Modules := Scheme.Modules.pullback (baseChangeSnd c ψ)
  let P' : Z'.Modules ⥤ ZW.Modules := Scheme.Modules.pullback (baseChangeSnd c ρ)
  let Q : T.Modules ⥤ T'.Modules := Scheme.Modules.pullback ψ.1
  let Q' : T'.Modules ⥤ W.Modules := Scheme.Modules.pullback ρ.1
  let QW : T.Modules ⥤ W.Modules := Scheme.Modules.pullback (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1
  let η : P ⋙ F' ≅ F ⋙ Q := RigData.rigNatIso ψ
  let η' : P' ⋙ FW ≅ F' ⋙ Q' := RigData.rigNatIso ρ
  let θ : Q ⋙ Q' ≅ QW := Scheme.Modules.τ ρ.1 ψ.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 G
  let U : T.Modules := unitModule T
  let U' : T'.Modules := SheafOfModules.unit T'.ringCatSheaf
  let α₁ : F.obj A₁.L ≅ U := A₁.α
  let α₂ : F.obj A₂.L ≅ U := A₂.α
  let u : Q.obj U ≅ U' := Scheme.Modules.pullbackUnitIso ψ.1
  let x₁ : F'.obj (P.obj A₁.L) ≅ Q.obj (F.obj A₁.L) := η.app A₁.L
  let x₂ : F'.obj (P.obj A₂.L) ≅ Q.obj (F.obj A₂.L) := η.app A₂.L
  let y₁ : FW.obj (P'.obj (P.obj A₁.L)) ≅ Q'.obj (F'.obj (P.obj A₁.L)) := η'.app (P.obj A₁.L)
  let y₂ : FW.obj (P'.obj (P.obj A₂.L)) ≅ Q'.obj (F'.obj (P.obj A₂.L)) := η'.app (P.obj A₂.L)
  let z₁ : Q'.obj (Q.obj (F.obj A₁.L)) ≅ QW.obj (F.obj A₁.L) := θ.app (F.obj A₁.L)
  let z₂ : Q'.obj (Q.obj (F.obj A₂.L)) ≅ QW.obj (F.obj A₂.L) := θ.app (F.obj A₂.L)
  let β₁ : F'.obj (P.obj A₁.L) ≅ U' := x₁ ≪≫ Q.mapIso α₁ ≪≫ u
  let β₂ : F'.obj (P.obj A₂.L) ≅ U' := x₂ ≪≫ Q.mapIso α₂ ≪≫ u
  let l₁ : FW.obj (P'.obj (P.obj A₁.L)) ≅ QW.obj (F.obj A₁.L) := y₁ ≪≫ Q'.mapIso x₁ ≪≫ z₁
  let l₂ : FW.obj (P'.obj (P.obj A₂.L)) ≅ QW.obj (F.obj A₂.L) := y₂ ≪≫ Q'.mapIso x₂ ≪≫ z₂
  have hφ₀ : F'.map φ ≫ β₂.hom = β₁.hom := hφ
  have hφ' : F'.map φ = β₁.hom ≫ β₂.inv := (Iso.eq_comp_inv β₂).2 hφ₀
  have hβ : β₁.hom ≫ β₂.inv = x₁.hom ≫ Q.map (α₁.hom ≫ α₂.inv) ≫ x₂.inv := by
    simp only [β₁, β₂, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  have hn₁ : FW.map (P'.map φ) = y₁.hom ≫ Q'.map (F'.map φ) ≫ y₂.inv :=
    (NatIso.naturality_2 η' φ).symm
  have hn₂ : Q'.map (Q.map (α₁.hom ≫ α₂.inv)) =
      z₁.hom ≫ QW.map (α₁.hom ≫ α₂.inv) ≫ z₂.inv :=
    (NatIso.naturality_2 θ (α₁.hom ≫ α₂.inv)).symm
  change FW.map (P'.map φ) = l₁.hom ≫ QW.map (α₁.hom ≫ α₂.inv) ≫ l₂.inv
  have hm : Q'.map (x₁.hom ≫ Q.map (α₁.hom ≫ α₂.inv) ≫ x₂.inv) =
      Q'.map x₁.hom ≫ Q'.map (Q.map (α₁.hom ≫ α₂.inv)) ≫ Q'.map x₂.inv :=
    (Q'.map_comp x₁.hom (Q.map (α₁.hom ≫ α₂.inv) ≫ x₂.inv)).trans
      (congrArg (fun k : Q'.obj (Q.obj (F.obj A₁.L)) ⟶ Q'.obj (F'.obj (P.obj A₂.L)) =>
        Q'.map x₁.hom ≫ k) (Q'.map_comp (Q.map (α₁.hom ≫ α₂.inv)) x₂.inv))
  rw [hn₁, hφ', hβ, hm, hn₂]
  simp only [l₁, l₂, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc]

lemma map_rawHom_comp_legIso (L : (Limits.pullback c t).Modules) :
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map (rawHom c ψ₁ ψ₂ L) ≫
        (legIso ψ₁ ψ₂ ψ₂ (pr₂ ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂) L).hom =
      (legIso ψ₁ ψ₂ ψ₁ (pr₁ ψ₁ ψ₂) (pr₁_comp_val ψ₁ ψ₂) L).hom := by
  dsimp only [rawHom, transHom₂, legIso, RigData.rigNatIso, Scheme.Modules.τ]
  let X : Bool → Scheme.{u} := fun
    | false => Limits.pullback c t₁
    | true => Limits.pullback c t₂
  let X' : Bool → Scheme.{u} := fun
    | false => T₁
    | true => T₂
  let q : ∀ b, X b ⟶ Limits.pullback c t := fun
    | false => baseChangeSnd c ψ₁
    | true => baseChangeSnd c ψ₂
  let f₀ : ∀ b, X' b ⟶ T := fun
    | false => ψ₁.1
    | true => ψ₂.1
  let s₀ : ∀ b, X' b ⟶ X b := fun
    | false => rigSection c t₁ ε
    | true => rigSection c t₂ ε
  let w : ∀ b, s₀ b ≫ q b = f₀ b ≫ rigSection c t ε := fun
    | false => rigSection_baseChangeSnd c ε ψ₁
    | true => rigSection_baseChangeSnd c ε ψ₂
  let cp : ChosenPullback (q false) (q true) := chosenPullback c ψ₁ ψ₂
  let r₁ := (pr₁ ψ₁ ψ₂).1
  let r₂ := (pr₂ ψ₁ ψ₂).1
  let m := (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1
  let s := rigSection c (strMap₁₂ ψ₁ ψ₂) ε
  have G₁ : r₁ ≫ f₀ false = m := pr₁_comp_val ψ₁ ψ₂
  have G₂ : r₂ ≫ f₀ true = m := pr₂_comp_val ψ₁ ψ₂
  have E₁ : s ≫ cp.p₁ = r₁ ≫ s₀ false := rigSection_baseChangeSnd c ε (pr₁ ψ₁ ψ₂)
  have E₂ : s ≫ cp.p₂ = r₂ ≫ s₀ true := rigSection_baseChangeSnd c ε (pr₂ ψ₁ ψ₂)
  have hq : s ≫ cp.p = m ≫ rigSection c t ε :=
    rigSection_baseChangeSnd c ε (postComp ψ₁ (pr₁ ψ₁ ψ₂))
  exact AlgebraicCurves.Geometry.Sheaves.DescentComparison.canonical_pullback_native_leg_relation
    q f₀ (rigSection c t ε) s₀ w L cp.p m s false true cp.p₁ cp.p₂ r₁ r₂
    cp.hp₁ cp.hp₂ G₁ G₂ E₁ E₂ hq

theorem map_comp_rawHom_eq
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (A₁ A₂ : RigData c ε t)
    (φ₁ : (Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₁.L
        ⟶ (Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₂.L)
    (φ₂ : (Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₁.L
        ⟶ (Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₂.L)
    [IsIso φ₁] [IsIso φ₂]
    (h₁ : RigData.Compat (A₁.pb ψ₁) (A₂.pb ψ₁) φ₁) (h₂ : RigData.Compat (A₁.pb ψ₂) (A₂.pb ψ₂) φ₂) :
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).map φ₁ ≫ rawHom c ψ₁ ψ₂ A₂.L =
      rawHom c ψ₁ ψ₂ A₁.L ≫ (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).map φ₂ := by
  have key : (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map
      ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).map φ₁ ≫ rawHom c ψ₁ ψ₂ A₂.L) =
      (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map
      (rawHom c ψ₁ ψ₂ A₁.L ≫ (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).map φ₂) := by
    have H1 := map_rawHom_comp_legIso (c := c) (ε := ε) ψ₁ ψ₂ A₁.L
    have H2 := map_rawHom_comp_legIso (c := c) (ε := ε) ψ₁ ψ₂ A₂.L
    have H2' : (legIso ψ₁ ψ₂ ψ₁ (pr₁ ψ₁ ψ₂) (pr₁_comp_val ψ₁ ψ₂) A₂.L).inv ≫
        (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map (rawHom c ψ₁ ψ₂ A₂.L) =
        (legIso ψ₁ ψ₂ ψ₂ (pr₂ ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂) A₂.L).inv :=
      (Iso.inv_comp_eq _).mpr ((Iso.eq_comp_inv _).mpr H2)
    rw [Functor.map_comp, Functor.map_comp,
      map_map_eq_legIso_conj ψ₁ ψ₂ ψ₁ (pr₁ ψ₁ ψ₂) (pr₁_comp_val ψ₁ ψ₂) A₁ A₂ φ₁ h₁,
      map_map_eq_legIso_conj ψ₁ ψ₂ ψ₂ (pr₂ ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂) A₁ A₂ φ₂ h₂]
    simp only [Category.assoc]
    rw [H2', ← H1, Category.assoc]
  let Φ :
        ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj
          ((Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₁.L) ≅
          (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj
          ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₂.L)) :=
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).mapIso (asIso φ₁) ≪≫
      asIso (rawHom c ψ₁ ψ₂ A₂.L)
  let Ψ :
        ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj
          ((Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₁.L) ≅
          (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj
          ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₂.L)) :=
    asIso (rawHom c ψ₁ ψ₂ A₁.L) ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).mapIso (asIso φ₂)
  let targetRig :
      (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).obj
          ((Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj
            ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₂.L)) ≅
        unitModule (Limits.pullback ψ₁.1 ψ₂.1) :=
    ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α
  have hΨ : (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).mapIso Ψ ≪≫ targetRig =
      (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).mapIso Φ ≪≫ targetRig :=
    Iso.ext (congrArg
      (fun γ :
        (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).obj
            ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj
              ((Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₁.L)) ⟶
          (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).obj
            ((Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj
              ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₂.L)) =>
        γ ≫ targetRig.hom) key.symm)
  have hΦΨ : Φ = Ψ :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq
      R c ε hH0
      (strMap₁₂ ψ₁ ψ₂) ((A₁.pb ψ₁).pb (pr₁ ψ₁ ψ₂)).toRLB ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).toRLB
      ((Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).mapIso Φ ≪≫ targetRig)
      targetRig Φ Ψ rfl hΨ
  exact congrArg Iso.hom hΦΨ

end bridge

attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_transHom₂
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_rawHom
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L


/-- Convert the existing MOD overlap proposition while both schemes and the
chosen Unit-family pullbacks are abstract. The affine reflection owner retains
its original invertibility and affine, flat and surjective inputs. -/
theorem nonempty_iso_of_compatible_pullback_iso_mod
    {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (sq : Unit → Unit → ChosenPullback q q)
    (sq₃ : ∀ i j k : Unit, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L₁ L₂ : Y.Modules)
    (h₁ : Scheme.Modules.IsInvertible L₁) (h₂ : Scheme.Modules.IsInvertible L₂)
    (e : (Scheme.Modules.pullback q).obj L₁ ≅
      (Scheme.Modules.pullback q).obj L₂)
    (comm : ∀ i j : Unit,
      (MOD.map (sq i j).p₁.op.toLoc).toFunctor.map e.hom ≫
          ((DescentData'.fromDescentDataFunctor MOD sq sq₃).obj
            ((MOD.toDescentData (fun _ : Unit => q)).obj L₂)).hom i j =
        ((DescentData'.fromDescentDataFunctor MOD sq sq₃).obj
          ((MOD.toDescentData (fun _ : Unit => q)).obj L₁)).hom i j ≫
            (MOD.map (sq i j).p₂.op.toLoc).toFunctor.map e.hom) :
    Nonempty (L₁ ≅ L₂) := by
  exact NativeDescentReflection.nonempty_iso_of_compatible_pullback_iso
    (Y := Y) (Y' := Y') q sq sq₃ L₁ L₂ h₁ h₂ e comm

section asm_b


variable {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
  (π : SchemeHomOver t' t) [IsAffineHom π.1] [Flat π.1] [Surjective π.1]

scoped instance isAffineHom_q : IsAffineHom (baseChangeSnd c π) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeSnd_snd c π).flip inferInstance
scoped instance flat_q : Flat (baseChangeSnd c π) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeSnd_snd c π).flip inferInstance
scoped instance surjective_q : Surjective (baseChangeSnd c π) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeSnd_snd c π).flip inferInstance

/-- The repeated chosen overlap of the faithfully flat base change. -/
abbrev sq : ∀ (_ _ : Unit), ChosenPullback (baseChangeSnd c π) (baseChangeSnd c π) :=
  fun _ _ => chosenPullback c π π
/-- The corresponding chosen triple overlap. -/
abbrev sq₃ : ∀ (i₁ i₂ i₃ : Unit), ChosenPullback₃ (sq c π i₁ i₂) (sq c π i₂ i₃) (sq c π i₁ i₃) :=
  fun _ _ _ => chosenPullback₃ c π

omit [IsAffineHom π.1] [Flat π.1] [Surjective π.1] in
lemma toDD_hom (L : (Limits.pullback c t).Modules) (i₁ i₂ : Unit) :
    ((DescentData'.fromDescentDataFunctor (MOD)
          (sq c π) (sq₃ c π)).obj
        (((MOD).toDescentData (fun _ : Unit => baseChangeSnd c π)).obj L)).hom i₁ i₂ =
      rawHom c π π L :=
  (fromDescentData_toDescentData_hom (fun _ : Unit => baseChangeSnd c π)
    (sq c π) (sq₃ c π) L i₁ i₂).trans
    (transHom₂_eq_rawHom π π L)

omit [IsAffineHom π.1] [Flat π.1] [Surjective π.1] in
lemma toDD_obj (L : (Limits.pullback c t).Modules) (i : Unit) :
    ((DescentData'.fromDescentDataFunctor (MOD)
          (sq c π) (sq₃ c π)).obj
        (((MOD).toDescentData (fun _ : Unit => baseChangeSnd c π)).obj L)).obj i
        = ((MOD).map (baseChangeSnd c π).op.toLoc).toFunctor.obj L :=
  fromDescentData_toDescentData_obj (fun _ : Unit => baseChangeSnd c π)
    (sq c π) (sq₃ c π) L i


omit [IsAffineHom π.1] [Flat π.1] [Surjective π.1] in
lemma isoMk_comm
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (A₁ A₂ : RigData c ε t)
    (ι' : (Scheme.Modules.pullback (baseChangeSnd c π)).obj A₁.L ≅
      (Scheme.Modules.pullback (baseChangeSnd c π)).obj A₂.L)
    (hι' : RigData.Compat (A₁.pb π) (A₂.pb π) ι'.hom) (i₁ i₂ : Unit) :
    ((MOD).map (sq c π i₁ i₂).p₁.op.toLoc).toFunctor.map ι'.hom ≫
        ((DescentData'.fromDescentDataFunctor (MOD)
          (sq c π) (sq₃ c π)).obj
        (((MOD).toDescentData (fun _ : Unit => baseChangeSnd c π)).obj A₂.L)).hom i₁ i₂ =
      ((DescentData'.fromDescentDataFunctor (MOD)
          (sq c π) (sq₃ c π)).obj
        (((MOD).toDescentData (fun _ : Unit => baseChangeSnd c π)).obj A₁.L)).hom i₁ i₂ ≫
        ((MOD).map (sq c π i₁ i₂).p₂.op.toLoc).toFunctor.map ι'.hom := by
  rw [toDD_hom, toDD_hom]
  dsimp only [sq, toDD_obj, modMap_toFunctor, chosenPullback_p₁, chosenPullback_p₂]
  exact map_comp_rawHom_eq π π hH0 A₁ A₂ ι'.hom ι'.hom hι' hι'

theorem asm_b
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (M₁ M₂ : RigidifiedLineBundle c ε t)
    (h : Nonempty ((M₁.pullbackAlong π).L ≅ (M₂.pullbackAlong π).L)) :
    Nonempty (M₁.L ≅ M₂.L) := by
  let A₁ : RigData c ε t := RigData.ofRLB M₁ M₁.rigidified.some
  let A₂ : RigData c ε t := RigData.ofRLB M₂ M₂.rigidified.some
  obtain ⟨ι', hι'⟩ := RigData.exists_compat_iso (A₁.pb π) (A₂.pb π) h
  let e : (Scheme.Modules.pullback (baseChangeSnd c π)).obj A₁.L ≅
      (Scheme.Modules.pullback (baseChangeSnd c π)).obj A₂.L := ι'
  have he : RigData.Compat (A₁.pb π) (A₂.pb π) e.hom := hι'
  change Nonempty (A₁.L ≅ A₂.L)
  have hc := isoMk_comm c ε π hH0 A₁ A₂ e he
  exact nonempty_iso_of_compatible_pullback_iso_mod
    (Y := Limits.pullback c t) (Y' := Limits.pullback c t')
    (baseChangeSnd c π) (sq c π) (sq₃ c π) A₁.L A₂.L
    A₁.isInvertible A₂.isInvertible e hc

end asm_b

attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_transHom₂
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_rawHom
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isAffineHom_q
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.flat_q
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.surjective_q
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L


end AlgebraicGeometry.RelPicard.DescentAux

attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_transHom₂
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_rawHom
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isAffineHom_q
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.flat_q
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.surjective_q
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L


attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_transHom₂
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_rawHom
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isAffineHom_q
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.flat_q
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.surjective_q
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L


attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_transHom₂
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_rawHom
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isAffineHom_q
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.flat_q
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.surjective_q
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L

end

attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₁_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.pr₂_val
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₁
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p₂
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.chosenPullback_p
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_transHom₂
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isIso_rawHom
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.isAffineHom_q
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.flat_q
attribute [local instance] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.surjective_q
attribute [local simp] AffineIsoDescent.AlgebraicGeometry.RelPicard.DescentAux.RigData.pb_L



open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open AffineIsoDescent.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open AffineIsoDescent.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra


open _root_.JacobianVarieties.Picard.Proofs.AffineIsoDescent in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle
theorem nonempty_iso_of_pullback_of_isAffineHom_of_flat_of_surjective_of_bijective_sections
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (π : SchemeHomOver t' t) [IsAffineHom π.1] [Flat π.1] [Surjective π.1]
    (M₁ M₂ : RigidifiedLineBundle c ε t)
    (h : Nonempty ((M₁.pullbackAlong π).L ≅ (M₂.pullbackAlong π).L)) :
    Nonempty (M₁.L ≅ M₂.L) :=
  AlgebraicGeometry.RelPicard.DescentAux.asm_b c ε π hH0 M₁ M₂ h
end JacobianVarieties.Picard.Proofs.AffineIsoDescent
end ProofImplementation
