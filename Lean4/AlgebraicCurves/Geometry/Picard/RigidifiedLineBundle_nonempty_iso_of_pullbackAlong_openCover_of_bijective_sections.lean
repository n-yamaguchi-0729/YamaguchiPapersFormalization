/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Geometry.Picard.RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq
import AlgebraicCurves.Geometry.Picard.RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_toDescentData_map_bijective_of_openCover
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app

import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import SchemeTheory.CategoryTheory.DescentComparison
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_canonical_pullback_leg_relation

/-!
# Descent of rigidified line-bundle isomorphisms

Compatible local isomorphisms of rigidified line bundles descend over an open
cover when the structural map has bijective global sections after base change.
Chosen fibre products and section pullback isomorphisms track the transition
morphisms used by the descent comparison.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs
namespace RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections

universe u v

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace OpenCoverAssembly

open CategoryTheory.Pseudofunctor
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_toDescentData_map_bijective_of_openCover
with_weak_namespace AlgebraicGeometry.Scheme.Modules
open HomZar

/-- Descend the two arrows of an actual compatible local isomorphism family.
The cover remains abstract while the existing comparison and hom-descent
owners are combined in their common `Mdl` fibre. -/
theorem nonempty_iso_of_compatible_local_isos
    {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}}
    (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base)
    (sq : ∀ i j, ChosenPullback (g i) (g j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L₁ L₂ : Y.Modules)
    (e : ∀ i, (Scheme.Modules.pullback (g i)).obj L₁ ≅
      (Scheme.Modules.pullback (g i)).obj L₂)
    (comm : ∀ i j,
      (Mdl.map (sq i j).p₁.op.toLoc).toFunctor.map (e i).hom ≫
          ((DescentData'.fromDescentDataFunctor Mdl sq sq₃).obj
            ((Mdl.toDescentData g).obj L₂)).hom i j =
        ((DescentData'.fromDescentDataFunctor Mdl sq sq₃).obj
          ((Mdl.toDescentData g).obj L₁)).hom i j ≫
            (Mdl.map (sq i j).p₂.op.toLoc).toFunctor.map (e j).hom) :
    Nonempty (L₁ ≅ L₂) := by
  let G : Y.Modules ⥤ Mdl.DescentData g := Mdl.toDescentData g
  let ξ : G.obj L₁ ≅ G.obj L₂ :=
    _root_.CategoryTheory.Pseudofunctor.DescentComparison.isoOfChosenOverlap
      Mdl g sq sq₃ L₁ L₂ e comm
  have hbij (L M : Y.Modules) :
      Function.Bijective (G.map : (L ⟶ M) → (G.obj L ⟶ G.obj M)) :=
    main
      g L M hg
  obtain ⟨φ, hφ⟩ := (hbij L₁ L₂).2 ξ.hom
  obtain ⟨ψ, hψ⟩ := (hbij L₂ L₁).2 ξ.inv
  refine ⟨⟨φ, ψ, (hbij L₁ L₁).1 ?_, (hbij L₂ L₂).1 ?_⟩⟩
  · exact (G.map_comp φ ψ).trans
      ((congrArg₂ (fun a b => a ≫ b) hφ hψ).trans
        (ξ.hom_inv_id.trans (G.map_id L₁).symm))
  · exact (G.map_comp ψ φ).trans
      ((congrArg₂ (fun a b => a ≫ b) hψ hφ).trans
        (ξ.inv_hom_id.trans (G.map_id L₂).symm))

end OpenCoverAssembly


namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X₀ X₁ X₂ X₃ : Scheme.{u}}

/-- Identify iterated pullback with pullback along the specified composite morphism. -/
noncomputable def τ (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f ≅ Scheme.Modules.pullback m :=
  pullbackComp f g ≪≫ pullbackCongr e

theorem τ_hom_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).hom.app M = (pullbackComp f g).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e
  simp [τ, pullbackCongr]

theorem τ_inv_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).inv.app M = eqToHom (by rw [e]) ≫ (pullbackComp f g).inv.app M := by
  subst e
  simp [τ, pullbackCongr]

/-- The pullback isomorphism associated with a commutative square of scheme morphisms. -/
noncomputable def sqIso {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) : Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f ≅
        Scheme.Modules.pullback k ⋙ Scheme.Modules.pullback h :=
  pullbackComp f g ≪≫ pullbackCongr e ≪≫ (pullbackComp h k).symm

theorem sqIso_hom_app {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) (M : Z.Modules) :
    (sqIso e).hom.app M = (τ f g (h ≫ k) e).hom.app M ≫ (τ h k (h ≫ k) rfl).inv.app M := by
  simp [sqIso, τ, pullbackCongr]

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
    (sqIso E).hom.app ((Scheme.Modules.pullback b).obj M) ≫ (Scheme.Modules.pullback r).map ((sqIso
        F).hom.app M) ≫
        (τ r p m G).hom.app ((Scheme.Modules.pullback s).obj M) =
      (Scheme.Modules.pullback s₀).map ((τ a b d e).hom.app M) ≫
        (τ s₀ d (m ≫ s) (route_comm a b d e s₀ s₁ s r p m G E F)).hom.app M ≫
          (τ m s (m ≫ s) rfl).inv.app M := by
  exact (AlgebraicGeometry.Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app a b d e s₀ s₁
      s r p m G E F
    (route_comm a b d e s₀ s₁ s r p m G E F) M).trans
    (congrArg (fun k => (Scheme.Modules.pullback s₀).map ((τ a b d e).hom.app M) ≫ k)
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
    (Scheme.Modules.pullback s₀).map ((τ a₁ b₁ d e₁).hom.app M ≫ (τ a₂ b₂ d e₂).inv.app M) ≫
      (sqIso E₂).hom.app ((Scheme.Modules.pullback b₂).obj M) ≫ (Scheme.Modules.pullback r₂).map
          ((sqIso F₂).hom.app M) ≫
        (τ r₂ p₂ m G₂).hom.app ((Scheme.Modules.pullback s).obj M) =
      (sqIso E₁).hom.app ((Scheme.Modules.pullback b₁).obj M) ≫ (Scheme.Modules.pullback r₁).map
          ((sqIso F₁).hom.app M) ≫
        (τ r₁ p₁ m G₁).hom.app ((Scheme.Modules.pullback s).obj M) := by
  have h₁ := route a₁ b₁ d e₁ s₀ s₁ s r₁ p₁ m G₁ E₁ F₁ M
  have h₂ := route a₂ b₂ d e₂ s₀ s₂ s r₂ p₂ m G₂ E₂ F₂ M
  have h₂' := (Iso.inv_comp_eq ((Scheme.Modules.pullback s₀).mapIso ((τ a₂ b₂ d e₂).app M))).mpr h₂
  simp only [Functor.map_comp, Category.assoc]
  exact (congrArg (fun k => (Scheme.Modules.pullback s₀).map ((τ a₁ b₁ d e₁).hom.app M) ≫ k)
      h₂').trans h₁.symm

end Head

section HeadRaw

variable {X X₀' X₁' X₂' : Scheme.{u}}
  (a₁ : X₀' ⟶ X₁') (b₁ : X₁' ⟶ X) (a₂ : X₀' ⟶ X₂') (b₂ : X₂' ⟶ X) (d : X₀' ⟶ X)
  (e₁ : a₁ ≫ b₁ = d) (e₂ : a₂ ≫ b₂ = d)

theorem τ_hom_app_comp_τ_inv_app (M : X.Modules) :
    (τ a₁ b₁ d e₁).hom.app M ≫ (τ a₂ b₂ d e₂).inv.app M =
      (pullbackComp a₁ b₁).hom.app M ≫ (pullbackCongr e₁).hom.app M ≫ (pullbackCongr
          e₂.symm).hom.app M ≫
        (pullbackComp a₂ b₂).inv.app M := by
  subst e₁
  simp [τ, pullbackCongr]

variable {Y Y₀ Y₁ Y₂ : Scheme.{u}}
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s₂ : Y₂ ⟶ X₂') (s : Y ⟶ X)
  (r₁ : Y₀ ⟶ Y₁) (p₁ : Y₁ ⟶ Y) (r₂ : Y₀ ⟶ Y₂) (p₂ : Y₂ ⟶ Y) (m : Y₀ ⟶ Y)
  (G₁ : r₁ ≫ p₁ = m) (G₂ : r₂ ≫ p₂ = m)
  (E₁ : s₀ ≫ a₁ = r₁ ≫ s₁) (F₁ : s₁ ≫ b₁ = p₁ ≫ s) (E₂ : s₀ ≫ a₂ = r₂ ≫ s₂) (F₂ : s₂ ≫ b₂ = p₂ ≫ s)

theorem head' (M : X.Modules) :
    (Scheme.Modules.pullback s₀).map ((pullbackComp a₁ b₁).hom.app M ≫ (pullbackCongr e₁).hom.app M
        ≫
        (pullbackCongr e₂.symm).hom.app M ≫ (pullbackComp a₂ b₂).inv.app M) ≫
      (sqIso E₂).hom.app ((Scheme.Modules.pullback b₂).obj M) ≫ (Scheme.Modules.pullback r₂).map
          ((sqIso F₂).hom.app M) ≫
        (τ r₂ p₂ m G₂).hom.app ((Scheme.Modules.pullback s).obj M) =
      (sqIso E₁).hom.app ((Scheme.Modules.pullback b₁).obj M) ≫ (Scheme.Modules.pullback r₁).map
          ((sqIso F₁).hom.app M) ≫
        (τ r₁ p₁ m G₁).hom.app ((Scheme.Modules.pullback s).obj M) := by
  have h := head a₁ b₁ a₂ b₂ d e₁ e₂ s₀ s₁ s₂ s r₁ p₁ r₂ p₂ m G₁ G₂ E₁ F₁ E₂ F₂ M
  rw [τ_hom_app_comp_τ_inv_app] at h
  exact h

end HeadRaw

end AlgebraicGeometry.Scheme.Modules

noncomputable section
namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
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
    {uS : U ⟶ Spec (CommRingCat.of R)} {vS : V ⟶ Spec (CommRingCat.of R)} {wS : W ⟶ Spec
        (CommRingCat.of R)}
    (u : SchemeHomOver uS x) (v : SchemeHomOver vS x) (a : SchemeHomOver wS uS) (b : SchemeHomOver
        wS vS)
    (h : IsPullback a.1 b.1 u.1 v.1) :
    IsPullback (baseChangeSnd c a) (baseChangeSnd c b) (baseChangeSnd c u) (baseChangeSnd c v) := by
  have hbig : IsPullback (pullback.snd c wS ≫ a.1) (baseChangeSnd c b) u.1 (pullback.snd c vS ≫ v.1)
      :=
    (isPullback_baseChangeSnd_snd c b).flip.paste_horiz h
  have hbig' : IsPullback (baseChangeSnd c a ≫ pullback.snd c uS) (baseChangeSnd c b) u.1
      (baseChangeSnd c v ≫ pullback.snd c x) := by
    rw [show baseChangeSnd c a ≫ pullback.snd c uS = pullback.snd c wS ≫ a.1 from pullback.lift_snd
        _ _ _,
      show baseChangeSnd c v ≫ pullback.snd c x = pullback.snd c vS ≫ v.1 from pullback.lift_snd _ _
          _]
    exact hbig
  refine hbig'.of_right ?_ (isPullback_baseChangeSnd_snd c u).flip
  rw [baseChangeSnd_comp, baseChangeSnd_comp]
  congr 1
  exact Subtype.ext h.w

/-- The structural map from the overlap of two schemes over the affine base. -/
abbrev strMap₁₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec
    (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    pullback ψ₁.1 ψ₂.1 ⟶ Spec (CommRingCat.of R) :=
  pullback.fst ψ₁.1 ψ₂.1 ≫ t₁

/-- The first projection from the overlap, as a morphism over the affine base. -/
def pr₁ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t₁ :=
  ⟨pullback.fst ψ₁.1 ψ₂.1, rfl⟩

/-- The second projection from the overlap, as a morphism over the affine base. -/
def pr₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t₂ :=
  ⟨pullback.snd ψ₁.1 ψ₂.1, by
    have h2 : pullback.snd ψ₁.1 ψ₂.1 ≫ ψ₂.1 ≫ t = pullback.snd ψ₁.1 ψ₂.1 ≫ t₂ := by rw [ψ₂.2]
    have h1 : pullback.fst ψ₁.1 ψ₂.1 ≫ ψ₁.1 ≫ t = pullback.fst ψ₁.1 ψ₂.1 ≫ t₁ := by rw [ψ₁.2]
    change pullback.snd ψ₁.1 ψ₂.1 ≫ t₂ = pullback.fst ψ₁.1 ψ₂.1 ≫ t₁
    rw [← h2, ← h1, ← Category.assoc, ← pullback.condition, Category.assoc]⟩

@[scoped simp] lemma pr₁_val {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶
    Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (pr₁ ψ₁ ψ₂).1 = pullback.fst ψ₁.1 ψ₂.1 := rfl

@[scoped simp] lemma pr₂_val {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶
    Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (pr₂ ψ₁ ψ₂).1 = pullback.snd ψ₁.1 ψ₂.1 := rfl

lemma postComp_pr₁_eq_postComp_pr₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    postComp ψ₁ (pr₁ ψ₁ ψ₂) = postComp ψ₂ (pr₂ ψ₁ ψ₂) :=
  Subtype.ext pullback.condition

/-- The chosen overlap square for the two base changes of the structural morphism. -/
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

/-- The chosen triple-overlap square for three copies of the same base change. -/
def chosenPullback₃ {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec
    (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    ChosenPullback₃ (chosenPullback c ψ ψ) (chosenPullback c ψ ψ) (chosenPullback c ψ ψ) where
  chosenPullback := chosenPullback c (pr₂ ψ ψ) (pr₁ ψ ψ)
  p := baseChangeSnd c (postComp (postComp ψ (pr₁ ψ ψ)) (pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)))
  p₁ := baseChangeSnd c (postComp (pr₁ ψ ψ) (pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)))
  p₃ := baseChangeSnd c (postComp (pr₂ ψ ψ) (pr₂ (pr₂ ψ ψ) (pr₁ ψ ψ)))
  l :=
    { f := baseChangeSnd c
        ⟨pullback.lift ((pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)).1 ≫ (pr₁ ψ ψ).1) ((pr₂ (pr₂ ψ ψ) (pr₁ ψ ψ)).1 ≫
            (pr₂ ψ ψ).1)
          (by
            have hT₂ : pullback.fst ψ.1 ψ.1 ≫ ψ.1 = pullback.snd ψ.1 ψ.1 ≫ ψ.1 := pullback.condition
            have hT₃ : pullback.fst (pullback.snd ψ.1 ψ.1) (pullback.fst ψ.1 ψ.1) ≫ pullback.snd ψ.1
                ψ.1 =
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
          change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ ψ.1 = (pullback.fst _ _ ≫ pullback.fst _
              _) ≫ ψ.1
          rw [pullback.lift_fst_assoc, Category.assoc]
          rfl) }
  hp₁ := by
    change baseChangeSnd c (pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)) ≫ baseChangeSnd c (pr₁ ψ ψ) = _
    erw [baseChangeSnd_comp]
  hp₃ := by
    change baseChangeSnd c (pr₂ (pr₂ ψ ψ) (pr₁ ψ ψ)) ≫ baseChangeSnd c (pr₂ ψ ψ) = _
    erw [baseChangeSnd_comp]

end AlgebraicGeometry.RelPicard.DescentAux
end

noncomputable section
namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace DescentAux
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

with_weak_namespace _root_.AlgebraicCurves.Geometry.Picard.Proofs
with_weak_namespace RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq
with_weak_namespace AlgebraicGeometry.Scheme
open Modules (unitModule) in
with_weak_namespace _root_.AlgebraicCurves.Geometry.Picard.Proofs
with_weak_namespace
  RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
with_weak_namespace AlgebraicGeometry.RelPicard.DescentAux
/-- An invertible module on the base-changed scheme with a specified rigidification along the
    section. -/
structure RigData {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) where
  /-- The module on the base-changed scheme. -/
  L : (Limits.pullback c t).Modules
  /-- The module is invertible. -/
  isInvertible : Scheme.Modules.IsInvertible L
  /-- The rigidification of the module along the base-changed section. -/
  α : (Scheme.Modules.pullback (rigSection c t ε)).obj L ≅ unitModule T

namespace RigData

variable {c ε} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

/-- A module morphism is compatible when it preserves the specified rigidifications. -/
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

lemma Compat.inv {A B : RigData c ε t} {φ : A.L ≅ B.L} (h : Compat A B φ.hom) : Compat B A φ.inv :=
    by
  simp only [Compat] at *
  rw [← h, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]

/-- Transport the module and its rigidification along an isomorphism of modules. -/
def ofIso (A : RigData c ε t) (L' : (Limits.pullback c t).Modules) (e : L' ≅ A.L)
    (hL' : Scheme.Modules.IsInvertible L') : RigData c ε t where
  L := L'
  isInvertible := hL'
  α := (Scheme.Modules.pullback (rigSection c t ε)).mapIso e ≪≫ A.α

lemma ofIso_compat_iff {A B : RigData c ε t} {LA LB : (Limits.pullback c t).Modules} (eA : LA ≅ A.L)
    (eB : LB ≅ B.L)
    (hA : Scheme.Modules.IsInvertible LA) (hB : Scheme.Modules.IsInvertible LB) (φ : LA ⟶ LB) :
    Compat (A.ofIso LA eA hA) (B.ofIso LB eB hB) φ ↔ Compat A B (eA.inv ≫ φ ≫ eB.hom) := by
  simp only [Compat, ofIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  constructor
  · intro h
    rw [h, ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.id_comp]
  · intro h
    rw [← cancel_epi ((Scheme.Modules.pullback (rigSection c t ε)).map eA.inv), ← Category.assoc,
      ← Functor.map_comp] at *
    simpa using h

/-- Identify section pullback after base change with base change after section pullback. -/
def rigNatIso {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    Scheme.Modules.pullback (baseChangeSnd c ψ) ⋙ Scheme.Modules.pullback (rigSection c t' ε) ≅
      Scheme.Modules.pullback (rigSection c t ε) ⋙ Scheme.Modules.pullback ψ.1 :=
  Scheme.Modules.pullbackComp (rigSection c t' ε) (baseChangeSnd c ψ) ≪≫
    Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε ψ) ≪≫
    (Scheme.Modules.pullbackComp ψ.1 (rigSection c t ε)).symm

/-- Pull back the module and its rigidification along a morphism over the base. -/
def pb (A : RigData c ε t) {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver
    t' t) :
    RigData c ε t' where
  L := (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A.L
  isInvertible := A.isInvertible.pullback _
  α := (rigNatIso ψ).app A.L ≪≫ (Scheme.Modules.pullback ψ.1).mapIso A.α ≪≫
      Scheme.Modules.pullbackUnitIso ψ.1

@[scoped simp] lemma pb_L (A : RigData c ε t) {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) : (A.pb ψ).L = (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A.L :=
        rfl

lemma Compat.pb {A B : RigData c ε t} {φ : A.L ⟶ B.L} (h : Compat A B φ) {T' : Scheme.{u}}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    Compat (A.pb ψ) (B.pb ψ) ((Scheme.Modules.pullback (baseChangeSnd c ψ)).map φ) := by
  let F : (Limits.pullback c t).Modules ⥤ T.Modules := Scheme.Modules.pullback (rigSection c t ε)
  let G : (Limits.pullback c t').Modules ⥤ T'.Modules := Scheme.Modules.pullback (rigSection c t' ε)
  let P : (Limits.pullback c t).Modules ⥤ (Limits.pullback c t').Modules :=
    Scheme.Modules.pullback (baseChangeSnd c ψ)
  let Q : T.Modules ⥤ T'.Modules := Scheme.Modules.pullback ψ.1
  let η : P ⋙ G ≅ F ⋙ Q := rigNatIso ψ
  let U : T.Modules := SheafOfModules.unit T.ringCatSheaf
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

end AlgebraicGeometry.RelPicard.DescentAux
end

noncomputable section
namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace DescentAux
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

open NeronModelInfra CategoryTheory.Pseudofunctor

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

namespace RigData
variable {c ε} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

with_weak_namespace _root_.AlgebraicCurves.Geometry.Picard.Proofs
with_weak_namespace RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq
with_weak_namespace AlgebraicGeometry.Scheme
open Modules (unitModule) in
with_weak_namespace _root_.AlgebraicCurves.Geometry.Picard.Proofs
with_weak_namespace
  RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
with_weak_namespace AlgebraicGeometry.RelPicard.DescentAux.RigData
/-- View a rigidified line bundle with a chosen rigidification as explicit rigidification data. -/
def ofRLB (M : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L ≅ unitModule T) :
    RigData c ε t := ⟨M.L, M.isInvertible, α⟩

/-- Forget the chosen rigidification and retain the underlying rigidified line bundle. -/
def toRLB (A : RigData c ε t) : RigidifiedLineBundle c ε t := ⟨A.L, A.isInvertible, ⟨A.α⟩⟩

lemma exists_compat_iso (A B : RigData c ε t) (h : Nonempty (A.L ≅ B.L)) :
    ∃ φ : A.L ≅ B.L, Compat A B φ.hom := by
  obtain ⟨φ, hφ⟩ :=
      AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
    R c ε t A.toRLB B.toRLB A.α B.α h.some
  exact ⟨φ, (compat_iff_mapIso A B φ).mpr hφ⟩

lemma compat_iso_unique
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
          ⊤)))
    (A B : RigData c ε t) (φ ψ : A.L ≅ B.L) (hφ : Compat A B φ.hom) (hψ : Compat A B ψ.hom) : φ = ψ
        :=
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq R c ε
      hH0 t
    A.toRLB B.toRLB A.α B.α φ ψ ((compat_iff_mapIso A B φ).mp hφ) ((compat_iff_mapIso A B ψ).mp hψ)

lemma compat_hom_unique
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
          ⊤)))
    (A B : RigData c ε t) (φ ψ : A.L ⟶ B.L) [IsIso φ] [IsIso ψ] (hφ : Compat A B φ) (hψ : Compat A B
        ψ) :
    φ = ψ :=
  congrArg Iso.hom (compat_iso_unique hH0 A B (asIso φ) (asIso ψ) hφ hψ)

end RigData

@[scoped simp] lemma chosenPullback_p {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (chosenPullback c ψ₁ ψ₂).p = baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)) := rfl

/-- The chosen triple-overlap square for three base changes of the structural morphism. -/
def chosenPullback₃' {T T₁ T₂ T₃ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} {t₃ : T₃ ⟶ Spec
        (CommRingCat.of R)}
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
            have h₁₂ : pullback.fst ψ₁.1 ψ₂.1 ≫ ψ₁.1 = pullback.snd ψ₁.1 ψ₂.1 ≫ ψ₂.1 :=
                pullback.condition
            have h₂₃ : pullback.fst ψ₂.1 ψ₃.1 ≫ ψ₂.1 = pullback.snd ψ₂.1 ψ₃.1 ≫ ψ₃.1 :=
                pullback.condition
            have h' : pullback.fst (pullback.snd ψ₁.1 ψ₂.1) (pullback.fst ψ₂.1 ψ₃.1) ≫ pullback.snd
                ψ₁.1 ψ₂.1 =
                pullback.snd (pullback.snd ψ₁.1 ψ₂.1) (pullback.fst ψ₂.1 ψ₃.1) ≫ pullback.fst ψ₂.1
                    ψ₃.1 :=
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
          change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ ψ₁.1 = (pullback.fst _ _ ≫ pullback.fst _
              _) ≫ ψ₁.1
          rw [pullback.lift_fst_assoc, Category.assoc]
          rfl) }
  hp₁ := by
    change baseChangeSnd c (pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) ≫ baseChangeSnd c (pr₁ ψ₁ ψ₂) = _
    erw [baseChangeSnd_comp]
  hp₃ := by
    change baseChangeSnd c (pr₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) ≫ baseChangeSnd c (pr₂ ψ₂ ψ₃) = _
    erw [baseChangeSnd_comp]

lemma exists_mem_range_baseChangeSnd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {ι : Type u} {U : ι → Scheme.{u}} {uS : ∀ i, U i ⟶ Spec (CommRingCat.of R)} (f : ∀ i,
        SchemeHomOver (uS i) t)
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

with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_toDescentData_map_bijective_of_openCover
with_weak_namespace AlgebraicGeometry.Scheme.Modules
open HomZar in
with_weak_namespace _root_.AlgebraicCurves.Geometry.Picard.Proofs
with_weak_namespace
  RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
with_weak_namespace AlgebraicGeometry.RelPicard.DescentAux
/-- The existing pseudofunctor of scheme module sheaves used for descent. -/
abbrev MOD : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Mdl

theorem modMap_toFunctor {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ((MOD).map g.op.toLoc).toFunctor = Scheme.Modules.pullback g := rfl

theorem modMapComp'_eq_mapComp_app {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u : a ⟶ b) (v : b ⟶ d) (M
    : (MOD).obj a) :
    ((MOD).mapComp' u v (u ≫ v) rfl).hom.toNatTrans.app M = ((MOD).mapComp u v).hom.toNatTrans.app M
        := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem modMapComp'_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (fg : X ⟶
    Z)
    (h : f ≫ g = fg) :
    ((MOD).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app L =
      (Scheme.Modules.pullbackCongr h.symm).hom.app L ≫ (Scheme.Modules.pullbackComp f g).inv.app L
          := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp]
  exact modMapComp'_eq_mapComp_app g.op.toLoc f.op.toLoc L

theorem modMapComp'_inv_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (fg : X ⟶
    Z)
    (h : f ≫ g = fg) :
    ((MOD).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app L =
      (Scheme.Modules.pullbackComp f g).hom.app L ≫ (Scheme.Modules.pullbackCongr h).hom.app L := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
      Category.comp_id]
  have h2 : ((MOD).mapComp' g.op.toLoc f.op.toLoc (g.op.toLoc ≫ f.op.toLoc) rfl).inv.toNatTrans.app
      L =
      ((MOD).mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app L := by
    rw [Pseudofunctor.mapComp'_eq_mapComp]
  exact h2

/-- The canonical transition morphism on a chosen overlap of two pullbacks. -/
def transHom₂ {X₁ X₂ S : Scheme.{u}} (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S) (cp : ChosenPullback q₁ q₂) (L :
    S.Modules) :
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

scoped instance isIso_transHom₂ {X₁ X₂ S : Scheme.{u}} (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S) (cp :
    ChosenPullback q₁ q₂)
    (L : S.Modules) : IsIso (transHom₂ q₁ q₂ cp L) := by
  rw [transHom₂_eq_fourfold]
  exact IsIso.comp_isIso' (NatIso.hom_app_isIso _ _) (IsIso.comp_isIso' (NatIso.hom_app_isIso _ _)
    (IsIso.comp_isIso' (NatIso.hom_app_isIso _ _) (NatIso.inv_app_isIso _ _)))

theorem fromDescentData_toDescentData_obj {S : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}} (g : ∀
    i, X i ⟶ S)
    (sq : ∀ i j, ChosenPullback (g i) (g j)) (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i
        k))
    (L : S.Modules) (i : ι) :
    ((DescentData'.fromDescentDataFunctor (MOD) sq sq₃).obj (((MOD).toDescentData g).obj L)).obj i =
      ((MOD).map (g i).op.toLoc).toFunctor.obj L := rfl

theorem fromDescentData_toDescentData_hom {S : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}} (g : ∀
    i, X i ⟶ S)
    (sq : ∀ i j, ChosenPullback (g i) (g j)) (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i
        k))
    (L : S.Modules) (i j : ι) :
    ((DescentData'.fromDescentDataFunctor (MOD) sq sq₃).obj (((MOD).toDescentData g).obj L)).hom i j
        =
      transHom₂ (g i) (g j) (sq i j) L := by
  dsimp only [transHom₂,
    _root_.AlgebraicCurves.Geometry.Sheaves.DescentComparison.canonicalTransition]
  exact _root_.CategoryTheory.Pseudofunctor.DescentComparison.chosen_canonical_overlap_hom
    MOD g sq sq₃ L i j

end MODsec

section bridge

variable {c ε}
variable {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of
    R)}
  {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t)

lemma bc_pr₁_comp : baseChangeSnd c (pr₁ ψ₁ ψ₂) ≫ baseChangeSnd c ψ₁ = baseChangeSnd c (postComp ψ₁
    (pr₁ ψ₁ ψ₂)) :=
  baseChangeSnd_comp c _ _

lemma bc_pr₂_comp : baseChangeSnd c (pr₂ ψ₁ ψ₂) ≫ baseChangeSnd c ψ₂ = baseChangeSnd c (postComp ψ₁
    (pr₁ ψ₁ ψ₂)) := by
  rw [baseChangeSnd_comp, ← postComp_pr₁_eq_postComp_pr₂]

lemma pr₁_comp_val : (pr₁ ψ₁ ψ₂).1 ≫ ψ₁.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 := rfl

lemma pr₂_comp_val : (pr₂ ψ₁ ψ₂).1 ≫ ψ₂.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 := pullback.condition.symm

variable (c) in
/-- The transition morphism on the chosen overlap of two base changes. -/
def rawHom (L : (Limits.pullback c t).Modules) :
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback
        (baseChangeSnd c ψ₁)).obj L) ⟶
      (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback
          (baseChangeSnd c ψ₂)).obj L) :=
  transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) (chosenPullback c ψ₁ ψ₂) L

theorem transHom₂_eq_rawHom (L : (Limits.pullback c t).Modules) :
    transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) (chosenPullback c ψ₁ ψ₂) L = rawHom c ψ₁ ψ₂
        L := rfl

scoped instance isIso_rawHom (L : (Limits.pullback c t).Modules) : IsIso (rawHom c ψ₁ ψ₂ L) := by
  exact isIso_transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂)
    (chosenPullback c ψ₁ ψ₂) L

/-- Compare the two routes for restricting a module to the section over an overlap. -/
def legIso {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t)
    (ρ : SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t') (G : ρ.1 ≫ ψ.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1) (L :
        (Limits.pullback c t).Modules) :
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).obj
        ((Scheme.Modules.pullback (baseChangeSnd c ρ)).obj ((Scheme.Modules.pullback (baseChangeSnd
            c ψ)).obj L)) ≅
      (Scheme.Modules.pullback (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1).obj ((Scheme.Modules.pullback
          (rigSection c t ε)).obj L) :=
  (RigData.rigNatIso (c := c) (ε := ε) ρ).app ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L)
      ≪≫
    (Scheme.Modules.pullback ρ.1).mapIso ((RigData.rigNatIso (c := c) (ε := ε) ψ).app L) ≪≫
      (Scheme.Modules.τ ρ.1 ψ.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 G).app ((Scheme.Modules.pullback
          (rigSection c t ε)).obj L)

lemma map_map_eq_legIso_conj {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ :
    SchemeHomOver t' t)
    (ρ : SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t') (G : ρ.1 ≫ ψ.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1)
    (A₁ A₂ : RigData c ε t)
    (φ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A₁.L ⟶ (Scheme.Modules.pullback
        (baseChangeSnd c ψ)).obj A₂.L)
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
  let U : T.Modules := SheafOfModules.unit T.ringCatSheaf
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

open _root_.AlgebraicCurves.Geometry.Sheaves.DescentComparison
  (canonical_pullback_native_leg_relation) in
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
  exact canonical_pullback_native_leg_relation
    q f₀ (rigSection c t ε) s₀ w L cp.p m s false true cp.p₁ cp.p₂ r₁ r₂
    cp.hp₁ cp.hp₂ G₁ G₂ E₁ E₂ hq

theorem map_comp_rawHom_eq
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
          ⊤)))
    (A₁ A₂ : RigData c ε t)
    (φ₁ : (Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₁.L ⟶ (Scheme.Modules.pullback
        (baseChangeSnd c ψ₁)).obj A₂.L)
    (φ₂ : (Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₁.L ⟶ (Scheme.Modules.pullback
        (baseChangeSnd c ψ₂)).obj A₂.L)
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
  let Φ : ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback
      (baseChangeSnd c ψ₁)).obj A₁.L) ≅
          (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback
              (baseChangeSnd c ψ₂)).obj A₂.L)) :=
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).mapIso (asIso φ₁) ≪≫ asIso (rawHom c ψ₁
        ψ₂ A₂.L)
  let Ψ : ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback
      (baseChangeSnd c ψ₁)).obj A₁.L) ≅
          (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback
              (baseChangeSnd c ψ₂)).obj A₂.L)) :=
    asIso (rawHom c ψ₁ ψ₂ A₁.L) ≪≫ (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).mapIso
        (asIso φ₂)
  have hΨ : (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).mapIso Ψ ≪≫ ((A₂.pb ψ₂).pb
      (pr₂ ψ₁ ψ₂)).α =
      (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).mapIso Φ ≪≫ ((A₂.pb ψ₂).pb (pr₂ ψ₁
          ψ₂)).α :=
    Iso.ext (by
      first
        | simpa only [Φ, Ψ, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Functor.map_comp,
            Category.assoc] using
            congrArg (· ≫ ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α.hom) key.symm
        | (change (Scheme.Modules.pullback _).map
              (rawHom c ψ₁ ψ₂ A₁.L ≫ (Scheme.Modules.pullback _).map φ₂) ≫ _ =
              (Scheme.Modules.pullback _).map
                ((Scheme.Modules.pullback _).map φ₁ ≫ rawHom c ψ₁ ψ₂ A₂.L) ≫ _
           rw [key]))
  have hΦΨ : Φ = Ψ :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq R c ε
        hH0
      (strMap₁₂ ψ₁ ψ₂) ((A₁.pb ψ₁).pb (pr₁ ψ₁ ψ₂)).toRLB ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).toRLB
      ((Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).mapIso Φ ≪≫ ((A₂.pb ψ₂).pb (pr₂
          ψ₁ ψ₂)).α)
      ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α Φ Ψ rfl hΨ
  exact congrArg Iso.hom hΦΨ

end bridge

section asm_bZ

variable {ι : Type u} {U : ι → Scheme.{u}} (uS : ∀ i, U i ⟶ Spec (CommRingCat.of R))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (f : ∀ i, SchemeHomOver (uS i) t)

scoped instance isOpenImmersion_baseChangeSnd [∀ i, IsOpenImmersion (f i).1] (i : ι) :
    IsOpenImmersion (baseChangeSnd c (f i)) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeSnd_snd c (f i)).flip inferInstance

/-- The chosen pairwise overlap squares for the base-changed open-cover family. -/
abbrev sqZ : ∀ (i j : ι), ChosenPullback (baseChangeSnd c (f i)) (baseChangeSnd c (f j)) :=
  fun i j => chosenPullback c (f i) (f j)
/-- The chosen triple-overlap squares for the base-changed open-cover family. -/
abbrev sq₃Z : ∀ (i j k : ι), ChosenPullback₃ (sqZ c uS t f i j) (sqZ c uS t f j k) (sqZ c uS t f i
    k) :=
  fun i j k => chosenPullback₃' c (f i) (f j) (f k)

lemma toDDZ_hom (L : (Limits.pullback c t).Modules) (i j : ι) :
    ((DescentData'.fromDescentDataFunctor (MOD)
          (sqZ c uS t f) (sq₃Z c uS t f)).obj
        (((MOD).toDescentData (fun i => baseChangeSnd c (f i))).obj L)).hom i j =
      rawHom c (f i) (f j) L :=
  (fromDescentData_toDescentData_hom (fun i => baseChangeSnd c (f i))
    (sqZ c uS t f) (sq₃Z c uS t f) L i j).trans
    (transHom₂_eq_rawHom (f i) (f j) L)

lemma toDDZ_obj (L : (Limits.pullback c t).Modules) (i : ι) :
    ((DescentData'.fromDescentDataFunctor (MOD)
          (sqZ c uS t f) (sq₃Z c uS t f)).obj
        (((MOD).toDescentData (fun i => baseChangeSnd c (f i))).obj L)).obj i = ((MOD).map
            (baseChangeSnd c (f i)).op.toLoc).toFunctor.obj L :=
  fromDescentData_toDescentData_obj (fun i => baseChangeSnd c (f i))
    (sqZ c uS t f) (sq₃Z c uS t f) L i


/-- Convert the existing MOD overlap proposition while the cover is abstract. -/
theorem nonempty_iso_of_compatible_local_isos_mod
    {Y : Scheme.{u}} {κ : Type v} {V : κ → Scheme.{u}}
    (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base)
    (sq : ∀ i j, ChosenPullback (g i) (g j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L₁ L₂ : Y.Modules)
    (e : ∀ i, (Scheme.Modules.pullback (g i)).obj L₁ ≅
      (Scheme.Modules.pullback (g i)).obj L₂)
    (comm : ∀ i j,
      (MOD.map (sq i j).p₁.op.toLoc).toFunctor.map (e i).hom ≫
          ((DescentData'.fromDescentDataFunctor MOD sq sq₃).obj
            ((MOD.toDescentData g).obj L₂)).hom i j =
        ((DescentData'.fromDescentDataFunctor MOD sq sq₃).obj
          ((MOD.toDescentData g).obj L₁)).hom i j ≫
            (MOD.map (sq i j).p₂.op.toLoc).toFunctor.map (e j).hom) :
    Nonempty (L₁ ≅ L₂) := by
  exact OpenCoverAssembly.nonempty_iso_of_compatible_local_isos
    g hg sq sq₃ L₁ L₂ e comm

lemma isoMk_commZ
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
          ⊤)))
    (A₁ A₂ : RigData c ε t)
    (ι' : ∀ i, (Scheme.Modules.pullback (baseChangeSnd c (f i))).obj A₁.L ≅
      (Scheme.Modules.pullback (baseChangeSnd c (f i))).obj A₂.L)
    (hι' : ∀ i, RigData.Compat (A₁.pb (f i)) (A₂.pb (f i)) (ι' i).hom) (i j : ι) :
    ((MOD).map (sqZ c uS t f i j).p₁.op.toLoc).toFunctor.map (ι' i).hom ≫
        ((DescentData'.fromDescentDataFunctor (MOD)
          (sqZ c uS t f) (sq₃Z c uS t f)).obj
        (((MOD).toDescentData (fun i => baseChangeSnd c (f i))).obj A₂.L)).hom i j =
      ((DescentData'.fromDescentDataFunctor (MOD)
          (sqZ c uS t f) (sq₃Z c uS t f)).obj
        (((MOD).toDescentData (fun i => baseChangeSnd c (f i))).obj A₁.L)).hom i j ≫
        ((MOD).map (sqZ c uS t f i j).p₂.op.toLoc).toFunctor.map (ι' j).hom := by
  let e : ∀ k,
      (Scheme.Modules.pullback (baseChangeSnd c (f k))).obj A₁.L ≅
        (Scheme.Modules.pullback (baseChangeSnd c (f k))).obj A₂.L := fun k => ι' k
  have hi : RigData.Compat (A₁.pb (f i)) (A₂.pb (f i)) (e i).hom := hι' i
  have hj : RigData.Compat (A₁.pb (f j)) (A₂.pb (f j)) (e j).hom := hι' j
  have hcomm := map_comp_rawHom_eq (f i) (f j) hH0 A₁ A₂ (e i).hom (e j).hom hi hj
  rw [toDDZ_hom, toDDZ_hom]
  dsimp only [sqZ, toDDZ_obj, modMap_toFunctor, chosenPullback_p₁, chosenPullback_p₂]
  exact hcomm

theorem asm_bZ
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
          ⊤)))
    [∀ i, IsOpenImmersion (f i).1] (hf : ∀ x : T, ∃ i, x ∈ Set.range (f i).1.base)
    (M₁ M₂ : RigidifiedLineBundle c ε t)
    (h : ∀ i, Nonempty ((M₁.pullbackAlong (f i)).L ≅ (M₂.pullbackAlong (f i)).L)) :
    Nonempty (M₁.L ≅ M₂.L) := by
  let A₁ : RigData c ε t := RigData.ofRLB M₁ M₁.rigidified.some
  let A₂ : RigData c ε t := RigData.ofRLB M₂ M₂.rigidified.some
  have hι : ∀ i, ∃ φ : (A₁.pb (f i)).L ≅ (A₂.pb (f i)).L,
      RigData.Compat (A₁.pb (f i)) (A₂.pb (f i)) φ.hom :=
    fun i => RigData.exists_compat_iso (A₁.pb (f i)) (A₂.pb (f i)) (h i)
  choose ι' hι' using hι
  let e : ∀ i,
      (Scheme.Modules.pullback (baseChangeSnd c (f i))).obj A₁.L ≅
        (Scheme.Modules.pullback (baseChangeSnd c (f i))).obj A₂.L := fun i => ι' i
  have he : ∀ i, RigData.Compat (A₁.pb (f i)) (A₂.pb (f i)) (e i).hom := hι'
  change Nonempty (A₁.L ≅ A₂.L)
  exact nonempty_iso_of_compatible_local_isos_mod
    (Y := Limits.pullback c t) (κ := ι) (V := fun i => Limits.pullback c (uS i))
    (fun i => baseChangeSnd c (f i)) (exists_mem_range_baseChangeSnd c f hf)
    (sqZ c uS t f) (sq₃Z c uS t f) A₁.L A₂.L
    e (isoMk_commZ c ε uS t f hH0 A₁ A₂ e he)

end asm_bZ

end AlgebraicGeometry.RelPicard.DescentAux
end

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

with_weak_namespace AlgebraicGeometry.RelPicard
open DescentAux in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle
theorem nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
          ⊤)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {ι : Type u} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ Spec (CommRingCat.of R))
    (f : ∀ i, SchemeHomOver (u i) t) [∀ i, IsOpenImmersion (f i).1]
    (hf : ∀ x : T, ∃ i, x ∈ Set.range (f i).1.base)
    (M₁ M₂ : RigidifiedLineBundle c ε t)
    (h : ∀ i, Nonempty ((M₁.pullbackAlong (f i)).L ≅ (M₂.pullbackAlong (f i)).L)) :
    Nonempty (M₁.L ≅ M₂.L) :=
  asm_bZ c ε u t f hH0 hf M₁ M₂ h
end RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
end AlgebraicCurves.Geometry.Picard.Proofs
end ProofImplementation
