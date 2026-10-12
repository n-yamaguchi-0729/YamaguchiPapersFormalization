/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.CurveCover
import Nyll.JacobianVarieties.Kummer.CurveCoverAction
import Nyll.JacobianVarieties.Kummer.CurveCoverLocalCoordinates
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.JacobianVarieties.Kummer.CurveCoverLocalAction
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.RootFiberTransitivity
import Mathlib.Algebra.Torsor.Defs

/-!
# The actual Kummer covering fiber is a root-of-unity torsor

Local root coordinates on the original normalization identify its geometric
fiber with nonzero roots of an actual unit. The root-scaling formula and
uniqueness of roots up to a root of unity prove that the existing action is
free and transitive. Local roots over a separably closed geometric point also
prove nonemptiness. The covering scheme may be disconnected.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace JacobianVarieties.Kummer

/-- Equal scheme morphisms induce equal restricted section maps. -/
theorem appLE_congr_hom {S N : Scheme.{u}} {g g' : S ⟶ N}
    (hgg : g = g') (W : N.Opens) (V : S.Opens)
    (hg : V ≤ g ⁻¹ᵁ W) (hg' : V ≤ g' ⁻¹ᵁ W) :
    g.appLE W V hg = g'.appLE W V hg' := by
  subst g'
  rfl

/-- Recover a section pullback from its restriction to the whole source. -/
theorem app_of_appLE {S N : Scheme.{u}} (f : S ⟶ N)
    (W : N.Opens) (hf : f ⁻¹ᵁ W = ⊤) (s : Γ(N, W)) :
    f.app W s = S.presheaf.map (homOfLE le_top).op (f.appLE W ⊤ hf.ge s) := by
  change f.app W s = S.presheaf.map (homOfLE le_top).op
    (S.presheaf.map (homOfLE hf.ge).op (f.app W s))
  rw [← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
  have hcomp : (homOfLE hf.ge).op ≫ (homOfLE (le_top : f ⁻¹ᵁ W ≤ ⊤)).op =
      𝟙 (op (f ⁻¹ᵁ W)) := Subsingleton.elim _ _
  rw [hcomp, CategoryTheory.Functor.map_id, CommRingCat.id_apply]

/-- Recover the whole-source restriction from a section pullback. -/
theorem appLE_of_app {S N : Scheme.{u}} (f : S ⟶ N)
    (W : N.Opens) (hf : f ⁻¹ᵁ W = ⊤) (s : Γ(N, W)) (t : Γ(S, ⊤))
    (hs : f.app W s = S.presheaf.map (homOfLE le_top).op t) :
    f.appLE W ⊤ hf.ge s = t := by
  change S.presheaf.map (homOfLE hf.ge).op (f.app W s) = t
  rw [hs, ← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
  have hcomp : (homOfLE (le_top : f ⁻¹ᵁ W ≤ ⊤)).op ≫ (homOfLE hf.ge).op = 𝟙 (op ⊤) :=
    Subsingleton.elim _ _
  rw [hcomp, CategoryTheory.Functor.map_id, CommRingCat.id_apply]

/-- An open containing a field-valued point pulls back to the whole field spectrum. -/
theorem point_preimage_top {Ω : Type u} [Field Ω]
    {X : Scheme.{u}} (ξ : Spec (.of Ω) ⟶ X) (V : X.Opens)
    (hξ : ξ default ∈ V) : ξ ⁻¹ᵁ V = ⊤ := by
  apply top_le_iff.mp
  intro x _hx
  change ξ x ∈ V
  rw [Subsingleton.elim x default]
  exact hξ

/-- Pulling back a base scalar agrees with the composite structural map. -/
theorem appLE_baseScalar {K Ω : Type u} [Field K] [Field Ω]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of K)) (ξ : Spec (.of Ω) ⟶ X)
    (V : X.Opens) (hξ : ξ ⁻¹ᵁ V = ⊤) (a : Γ(Spec (.of K), ⊤)) :
    ξ.appLE V ⊤ hξ.ge (c.appLE ⊤ V le_top a) = (ξ ≫ c).appTop a := by
  have hcomp := Scheme.Hom.appLE_comp_appLE ξ c ⊤ V ⊤ le_top hξ.ge
  have htop : (ξ ≫ c).appLE ⊤ ⊤ le_top = (ξ ≫ c).appTop :=
    (ξ ≫ c).appLE_eq_app
  exact ConcreteCategory.congr_hom (hcomp.trans htop) a

variable {X Y Z : Scheme.{u}} (π : Y ⟶ X) (V : X.Opens)
  (z : Z ⟶ X)

/-- A lift over a morphism pulls back the chosen open to the whole source. -/
theorem rootLift_preimage (hz : z ⁻¹ᵁ V = ⊤) (s : {s : Z ⟶ Y // s ≫ π = z}) :
    s.1 ⁻¹ᵁ (π ⁻¹ᵁ V) = ⊤ :=
  (Scheme.Hom.comp_preimage s.1 π V).symm.trans
    ((congrArg (fun q : Z ⟶ X => q ⁻¹ᵁ V) s.2).trans hz)

/-- The section coordinate of an actual lift over a scheme morphism. -/
def rootLiftCoordinate (hz : z ⁻¹ᵁ V = ⊤) (T : Γ(Y, π ⁻¹ᵁ V))
    (s : {s : Z ⟶ Y // s ≫ π = z}) : Γ(Z, ⊤) :=
  s.1.appLE (π ⁻¹ᵁ V) ⊤ (rootLift_preimage π V z hz s).ge T

/-- The coordinate of a lifted base section is its original pullback. -/
theorem rootLift_app_base (hz : z ⁻¹ᵁ V = ⊤) (v : Γ(X, V))
    (s : {s : Z ⟶ Y // s ≫ π = z}) :
    s.1.appLE (π ⁻¹ᵁ V) ⊤ (rootLift_preimage π V z hz s).ge (π.app V v) =
      z.appLE V ⊤ hz.ge v := by
  let hpre := rootLift_preimage π V z hz s
  have happ : π.app V ≫ s.1.appLE (π ⁻¹ᵁ V) ⊤ hpre.ge = z.appLE V ⊤ hz.ge := by
    have hcomp := Scheme.Hom.appLE_comp_appLE s.1 π V (π ⁻¹ᵁ V) ⊤ le_rfl hpre.ge
    exact (congrArg (fun q => q ≫ s.1.appLE (π ⁻¹ᵁ V) ⊤ hpre.ge)
      π.app_eq_appLE).trans
      (hcomp.trans (appLE_congr_hom s.2 V ⊤ _ hz.ge))
  exact ConcreteCategory.congr_hom happ v

/-- A lift coordinate satisfies the given root equation. -/
theorem rootLiftCoordinate_pow (hz : z ⁻¹ᵁ V = ⊤)
    (T : Γ(Y, π ⁻¹ᵁ V)) (n : ℕ) (v : Γ(X, V))
    (hT : T ^ n = π.app V v) (s : {s : Z ⟶ Y // s ≫ π = z}) :
    rootLiftCoordinate π V z hz T s ^ n = z.appLE V ⊤ hz.ge v := by
  change (s.1.appLE (π ⁻¹ᵁ V) ⊤ (rootLift_preimage π V z hz s).ge T) ^ n = _
  rw [← map_pow, hT]
  exact rootLift_app_base π V z hz v s

/-- Lift coordinates respect a proved scaling map over the base. -/
theorem rootLiftCoordinate_comp (hz : z ⁻¹ᵁ V = ⊤)
    (T : Γ(Y, π ⁻¹ᵁ V)) (e : Y ⟶ Y) (he : e ≫ π = π)
    (hW : π ⁻¹ᵁ V ≤ e ⁻¹ᵁ (π ⁻¹ᵁ V)) (c : Γ(X, V))
    (hscale : e.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) hW T = π.app V c * T)
    (s : {s : Z ⟶ Y // s ≫ π = z}) :
    rootLiftCoordinate π V z hz T
      ⟨s.1 ≫ e, (Category.assoc s.1 e π).trans ((congrArg (s.1 ≫ ·) he).trans s.2)⟩ =
      z.appLE V ⊤ hz.ge c * rootLiftCoordinate π V z hz T s := by
  let hpre := rootLift_preimage π V z hz s
  have happ := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE s.1 e (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) ⊤ hW hpre.ge) T
  change s.1.appLE (π ⁻¹ᵁ V) ⊤ hpre.ge
      (e.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) hW T) = _ at happ
  change (s.1 ≫ e).appLE (π ⁻¹ᵁ V) ⊤ _ T = _
  rw [← happ, hscale, map_mul, rootLift_app_base π V z hz c s]
  rfl

/-- The root-lifting universal property makes coordinates injective. -/
theorem rootLiftCoordinate_injective (hz : z ⁻¹ᵁ V = ⊤)
    (T : Γ(Y, π ⁻¹ᵁ V)) (n : ℕ) (v : Γ(X, V))
    (hT : T ^ n = π.app V v)
    (hlift : ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ n = z.app V v →
      ∃! s : Z ⟶ Y, s ≫ π = z ∧ s.app (π ⁻¹ᵁ V) T =
        Z.presheaf.map (homOfLE le_top).op τ) :
    Function.Injective (rootLiftCoordinate π V z hz T) := by
  intro s t hst
  let τ := rootLiftCoordinate π V z hz T s
  have hs : s.1.app (π ⁻¹ᵁ V) T = Z.presheaf.map (homOfLE le_top).op τ :=
    app_of_appLE s.1 (π ⁻¹ᵁ V) (rootLift_preimage π V z hz s) T
  have ht : t.1.app (π ⁻¹ᵁ V) T = Z.presheaf.map (homOfLE le_top).op τ :=
    (app_of_appLE t.1 (π ⁻¹ᵁ V) (rootLift_preimage π V z hz t) T).trans
      (congrArg (Z.presheaf.map (homOfLE le_top).op) hst.symm)
  have hτ : Z.presheaf.map (homOfLE le_top).op τ ^ n = z.app V v := by
    rw [← map_pow, rootLiftCoordinate_pow π V z hz T n v hT s]
    exact (app_of_appLE z V hz v).symm
  apply Subtype.ext
  exact (hlift τ hτ).unique ⟨s.2, hs⟩ ⟨t.2, ht⟩

/-- The root-lifting universal property realizes each solution coordinate. -/
theorem exists_rootLiftCoordinate (hz : z ⁻¹ᵁ V = ⊤)
    (T : Γ(Y, π ⁻¹ᵁ V)) (n : ℕ) (v : Γ(X, V))
    (hlift : ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ n = z.app V v →
      ∃! s : Z ⟶ Y, s ≫ π = z ∧ s.app (π ⁻¹ᵁ V) T =
        Z.presheaf.map (homOfLE le_top).op τ)
    (τ : Γ(Z, ⊤)) (hτ : τ ^ n = z.appLE V ⊤ hz.ge v) :
    ∃ s : {s : Z ⟶ Y // s ≫ π = z}, rootLiftCoordinate π V z hz T s = τ := by
  have hroot : Z.presheaf.map (homOfLE le_top).op τ ^ n = z.app V v := by
    rw [← map_pow, hτ]
    exact (app_of_appLE z V hz v).symm
  obtain ⟨s, hs, _⟩ := hlift τ hroot
  refine ⟨⟨s, hs.1⟩, ?_⟩
  exact appLE_of_app s (π ⁻¹ᵁ V) (rootLift_preimage π V z hz ⟨s, hs.1⟩) T τ hs.2

/-- Identify an actual geometric fiber with scheme morphisms over its point. -/
def fiberLiftEquiv {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ S) (W : FiniteEtale S) :
    (FiniteEtale.fiber ξ).obj W ≃ {s : Spec (.of Ω) ⟶ W.left // s ≫ W.hom = ξ} :=
  (FiniteEtale.fiberObjEquivHom ξ W).trans
    (NeronModelInfra.schemeHomOverEquivOverHom ξ W.hom).symm

/-- The geometric-fiber identification respects a morphism of covers. -/
theorem fiberLiftEquiv_naturality
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ S) {W W' : FiniteEtale S} (f : W ⟶ W')
    (x : (FiniteEtale.fiber ξ).obj W) :
    (fiberLiftEquiv ξ W' ((FiniteEtale.fiber ξ).map f x)).1 =
      (fiberLiftEquiv ξ W x).1 ≫ f.left := by
  exact (congrArg (fun q => q.left)
    (FiniteEtale.fiberObjEquivHom_naturality ξ f x)).symm

/-- The ground-field homomorphism induced by a geometric point. -/
def pointScalar {K Ω : Type u} [Field K] [Field Ω]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of K)) (ξ : Spec (.of Ω) ⟶ X) : K →+* Ω :=
  (Scheme.ΓSpecIso (.of Ω)).hom.hom.comp
    ((ξ ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)

end JacobianVarieties.Kummer

namespace AlgebraicCurve.CurveModel

open JacobianVarieties.Kummer

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+) (u : Pic0.kummerUnits K F n)
  (hn : IsUnit ((n : ℕ) : K)) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ M.C)

private theorem exists_kummerFiberCoordinate :
    let := M.kummerGeometricRootAction n u hn ξ
    ∃ q : (FiniteEtale.fiber ξ).obj (M.kummerCover n hn u) → Ω,
      Function.Injective q ∧ (∀ x, q x ≠ 0) ∧
      (∀ x y, q x ^ (n : ℕ) = q y ^ (n : ℕ)) ∧
      ∀ (ζ : rootsOfUnity (n : ℕ) K) x,
        q (ζ • x) = pointScalar M.toBase ξ ((ζ : Kˣ) : K) * q x := by
  let := M.kummerGeometricRootAction n u hn ξ
  let f := M.kummerGenericMap n u
  let π := f.fromNormalization
  let W := M.kummerCover n hn u
  obtain ⟨V, _hV, hxV, h, _hh, v, hv, T, hTpow, hTgen, hlift⟩ :=
    M.exists_kummer_root_chart n u hn (ξ default)
  have : Nonempty V := ⟨⟨ξ default, hxV⟩⟩
  have hξ : ξ ⁻¹ᵁ V = ⊤ := point_preimage_top ξ V hxV
  let l := fiberLiftEquiv ξ W
  let c : {s : Spec (.of Ω) ⟶ f.normalization // s ≫ π = ξ} → Γ(Spec (.of Ω), ⊤) :=
    rootLiftCoordinate π V ξ hξ T
  let q : (FiniteEtale.fiber ξ).obj W → Ω :=
    fun x => (Scheme.ΓSpecIso (.of Ω)).hom (c (l x))
  have hpow (x : (FiniteEtale.fiber ξ).obj W) :
      q x ^ (n : ℕ) = (Scheme.ΓSpecIso (.of Ω)).hom (ξ.appLE V ⊤ hξ.ge v) := by
    change ((Scheme.ΓSpecIso (.of Ω)).hom (c (l x))) ^ (n : ℕ) = _
    rw [← map_pow]
    exact congrArg (Scheme.ΓSpecIso (.of Ω)).hom
      (rootLiftCoordinate_pow π V ξ hξ T (n : ℕ) v hTpow (l x))
  have hvΩ : IsUnit ((Scheme.ΓSpecIso (.of Ω)).hom (ξ.appLE V ⊤ hξ.ge v)) :=
    (hv.map (ξ.appLE V ⊤ hξ.ge).hom).map (Scheme.ΓSpecIso (.of Ω)).hom.hom
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply l.injective
    apply rootLiftCoordinate_injective π V ξ hξ T (n : ℕ) v hTpow (hlift _ ξ hξ)
    exact (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.injective hxy
  · intro x hx
    apply hvΩ.ne_zero
    rw [← hpow x, hx, zero_pow n.ne_zero]
  · intro x y
    exact (hpow x).trans (hpow y).symm
  · intro ζ x
    let e := M.kummerNormalizationRootScale n u ζ
    have he : e.hom ≫ π = π :=
      EtaleFundamentalGroups.Inertia.normalizationSourceIso_hom_fromNormalization _ _ _ _
    have hpre : π ⁻¹ᵁ V ≤ e.hom ⁻¹ᵁ (π ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, he]
    have hscale := M.kummerNormalizationRootScale_localRoot n u V h T hTgen ζ
    have hcoord := rootLiftCoordinate_comp π V ξ hξ T e.hom he hpre
      (M.toBase.appLE ⊤ V le_top ((Scheme.ΓSpecIso (.of K)).inv ((ζ : Kˣ) : K)))
      hscale (l x)
    have hl : l (ζ • x) =
        ⟨(l x).1 ≫ e.hom,
          (Category.assoc _ _ _).trans ((congrArg ((l x).1 ≫ ·) he).trans (l x).2)⟩ := by
      apply Subtype.ext
      exact fiberLiftEquiv_naturality ξ (M.kummerCoverRootScale n u hn ζ).hom x
    change (Scheme.ΓSpecIso (.of Ω)).hom (c (l (ζ • x))) = _
    rw [hl]
    change (Scheme.ΓSpecIso (.of Ω)).hom
      (rootLiftCoordinate π V ξ hξ T _) = _
    apply (congrArg (Scheme.ΓSpecIso (.of Ω)).hom hcoord).trans
    apply (map_mul (Scheme.ΓSpecIso (.of Ω)).hom.hom _ _).trans
    exact congrArg (fun a : Γ(Spec (.of Ω), ⊤) =>
      (Scheme.ΓSpecIso (.of Ω)).hom a * q x)
      (appLE_baseScalar M.toBase ξ V hξ ((Scheme.ΓSpecIso (.of K)).inv ((ζ : Kˣ) : K)))

/-- The actual normalized Kummer cover has a nonempty geometric fiber. The
proof constructs a local root over the separably closed geometric point. -/
theorem kummerGeometricFiber_nonempty :
    Nonempty ((FiniteEtale.fiber ξ).obj (M.kummerCover n hn u)) := by
  let f := M.kummerGenericMap n u
  let π := f.fromNormalization
  obtain ⟨V, _hV, hxV, _h, _hh, v, _hv, T, _hTpow, _hTgen, hlift⟩ :=
    M.exists_kummer_root_chart n u hn (ξ default)
  have hξ : ξ ⁻¹ᵁ V = ⊤ := point_preimage_top ξ V hxV
  let ι := pointScalar M.toBase ξ
  have hnΩ : IsUnit ((n : ℕ) : Ω) := by
    simpa only [map_natCast] using hn.map ι
  have : NeZero ((n : ℕ) : Ω) := ⟨hnΩ.ne_zero⟩
  obtain ⟨a, ha⟩ := IsSepClosed.exists_pow_nat_eq
    ((Scheme.ΓSpecIso (.of Ω)).hom (ξ.appLE V ⊤ hξ.ge v)) (n : ℕ)
  let τ : Γ(Spec (.of Ω), ⊤) := (Scheme.ΓSpecIso (.of Ω)).inv a
  have hτ : τ ^ (n : ℕ) = ξ.appLE V ⊤ hξ.ge v := by
    apply (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.injective
    rw [map_pow]
    change ((Scheme.ΓSpecIso (.of Ω)).hom ((Scheme.ΓSpecIso (.of Ω)).inv a)) ^ (n : ℕ) = _
    rw [Iso.inv_hom_id_apply]
    exact ha
  obtain ⟨s, _hs⟩ := exists_rootLiftCoordinate π V ξ hξ T (n : ℕ) v (hlift _ ξ hξ) τ hτ
  exact ⟨(fiberLiftEquiv ξ (M.kummerCover n hn u)).symm s⟩

/-- Root scaling acts freely and transitively on the actual geometric fiber,
including for disconnected normalized Kummer covers. -/
theorem kummerGeometricRootAction_existsUnique [IsSepClosed K]
    (x y : (FiniteEtale.fiber ξ).obj (M.kummerCover n hn u)) :
    let := M.kummerGeometricRootAction n u hn ξ
    ∃! ζ : rootsOfUnity (n : ℕ) K, ζ • x = y := by
  let := M.kummerGeometricRootAction n u hn ξ
  obtain ⟨q, hqinj, hqzero, hqpow, hqscale⟩ := M.exists_kummerFiberCoordinate n u hn ξ
  obtain ⟨ζ, hζ, huniq⟩ := EtaleFundamentalGroups.Kummer.existsUnique_rootScale
    (pointScalar M.toBase ξ) n hn (q x) (q y) (hqzero x) (hqpow x y)
  refine ⟨ζ, hqinj ((hqscale ζ x).trans hζ), ?_⟩
  intro η hη
  apply huniq η
  exact (hqscale η x).symm.trans (congrArg q hη)

/-- The torsor structure uses the already constructed root-scaling action on
the original geometric fiber; no connectedness hypothesis is required. -/
@[instance_reducible]
def kummerGeometricRootTorsor [IsSepClosed K] :
    Torsor (rootsOfUnity (n : ℕ) K)
      ((FiniteEtale.fiber ξ).obj (M.kummerCover n hn u)) := by
  let a := M.kummerGeometricRootAction n u hn ξ
  let d (x y : (FiniteEtale.fiber ξ).obj (M.kummerCover n hn u)) : rootsOfUnity (n : ℕ) K :=
    Classical.choose (M.kummerGeometricRootAction_existsUnique n u hn ξ y x).exists
  have hd (x y : (FiniteEtale.fiber ξ).obj (M.kummerCover n hn u)) : d x y • y = x :=
    Classical.choose_spec (M.kummerGeometricRootAction_existsUnique n u hn ξ y x).exists
  exact {
    toMulAction := a
    sdiv := d
    nonempty := M.kummerGeometricFiber_nonempty n u hn ξ
    sdiv_smul' := hd
    smul_sdiv' := fun ζ x =>
      (M.kummerGeometricRootAction_existsUnique n u hn ξ x (ζ • x)).unique
        (hd (ζ • x) x) rfl }

end AlgebraicCurve.CurveModel
