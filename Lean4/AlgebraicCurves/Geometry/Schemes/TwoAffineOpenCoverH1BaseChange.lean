/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.StageHom

/-!
# Two Affine Open Cover H1Base Change
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] {T : Type u} [CommRing T]

/-- A morphism of two affine covers compatible with the indicated map of base rings. -/
structure HomOver (τ : R →+* S) {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {Y : Scheme.{u}} (𝒲 : Y.TwoAffineOpenCover) (c' : Y ⟶ Spec (.of S)) where
  /-- The underlying morphism of schemes. -/
  hom : Y ⟶ X
  /-- Compatibility with the structure morphisms to the affine bases. -/
  comm : hom ≫ c = c' ≫ Spec.map (CommRingCat.ofHom τ)
  /-- The first chart maps into the first chart of the target cover. -/
  U0_le : 𝒲.U0 ≤ hom ⁻¹ᵁ 𝒱.U0
  /-- The second chart maps into the second chart of the target cover. -/
  U1_le : 𝒲.U1 ≤ hom ⁻¹ᵁ 𝒱.U1

namespace HomOver

variable {τ : R →+* S} {X : Scheme.{u}} {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)}
  {Y : Scheme.{u}} {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ Spec (.of S)} (f : HomOver τ 𝒱 c 𝒲 c')

theorem inf_le : 𝒲.U0 ⊓ 𝒲.U1 ≤ f.hom ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1) := by
  rw [Scheme.Hom.preimage_inf]; exact inf_le_inf f.U0_le f.U1_le

theorem appLE_algebraMap {U : X.Opens} {V : Y.Opens} (h : V ≤ f.hom ⁻¹ᵁ U) (r : R) :
    (f.hom.appLE U V h).hom ((algebraOfHom c U).algebraMap r) = (algebraOfHom c' V).algebraMap (τ
      r) := by
  let x : Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv.hom r
  have hcomp : c.appLE ⊤ U le_top ≫ f.hom.appLE U V h =
      (Spec.map (CommRingCat.ofHom τ)).appTop ≫ c'.appLE ⊤ V le_top := by
    have h₁ := Scheme.Hom.appLE_comp_appLE f.hom c ⊤ U V le_top h
    have h₂ : (f.hom ≫ c).appLE ⊤ V le_top =
        (c' ≫ Spec.map (CommRingCat.ofHom τ)).appLE ⊤ V le_top :=
      congrArg (fun φ : Y ⟶ Spec (.of R) => φ.appLE ⊤ V le_top) f.comm
    have h₃ := Scheme.Hom.appLE_comp_appLE c' (Spec.map (CommRingCat.ofHom τ))
      ⊤ ⊤ V le_top le_top
    have happ : (Spec.map (CommRingCat.ofHom τ)).appLE ⊤ ⊤ le_top =
        (Spec.map (CommRingCat.ofHom τ)).appTop :=
      (Scheme.Hom.app_eq_appLE _).symm
    exact h₁.trans (h₂.trans (h₃.symm.trans
      (congrArg (fun ψ => ψ ≫ c'.appLE ⊤ V le_top) happ)))
  have hnat : (Scheme.ΓSpecIso (.of S)).inv.hom (τ r) =
      (Spec.map (CommRingCat.ofHom τ)).appTop.hom x :=
    (CommRingCat.comp_apply (CommRingCat.ofHom τ) (Scheme.ΓSpecIso (.of S)).inv r).symm.trans
      ((DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom τ))) r).trans
        (CommRingCat.comp_apply (Scheme.ΓSpecIso (.of R)).inv
          (Spec.map (CommRingCat.ofHom τ)).appTop r))
  change (f.hom.appLE U V h).hom ((c.appLE ⊤ U le_top).hom x) =
    (c'.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (.of S)).inv.hom (τ r))
  exact (CommRingCat.comp_apply (c.appLE ⊤ U le_top) (f.hom.appLE U V h) x).symm.trans
    ((DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) x).trans
      ((CommRingCat.comp_apply (Spec.map (CommRingCat.ofHom τ)).appTop
        (c'.appLE ⊤ V le_top) x).trans
        (congrArg (c'.appLE ⊤ V le_top).hom hnat.symm)))

/-- The semilinear restriction of sections along the morphism on the specified opens. -/
def sectionsMap {U : X.Opens} {V : Y.Opens} (h : V ≤ f.hom ⁻¹ᵁ U) :
    letI := algebraOfHom c U; letI := algebraOfHom c' V
    Γ(X, U) →ₛₗ[τ] Γ(Y, V) :=
  letI := algebraOfHom c U; letI := algebraOfHom c' V
  { toFun := (f.hom.appLE U V h).hom
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => by
      change (f.hom.appLE U V h).hom ((algebraOfHom c U).algebraMap r * x) =
        (algebraOfHom c' V).algebraMap (τ r) * (f.hom.appLE U V h).hom x
      rw [map_mul, appLE_algebraMap] }

/-- The induced semilinear map on sections over the first chart. -/
def map0 : (𝒱.cover c).A0 →ₛₗ[τ] (𝒲.cover c').A0 := f.sectionsMap f.U0_le

/-- The induced semilinear map on sections over the second chart. -/
def map1 : (𝒱.cover c).A1 →ₛₗ[τ] (𝒲.cover c').A1 := f.sectionsMap f.U1_le

/-- The induced semilinear map on sections over the chart intersection. -/
def map01 : (𝒱.cover c).A01 →ₛₗ[τ] (𝒲.cover c').A01 := f.sectionsMap f.inf_le

theorem map0_apply (x : (𝒱.cover c).A0) : f.map0 x = (f.hom.appLE 𝒱.U0 𝒲.U0 f.U0_le).hom x := rfl
theorem map1_apply (x : (𝒱.cover c).A1) : f.map1 x = (f.hom.appLE 𝒱.U1 𝒲.U1 f.U1_le).hom x := rfl
theorem map01_apply (x : (𝒱.cover c).A01) :
    f.map01 x = (f.hom.appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒲.U0 ⊓ 𝒲.U1) f.inf_le).hom x := rfl

theorem map01_ρ0 (x : (𝒱.cover c).A0) : f.map01 ((𝒱.cover c).ρ0 x) = (𝒲.cover c').ρ0 (f.map0 x)
  := by
  let y : Γ(X, 𝒱.U0) := x
  have hnat : X.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op ≫
      f.hom.appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒲.U0 ⊓ 𝒲.U1) f.inf_le =
      f.hom.appLE 𝒱.U0 𝒲.U0 f.U0_le ≫
        Y.presheaf.map (homOfLE (inf_le_left : 𝒲.U0 ⊓ 𝒲.U1 ≤ 𝒲.U0)).op :=
    (Scheme.Hom.map_appLE f.hom f.inf_le
      (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op).trans
      (Scheme.Hom.appLE_map f.hom f.U0_le
        (homOfLE (inf_le_left : 𝒲.U0 ⊓ 𝒲.U1 ≤ 𝒲.U0)).op).symm
  exact (CommRingCat.comp_apply _ _ y).symm.trans
    ((DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hnat) y).trans
      (CommRingCat.comp_apply _ _ y))

theorem map01_ρ1 (x : (𝒱.cover c).A1) : f.map01 ((𝒱.cover c).ρ1 x) = (𝒲.cover c').ρ1 (f.map1 x)
  := by
  let y : Γ(X, 𝒱.U1) := x
  have hnat : X.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op ≫
      f.hom.appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒲.U0 ⊓ 𝒲.U1) f.inf_le =
      f.hom.appLE 𝒱.U1 𝒲.U1 f.U1_le ≫
        Y.presheaf.map (homOfLE (inf_le_right : 𝒲.U0 ⊓ 𝒲.U1 ≤ 𝒲.U1)).op :=
    (Scheme.Hom.map_appLE f.hom f.inf_le
      (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op).trans
      (Scheme.Hom.appLE_map f.hom f.U1_le
        (homOfLE (inf_le_right : 𝒲.U0 ⊓ 𝒲.U1 ≤ 𝒲.U1)).op).symm
  exact (CommRingCat.comp_apply _ _ y).symm.trans
    ((DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hnat) y).trans
      (CommRingCat.comp_apply _ _ y))

theorem map01_cechDiff (s : (𝒱.cover c).A0 × (𝒱.cover c).A1) :
    f.map01 ((𝒱.structureSheafSections c).cechDiff s) =
      (𝒲.structureSheafSections c').cechDiff (f.map0 s.1, f.map1 s.2) := by
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply, map_sub]
  change f.map01 ((1 : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 s.2) - f.map01 ((𝒱.cover c).ρ0 s.1) =
    (1 : (𝒲.cover c').A01) * (𝒲.cover c').ρ1 (f.map1 s.2) - (𝒲.cover c').ρ0 (f.map0 s.1)
  rw [one_mul, one_mul, map01_ρ0, map01_ρ1]

theorem range_cechDiff_le_comap :
    LinearMap.range (𝒱.structureSheafSections c).cechDiff ≤
      (LinearMap.range (𝒲.structureSheafSections c').cechDiff).comap f.map01 := by
  rintro _ ⟨s, rfl⟩
  rw [Submodule.mem_comap, map01_cechDiff]
  exact LinearMap.mem_range_self _ _

/-- The induced map on the first Cech cohomology of the structure sheaf. -/
def H1map : (𝒱.structureSheafSections c).H1 →ₛₗ[τ] (𝒲.structureSheafSections c').H1 :=
  Submodule.mapQ _ _ f.map01 f.range_cechDiff_le_comap

theorem H1map_mk (y : (𝒱.cover c).A01) :
    f.H1map (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f.map01 y) := rfl

theorem H1map_congr {τ' : R →+* S} {f : HomOver τ 𝒱 c 𝒲 c'} {g : HomOver τ' 𝒱 c 𝒲 c'} (h : f.hom =
  g.hom)
    (x : (𝒱.structureSheafSections c).H1) : f.H1map x = g.H1map x := by
  obtain ⟨fh, _, _, _⟩ := f
  obtain ⟨gh, _, _, _⟩ := g
  cases h
  induction x using Submodule.Quotient.induction_on with
  | H y => rfl

/-- The identity morphism of an affine cover over its base ring. -/
protected def id (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) : HomOver (RingHom.id R) 𝒱 c 𝒱
  c where
  hom := 𝟙 X
  comm := by
    change 𝟙 X ≫ c = c ≫ Spec.map (𝟙 _)
    rw [Spec.map_id, Category.id_comp, Category.comp_id]
  U0_le := le_rfl
  U1_le := le_rfl

theorem id_H1map (x : (𝒱.structureSheafSections c).H1) : (HomOver.id 𝒱 c).H1map x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    have key : (HomOver.id 𝒱 c).hom.appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒱.U0 ⊓ 𝒱.U1) (HomOver.id 𝒱 c).inf_le = 𝟙
      _ := by
      change (𝟙 X : X ⟶ X).app _ ≫ X.presheaf.map _ = _
      rw [Scheme.Hom.id_app]
      erw [Category.id_comp]
      exact (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_id _)
    rw [H1map_mk, map01_apply, key]
    rfl

/-- Composition of morphisms of affine covers over composable base ring maps. -/
def comp {υ : S →+* T} {Z : Scheme.{u}} {𝒳 : Z.TwoAffineOpenCover} {c'' : Z ⟶ Spec (.of T)}
    (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') : HomOver (υ.comp τ) 𝒱 c 𝒳 c'' where
  hom := g.hom ≫ f.hom
  comm := by
    rw [Category.assoc, f.comm, ← Category.assoc, g.comm, Category.assoc, ← Spec.map_comp]
    rfl
  U0_le := g.U0_le.trans
    (by rw [Scheme.Hom.comp_preimage]; exact Scheme.Hom.preimage_mono _ f.U0_le)
  U1_le := g.U1_le.trans
    (by rw [Scheme.Hom.comp_preimage]; exact Scheme.Hom.preimage_mono _ f.U1_le)

theorem comp_H1map {υ : S →+* T} {Z : Scheme.{u}} {𝒳 : Z.TwoAffineOpenCover} {c'' : Z ⟶ Spec (.of
  T)}
    (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') (x : (𝒱.structureSheafSections c).H1) :
    (g.comp f).H1map x = g.H1map (f.H1map x) := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    rw [H1map_mk, H1map_mk, H1map_mk]
    let z : Γ(X, 𝒱.U0 ⊓ 𝒱.U1) := y
    have hcomp : f.hom.appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒲.U0 ⊓ 𝒲.U1) f.inf_le ≫
        g.hom.appLE (𝒲.U0 ⊓ 𝒲.U1) (𝒳.U0 ⊓ 𝒳.U1) g.inf_le =
        (g.comp f).hom.appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒳.U0 ⊓ 𝒳.U1) (g.comp f).inf_le :=
      Scheme.Hom.appLE_comp_appLE g.hom f.hom (𝒱.U0 ⊓ 𝒱.U1)
        (𝒲.U0 ⊓ 𝒲.U1) (𝒳.U0 ⊓ 𝒳.U1) f.inf_le g.inf_le
    have hz := (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) z).symm.trans
      (CommRingCat.comp_apply _ _ z)
    exact congrArg (fun t : (𝒳.structureSheafSections c'').M01 =>
      (Submodule.Quotient.mk t : (𝒳.structureSheafSections c'').H1)) hz

end HomOver

section BaseChange

variable {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
  {A : Type u} [CommRing A] [Algebra R A] {B : Type u} [CommRing B] [Algebra R B]
  {B' : Type u} [CommRing B'] [Algebra R B']

variable (A) in
/-- The projection from the affine cover obtained by base change. -/
def HomOver.baseChange :
    HomOver (algebraMap R A) 𝒱 c (𝒱.pullback c A) (pullback.snd c (specMap R A)) where
  hom := pullback.fst c (specMap R A)
  comm := pullback.condition
  U0_le := le_rfl
  U1_le := le_rfl

/-- The morphism between base changed covers induced by an algebra homomorphism. -/
def HomOver.stage (g : A →ₐ[R] B) :
    HomOver g.toRingHom (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒱.pullback c B) (pullback.snd c (specMap R B)) where
  hom := RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R g)
  comm := pullback.lift_snd _ _ _
  U0_le := (baseChangeSnd_preimage_U0 𝒱 c (RelPicard.LFP.stageHom R g)).ge
  U1_le := (baseChangeSnd_preimage_U1 𝒱 c (RelPicard.LFP.stageHom R g)).ge

variable (A) in
/-- The semilinear map on first Cech cohomology induced by base change. -/
def H1baseChangeMap : (𝒱.structureSheafSections c).H1 →ₛₗ[algebraMap R A]
    ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1 :=
  (HomOver.baseChange 𝒱 c A).H1map

/-- The semilinear map on first Cech cohomology induced by a map of base algebras. -/
def H1stageMap (g : A →ₐ[R] B) :
    ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1 →ₛₗ[g.toRingHom]
      ((𝒱.pullback c B).structureSheafSections (pullback.snd c (specMap R B))).H1 :=
  (HomOver.stage 𝒱 c g).H1map

theorem baseChange_map01_apply (y : (𝒱.cover c).A01) :
    (HomOver.baseChange 𝒱 c A).map01 y = ((pullback.fst c (specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom y
      := by
  rw [HomOver.map01_apply, Scheme.Hom.app_eq_appLE]
  rfl

theorem H1baseChangeMap_mk (y : (𝒱.cover c).A01) :
    H1baseChangeMap 𝒱 c A (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((HomOver.baseChange 𝒱 c A).map01 y) := rfl

theorem stage_map01_apply (g : A →ₐ[R] B) (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R
  A))).A01) :
    (HomOver.stage 𝒱 c g).map01 f =
      ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R g)).appLE
        ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) ((𝒱.pullback c B).U0 ⊓ (𝒱.pullback c B).U1)
        (HomOver.stage 𝒱 c g).inf_le).hom f := rfl

theorem H1stageMap_mk (g : A →ₐ[R] B) (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R
  A))).A01) :
    H1stageMap 𝒱 c g (Submodule.Quotient.mk f) = Submodule.Quotient.mk ((HomOver.stage 𝒱 c
      g).map01 f) := rfl

theorem H1stageMap_H1baseChangeMap (g : A →ₐ[R] B) (x : (𝒱.structureSheafSections c).H1) :
    H1stageMap 𝒱 c g (H1baseChangeMap 𝒱 c A x) = H1baseChangeMap 𝒱 c B x := by
  rw [H1stageMap, H1baseChangeMap, H1baseChangeMap, ← HomOver.comp_H1map]
  exact HomOver.H1map_congr (baseChangeSnd_fst c (RelPicard.LFP.stageHom R g)) x

theorem H1stageMap_id (x : ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R
  A))).H1) :
    H1stageMap 𝒱 c (AlgHom.id R A) x = x := by
  refine (HomOver.H1map_congr (f := HomOver.stage 𝒱 c (AlgHom.id R A))
    (g := HomOver.id (𝒱.pullback c A) (pullback.snd c (specMap R A))) ?_ x).trans
      (HomOver.id_H1map x)
  change RelPicard.baseChangeSnd c _ = 𝟙 _
  rw [← RelPicard.baseChangeSnd_id c (specMap R A)]
  congr 1
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id A)) = 𝟙 _
  exact Spec.map_id _

theorem H1stageMap_comp (g : A →ₐ[R] B) (g' : B →ₐ[R] B')
    (x : ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1) :
    H1stageMap 𝒱 c g' (H1stageMap 𝒱 c g x) = H1stageMap 𝒱 c (g'.comp g) x := by
  rw [H1stageMap, H1stageMap, H1stageMap, ← HomOver.comp_H1map]
  refine HomOver.H1map_congr ?_ x
  change RelPicard.baseChangeSnd c _ ≫ RelPicard.baseChangeSnd c _ = RelPicard.baseChangeSnd c _
  rw [RelPicard.baseChangeSnd_comp]
  congr 1
  apply Subtype.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

end BaseChange

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
