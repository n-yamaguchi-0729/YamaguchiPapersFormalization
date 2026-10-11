/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Lean.Elab.Command
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Tactic.Choose
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Irreducible
import SchemeTheory.ProjectiveSpace.Basic
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_algHom_away_apply_ratio_eq

/-!
# exists is Proper surjective is Open Immersion comp eq of is Integral
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Compactification

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
  HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SolCHint

/-- The standard grading on homogeneous coordinates. -/
abbrev grading (A : Type u) [CommRing A] (n : ℕ) := MvPolynomial.homogeneousSubmodule (Fin (n + 1))
  A

/-- Projective space with the chosen coordinates. -/
abbrev PP (A : Type u) [CommRing A] (n : ℕ) : Scheme.{u} := Proj (grading A n)

/-- The standard affine open for the zeroth coordinate. -/
abbrev W (A : Type u) [CommRing A] (n : ℕ) : (PP A n).Opens :=
  Proj.basicOpen (grading A n) (MvPolynomial.X 0)

/-- The inclusion of the zeroth affine chart. -/
abbrev awayι₀ (A : Type u) [CommRing A] (n : ℕ) :
    Spec (.of (Away (grading A n) (MvPolynomial.X (0 : Fin (n + 1))))) ⟶ PP A n :=
  Proj.awayι (grading A n) (MvPolynomial.X 0) (ProjSpace.X_mem_one A n 0) one_pos

section Chart

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

lemma ι_comp_eq_isoSpec_hom (U : X.Opens) (hU : IsAffineOpen U) :
    U.ι ≫ f = hU.isoSpec.hom ≫ Spec.map (f.appLE ⊤ U le_top) ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv := by
  rw [← IsAffineOpen.toSpecΓ_fromSpec hU, Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, IsAffineOpen.isoSpec_hom]

theorem exists_chart [LocallyOfFiniteType f] (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (c : (U : Scheme.{u}) ⟶
        Spec (.of (Away (grading A n) (MvPolynomial.X (0 : Fin (n + 1)))))),
      IsClosedImmersion c ∧ c ≫ awayι₀ A n ≫ ProjSpace.π A n = U.ι ≫ f := by
  let φ₀ : A →+* Γ(X, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U le_top).hom
  let : Algebra A Γ(X, U) := φ₀.toAlgebra
  have hft : Algebra.FiniteType A Γ(X, U) := by
    have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
      f.finiteType_appLE (isAffineOpen_top _) hU le_top
    have h2 : φ₀.FiniteType := by
      change ((f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).FiniteType
      exact h1.comp (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.surjective)
    exact h2
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  let b : Fin (n + 1) → Γ(X, U) := Fin.cases 1 fun i => φ (MvPolynomial.X i)
  obtain ⟨θ, hθ⟩ := ProjSpace.exists_algHom_away_apply_ratio_eq A n 0 b rfl
  have hθsurj : Function.Surjective θ := by
    have hrange : φ.range ≤ θ.range := by
      have : φ.range = (Algebra.adjoin A (Set.range
          (MvPolynomial.X : Fin n → MvPolynomial (Fin n) A))).map φ := by
        rw [MvPolynomial.adjoin_range_X, Algebra.map_top]
      rw [this, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨ProjSpace.ratio A n 0 i.succ, by simpa [b] using hθ i.succ⟩
    intro c
    obtain ⟨p, rfl⟩ := hφ c
    exact hrange ⟨p, rfl⟩
  refine ⟨n, hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ.toRingHom), ?_, ?_⟩
  · have : IsClosedImmersion (Spec.map (CommRingCat.ofHom θ.toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _ hθsurj
    infer_instance
  · rw [ι_comp_eq_isoSpec_hom f U hU, Category.assoc, ProjSpace.awayι_comp_π,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U le_top)]
    congr 1
    exact θ.comp_algebraMap

end Chart

section Setup

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- A finite covering with closed embeddings into projective affine charts. -/
structure ChartData where
  /-- The number of charts. -/
  m : ℕ
  /-- The covering open subsets. -/
  U : Fin m → X.Opens
  /-- Every chart is nonempty. -/
  hne : ∀ k, ((U k : X.Opens) : Set X).Nonempty
  /-- The charts cover the original scheme. -/
  hcov : ⨆ k, U k = ⊤
  /-- The dimensions of the ambient projective spaces. -/
  e : Fin m → ℕ
  /-- The closed embeddings into standard affine charts. -/
  c : ∀ k, ((U k : X.Opens) : Scheme.{u}) ⟶
    Spec (.of (Away (grading A (e k)) (MvPolynomial.X (0 : Fin (e k + 1)))))
  /-- Each chart map is a closed immersion. -/
  hc : ∀ k, IsClosedImmersion (c k)
  /-- The chart embeddings commute with the structure morphisms. -/
  hover : ∀ k, c k ≫ awayι₀ A (e k) ≫ ProjSpace.π A (e k) = (U k).ι ≫ f

attribute [scoped instance] ChartData.hc

theorem nonempty_chartData [LocallyOfFiniteType f] [CompactSpace X] : Nonempty (ChartData f) := by
  let 𝒰 := X.affineCover.finiteSubcover
  let ε := Fintype.equivFin 𝒰.I₀
  let U : Fin (Fintype.card 𝒰.I₀) → X.Opens := fun k => (𝒰.f (ε.symm k)).opensRange
  have hU : ∀ k, IsAffineOpen (U k) := fun k => isAffineOpen_opensRange _
  choose e c hc hover using fun k => exists_chart f (U k) (hU k)
  have hne : ∀ k, ((U k : X.Opens) : Set X).Nonempty := fun k =>
    ⟨(ε.symm k).1, X.affineCover.covers (ε.symm k).1⟩
  have hcov : ⨆ k, U k = ⊤ := by
    rw [← 𝒰.iSup_opensRange]
    exact (Equiv.iSup_comp (g := fun i => (𝒰.f i).opensRange) ε.symm)
  exact ⟨⟨_, U, hne, hcov, e, c, hc, hover⟩⟩

namespace ChartData

variable {f} (D : ChartData f)

/-- The immersion of a covering chart into projective space. -/
def ι (k : Fin D.m) : ((D.U k : X.Opens) : Scheme.{u}) ⟶ PP A (D.e k) := D.c k ≫ awayι₀ A (D.e k)

scoped instance (k : Fin D.m) : IsImmersion (D.ι k) := by unfold ι; infer_instance

lemma ι_comp_π (k : Fin D.m) : D.ι k ≫ ProjSpace.π A (D.e k) = (D.U k).ι ≫ f := by
  rw [ι, Category.assoc, D.hover]

lemma range_ι_subset (k : Fin D.m) : Set.range (D.ι k) ⊆ (W A (D.e k) : Set (PP A (D.e k))) := by
  rw [ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  refine (Set.image_subset_range _ _).trans ?_
  rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]

/-- The product of the projective spaces over the base. -/
abbrev PiS : Scheme.{u} := ProjSpace.prodOver A D.e

/-- The structure morphism of the projective product. -/
abbrev prπ : D.PiS ⟶ Spec (CommRingCat.of A) := ProjSpace.prodOverπ A D.e

/-- The projection to a chosen projective factor. -/
abbrev pr (k : Fin D.m) : D.PiS ⟶ PP A (D.e k) := ProjSpace.prodPr A D.e k

/-- The inverse image of a standard affine chart under a product projection. -/
def Ω (k : Fin D.m) : D.PiS.Opens := D.pr k ⁻¹ᵁ W A (D.e k)

/-- The common open subset of the covering charts. -/
def Uo : X.Opens := Finset.univ.inf D.U

lemma Uo_le (k : Fin D.m) : D.Uo ≤ D.U k := Finset.inf_le (Finset.mem_univ k)

lemma mem_Uo {x : X} : x ∈ D.Uo ↔ ∀ k, x ∈ D.U k := by
  rw [Uo, ← SetLike.mem_coe, Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
  simp

/-- The morphism from the common open subset to the projective product. -/
def g : (D.Uo : Scheme.{u}) ⟶ D.PiS :=
  ProjSpace.prodLift A (D.Uo.ι ≫ f) D.e (fun k => X.homOfLE (D.Uo_le k) ≫ D.ι k)
    (fun k => by rw [Category.assoc, D.ι_comp_π, ← Category.assoc, Scheme.homOfLE_ι])

lemma g_comp_prπ : D.g ≫ D.prπ = D.Uo.ι ≫ f := ProjSpace.prodLift_comp_prodOverπ ..

lemma g_comp_pr (k : Fin D.m) : D.g ≫ D.pr k = X.homOfLE (D.Uo_le k) ≫ D.ι k :=
  ProjSpace.prodLift_comp_prodPr ..

/-- The product of the original scheme and the projective ambient scheme over the base. -/
abbrev XP : Scheme.{u} := pullback f D.prπ

/-- The graph morphism into the ambient product. -/
def ψ : (D.Uo : Scheme.{u}) ⟶ D.XP := pullback.lift D.Uo.ι D.g D.g_comp_prπ.symm

@[scoped simp] lemma ψ_fst : D.ψ ≫ pullback.fst f D.prπ = D.Uo.ι := pullback.lift_fst ..
@[scoped simp] lemma ψ_snd : D.ψ ≫ pullback.snd f D.prπ = D.g := pullback.lift_snd ..

scoped instance : IsImmersion D.ψ := by
  have : IsImmersion (D.ψ ≫ pullback.fst f D.prπ) := by rw [ψ_fst]; infer_instance
  exact IsImmersion.of_comp _ (pullback.fst f D.prπ)

/-- The scheme-theoretic image of the graph morphism. -/
abbrev X' : Scheme.{u} := D.ψ.image

/-- The closed immersion of the scheme-theoretic image. -/
abbrev α : D.X' ⟶ D.XP := D.ψ.imageι

/-- The graph morphism factored through its image. -/
abbrev ψ' : (D.Uo : Scheme.{u}) ⟶ D.X' := D.ψ.toImage

lemma ψ'_α : D.ψ' ≫ D.α = D.ψ := D.ψ.toImage_imageι

/-- The image projection to the original scheme. -/
def π : D.X' ⟶ X := D.α ≫ pullback.fst f D.prπ

/-- The image projection to the projective ambient scheme. -/
def ιι : D.X' ⟶ D.PiS := D.α ≫ pullback.snd f D.prπ

scoped instance : IsProper D.π := by unfold π; infer_instance
scoped instance [IsSeparated f] : IsSeparated D.ιι := by unfold ιι; infer_instance

lemma π_comp_f : D.π ≫ f = D.ιι ≫ D.prπ := by
  simp only [π, ιι, Category.assoc, pullback.condition]

@[scoped simp] lemma ψ'_π : D.ψ' ≫ D.π = D.Uo.ι := by rw [π, ← Category.assoc, ψ'_α, ψ_fst]
@[scoped simp] lemma ψ'_ιι : D.ψ' ≫ D.ιι = D.g := by rw [ιι, ← Category.assoc, ψ'_α, ψ_snd]

/-- The inverse image of an original covering chart. -/
def V (k : Fin D.m) : D.X'.Opens := D.π ⁻¹ᵁ D.U k

end ChartData

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


end Setup

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


section Instances

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

namespace ChartData

omit [IsIntegral X] in
lemma isNoetherian_X (_D : ChartData f) : IsNoetherian X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  {}

scoped instance noetherianSpace_Uo : NoetherianSpace (D.Uo : Scheme.{u}) := by
  have := D.isNoetherian_X
  change NoetherianSpace D.Uo
  exact (inferInstance : NoetherianSpace X).set _

scoped instance compactSpace_XP : CompactSpace D.XP := by
  have := D.isNoetherian_X
  infer_instance

omit [IsNoetherianRing A] [LocallyOfFiniteType f] [QuasiCompact f] in
lemma Uo_nonempty : ((D.Uo : X.Opens) : Set X).Nonempty := by
  classical
  have hirr : IsIrreducible (Set.univ : Set X) := IrreducibleSpace.isIrreducible_univ X
  have := (isIrreducible_iff_sInter.mp hirr) (Finset.univ.image fun k => ((D.U k : X.Opens) : Set
    X))
    (by simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
          forall_apply_eq_imp_iff]
        exact fun k => (D.U k).isOpen)
    (by simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
          forall_apply_eq_imp_iff, Set.univ_inter]
        exact fun k => D.hne k)
  simp only [Set.univ_inter, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.sInter_range] at this
  obtain ⟨x, hx⟩ := this
  exact ⟨x, D.mem_Uo.mpr (by simpa using hx)⟩

scoped instance nonempty_Uo : Nonempty (D.Uo : Scheme.{u}) := by
  obtain ⟨x, hx⟩ := D.Uo_nonempty
  exact ⟨⟨x, hx⟩⟩

scoped instance isIntegral_Uo : IsIntegral (D.Uo : Scheme.{u}) :=
  isIntegral_of_isOpenImmersion D.Uo.ι

scoped instance quasiCompact_ψ : QuasiCompact D.ψ := inferInstance
scoped instance : IsOpenImmersion D.ψ' := inferInstance
scoped instance : IsDominant D.ψ' := inferInstance

scoped instance isReduced_X' : IsReduced D.X' := by
  have : ∀ U' : D.XP.affineOpens,
      _root_.IsReduced ((Γ(D.XP, (U' : D.XP.Opens)) : Type u) ⧸ D.ψ.ker.ideal U') := fun U' => by
    rw [← Ideal.isRadical_iff_quotient_reduced, Scheme.Hom.ker_apply]
    intro x ⟨n, hn⟩
    rw [RingHom.mem_ker, map_pow] at hn
    exact RingHom.mem_ker.mpr (IsReduced.eq_zero _ ⟨n, hn⟩)
  have hcover : ∀ U' : D.XP.affineOpens,
      IsReduced (D.ψ.ker.subschemeCover.openCover.X U') :=
    fun U' => by
    change IsReduced (Spec (.of ((Γ(D.XP, (U' : D.XP.Opens)) : Type u) ⧸ D.ψ.ker.ideal U')))
    infer_instance
  exact (IsReduced.iff_of_openCover _ D.ψ.ker.subschemeCover.openCover).mpr hcover

scoped instance irreducibleSpace_X' : IrreducibleSpace D.X' := by
  have h : IsIrreducible (D.ψ.ker.support : Set D.XP) := by
    rw [Scheme.Hom.support_ker, ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image _ D.ψ.continuous.continuousOn).closure
  exact Subtype.irreducibleSpace h

scoped instance isIntegral_X' : IsIntegral D.X' := isIntegral_of_irreducibleSpace_of_isReduced _

scoped instance compactSpace_X' : CompactSpace D.X' :=
  QuasiCompact.compactSpace_of_compactSpace D.ψ.imageι

end ChartData

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


end Instances

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


section Step1

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

namespace ChartData

/-- The restriction of the image projection to a covering chart. -/
def πk (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ (D.U k : X.Opens) := D.π.resLE (D.U k) (D.V k) le_rfl

omit [IsNoetherianRing A] [IsIntegral X] [LocallyOfFiniteType f]
  [QuasiCompact f] in
lemma πk_ι (k : Fin D.m) : D.πk k ≫ (D.U k).ι = (D.V k).ι ≫ D.π := Scheme.Hom.resLE_comp_ι ..

/-- The chartwise projective map through the original scheme. -/
def ak (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ PP A (D.e k) := D.πk k ≫ D.ι k

/-- The chartwise projective map through the ambient scheme. -/
def bk (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ PP A (D.e k) := (D.V k).ι ≫ D.ιι ≫ D.pr k

omit [IsNoetherianRing A] [IsIntegral X] [LocallyOfFiniteType f]
  [QuasiCompact f] in
lemma range_ψ'_subset_V (k : Fin D.m) : Set.range D.ψ' ⊆ Set.range (D.V k).ι := by
  rintro _ ⟨u, rfl⟩
  rw [Scheme.Opens.range_ι]
  change D.π (D.ψ' u) ∈ D.U k
  rw [← Scheme.Hom.comp_apply, ψ'_π]
  exact D.Uo_le k u.2

/-- The lift from the common open subset to an image chart. -/
def ψk (k : Fin D.m) : (D.Uo : Scheme.{u}) ⟶ (D.V k : Scheme.{u}) :=
  IsOpenImmersion.lift (D.V k).ι D.ψ' (D.range_ψ'_subset_V k)

omit [IsNoetherianRing A] [IsIntegral X] [LocallyOfFiniteType f]
  [QuasiCompact f] in
@[scoped simp] lemma ψk_ι (k : Fin D.m) : D.ψk k ≫ (D.V k).ι = D.ψ' := IsOpenImmersion.lift_fac ..

scoped instance (k : Fin D.m) : IsDominant (D.ψk k) := by
  constructor
  have h : Set.range (D.ψk k) = (D.V k).ι ⁻¹' Set.range D.ψ' := by
    rw [← D.ψk_ι k, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.preimage_image_eq _ (D.V k).ι.isOpenEmbedding.injective]
  rw [DenseRange, h]
  exact D.ψ'.denseRange.preimage (D.V k).ι.isOpenEmbedding.isOpenMap

omit [IsNoetherianRing A] [IsIntegral X] [LocallyOfFiniteType f]
  [QuasiCompact f] in
lemma ψk_πk (k : Fin D.m) : D.ψk k ≫ D.πk k = X.homOfLE (D.Uo_le k) := by
  rw [← cancel_mono (D.U k).ι, Category.assoc, πk_ι, ← Category.assoc, ψk_ι, ψ'_π,
    Scheme.homOfLE_ι]

theorem ak_eq_bk (k : Fin D.m) : D.ak k = D.bk k := by
  refine ext_of_isDominant_of_isSeparated (ProjSpace.π A (D.e k)) ?_ (D.ψk k) ?_
  · rw [ak, bk, Category.assoc, ι_comp_π, ← Category.assoc, πk_ι, Category.assoc, Category.assoc,
      Category.assoc, ProjSpace.prodPr_comp_π, π_comp_f]
  · rw [ak, bk, ← Category.assoc, ψk_πk, ← Category.assoc, ψk_ι, ← Category.assoc, ψ'_ιι, g_comp_pr]

lemma pr_ιι_apply (k : Fin D.m) (x : D.X') (hx : x ∈ D.V k) :
    D.pr k (D.ιι x) = D.ι k (D.πk k ⟨x, hx⟩) := by
  have := congrArg (fun h => h ⟨x, hx⟩) (D.ak_eq_bk k)
  simp only [ak, bk, Scheme.Hom.comp_base, TopCat.coe_comp] at this
  exact this.symm

lemma V_le_preimage_Ω (k : Fin D.m) : D.V k ≤ D.ιι ⁻¹ᵁ D.Ω k := by
  intro x hx
  change D.pr k (D.ιι x) ∈ W A (D.e k)
  rw [D.pr_ιι_apply k x hx]
  exact D.range_ι_subset k ⟨_, rfl⟩

end ChartData

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


end Step1

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


section Step3

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

namespace ChartData

/-- The restriction of the ambient map to its affine chart. -/
def ιΩ (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ (D.Ω k : Scheme.{u}) :=
  D.ιι.resLE (D.Ω k) (D.V k) (D.V_le_preimage_Ω k)

lemma ιΩ_ι (k : Fin D.m) : D.ιΩ k ≫ (D.Ω k).ι = (D.V k).ι ≫ D.ιι := Scheme.Hom.resLE_comp_ι ..

/-- The product of an original chart and an ambient chart over the base. -/
abbrev T (k : Fin D.m) : Scheme.{u} := pullback ((D.U k).ι ≫ f) ((D.Ω k).ι ≫ D.prπ)

/-- The open immersion of the chartwise product. -/
def mT (k : Fin D.m) : D.T k ⟶ D.XP :=
  pullback.map _ _ _ _ (D.U k).ι (D.Ω k).ι (𝟙 _) (by simp) (by simp)

scoped instance (k : Fin D.m) : IsOpenImmersion (D.mT k) := by unfold mT; infer_instance

omit [IsNoetherianRing A] [IsIntegral X] [LocallyOfFiniteType f]
  [QuasiCompact f] in
@[scoped simp] lemma mT_fst (k : Fin D.m) : D.mT k ≫ pullback.fst f D.prπ = pullback.fst _ _ ≫ (D.U
  k).ι :=
  pullback.lift_fst ..
omit [IsNoetherianRing A] [IsIntegral X] [LocallyOfFiniteType f]
  [QuasiCompact f] in
@[scoped simp] lemma mT_snd (k : Fin D.m) : D.mT k ≫ pullback.snd f D.prπ = pullback.snd _ _ ≫ (D.Ω
  k).ι :=
  pullback.lift_snd ..

omit [IsNoetherianRing A] [IsIntegral X] [LocallyOfFiniteType f]
  [QuasiCompact f] in
lemma range_mT (k : Fin D.m) : Set.range (D.mT k) =
    pullback.fst f D.prπ ⁻¹' (D.U k : Set X) ∩ pullback.snd f D.prπ ⁻¹' (D.Ω k : Set D.PiS) := by
  rw [mT, Scheme.Pullback.range_map, Scheme.Opens.range_ι, Scheme.Opens.range_ι]

/-- The map from an image chart to the chartwise product. -/
def tk (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ D.T k :=
  pullback.lift (D.πk k) (D.ιΩ k) (by
    rw [← Category.assoc, πk_ι, ← Category.assoc, ιΩ_ι, Category.assoc, Category.assoc, π_comp_f])

lemma tk_mT (k : Fin D.m) : D.tk k ≫ D.mT k = (D.V k).ι ≫ D.α := by
  apply pullback.hom_ext
  · rw [Category.assoc, mT_fst, ← Category.assoc, tk, pullback.lift_fst, πk_ι, Category.assoc]; rfl
  · rw [Category.assoc, mT_snd, ← Category.assoc, tk, pullback.lift_snd, ιΩ_ι, Category.assoc]; rfl

scoped instance (k : Fin D.m) : IsClosedImmersion (D.tk k) := by
  have : IsImmersion (D.tk k ≫ D.mT k) := by rw [tk_mT]; infer_instance
  have : IsImmersion (D.tk k) := IsImmersion.of_comp _ (D.mT k)
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  have hrange : Set.range (D.tk k) = D.mT k ⁻¹' Set.range D.α := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨v, rfl⟩
      refine ⟨(D.V k).ι v, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, tk_mT]
    · rintro w ⟨x, hx⟩
      have hxV : x ∈ D.V k := by
        change D.π x ∈ D.U k
        have : (D.mT k ≫ pullback.fst f D.prπ) w ∈ (D.U k : Set X) := by
          rw [mT_fst]
          exact ((pullback.fst ((D.U k).ι ≫ f) ((D.Ω k).ι ≫ D.prπ)) w).2
        rw [Scheme.Hom.comp_apply, ← hx] at this
        exact this
      refine ⟨⟨x, hxV⟩, (D.mT k).isOpenEmbedding.injective ?_⟩
      exact (congrArg (fun q : (D.V k : Scheme.{u}) ⟶ D.XP =>
        q (show (D.V k : Scheme.{u}) from ⟨x, hxV⟩)) (D.tk_mT k)).trans hx
  rw [hrange]
  exact IsClosed.preimage (D.mT k).continuous D.α.isClosedEmbedding.isClosed_range

/-- The lift of an ambient affine chart to a standard projective chart. -/
def rk (k : Fin D.m) : (D.Ω k : Scheme.{u}) ⟶
    Spec (.of (Away (grading A (D.e k)) (MvPolynomial.X (0 : Fin (D.e k + 1))))) :=
  IsOpenImmersion.lift (awayι₀ A (D.e k)) ((D.Ω k).ι ≫ D.pr k) (by
    rintro _ ⟨w, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    exact w.2)

omit [IsNoetherianRing A] [IsIntegral X] [LocallyOfFiniteType f]
  [QuasiCompact f] in
@[scoped simp] lemma rk_awayι (k : Fin D.m) : D.rk k ≫ awayι₀ A (D.e k) = (D.Ω k).ι ≫ D.pr k :=
  IsOpenImmersion.lift_fac ..

/-- The pullback of the closed chart embedding. -/
abbrev G (k : Fin D.m) : Scheme.{u} := pullback (D.c k) (D.rk k)

/-- The factorization of the image chart through the closed pullback. -/
def tk' (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ D.G k :=
  pullback.lift (D.πk k) (D.ιΩ k) (by
    rw [← cancel_mono (awayι₀ A (D.e k)), Category.assoc, Category.assoc, rk_awayι,
      ← Category.assoc (D.ιΩ k), ιΩ_ι, Category.assoc]
    exact D.ak_eq_bk k)

/-- The structure morphism of the standard projective chart. -/
abbrev ik (k : Fin D.m) : Spec (.of (Away (grading A (D.e k)) (MvPolynomial.X (0 : Fin (D.e k +
  1)))))
    ⟶ Spec (CommRingCat.of A) := awayι₀ A (D.e k) ≫ ProjSpace.π A (D.e k)

omit [IsNoetherianRing A] [IsIntegral X] [LocallyOfFiniteType f]
  [QuasiCompact f] in
lemma c_ik (k : Fin D.m) : D.c k ≫ D.ik k = (D.U k).ι ≫ f := D.hover k

omit [IsNoetherianRing A] [IsIntegral X] [LocallyOfFiniteType f]
  [QuasiCompact f] in
lemma rk_ik (k : Fin D.m) : D.rk k ≫ D.ik k = (D.Ω k).ι ≫ D.prπ := by
  rw [← Category.assoc, rk_awayι, Category.assoc, ProjSpace.prodPr_comp_π]

lemma tk'_comp (k : Fin D.m) :
    D.tk' k ≫ pullback.mapDesc (D.c k) (D.rk k) (D.ik k) ≫
      (pullback.congrHom (D.c_ik k) (D.rk_ik k)).hom = D.tk k := by
  apply pullback.hom_ext
  · simp only [tk', tk, pullback.mapDesc, Category.assoc, pullback.congrHom_hom,
      pullback.lift_fst, Category.comp_id]
  · simp only [tk', tk, pullback.mapDesc, Category.assoc, pullback.congrHom_hom,
      pullback.lift_snd, Category.comp_id]

scoped instance (k : Fin D.m) : IsClosedImmersion (D.tk' k) := by
  have : IsClosedImmersion (D.tk' k ≫ (pullback.mapDesc (D.c k) (D.rk k) (D.ik k) ≫
      (pullback.congrHom (D.c_ik k) (D.rk_ik k)).hom)) := by
    rw [tk'_comp]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (pullback.mapDesc (D.c k) (D.rk k) (D.ik k) ≫ (pullback.congrHom (D.c_ik k) (D.rk_ik k)).hom)

theorem isClosedImmersion_ιΩ (k : Fin D.m) : IsClosedImmersion (D.ιΩ k) := by
  have : D.ιΩ k = D.tk' k ≫ pullback.snd (D.c k) (D.rk k) := (pullback.lift_snd _ _ _).symm
  rw [this]
  infer_instance

end ChartData

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


end Step3

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


section Step2

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

namespace ChartData

/-- The inverse image of an ambient affine chart. -/
abbrev O (k : Fin D.m) : D.X'.Opens := D.ιι ⁻¹ᵁ D.Ω k

/-- The inclusion of an image chart into an ambient inverse image. -/
abbrev ek (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ (D.O k : Scheme.{u}) := D.X'.homOfLE
  (D.V_le_preimage_Ω k)

omit [IsSeparated f] in
lemma ek_comp (k : Fin D.m) : D.ek k ≫ (D.ιι ∣_ D.Ω k) = D.ιΩ k := rfl

omit [IsNoetherianRing A] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
lemma V_nonempty (k : Fin D.m) : ((D.V k : D.X'.Opens) : Set D.X').Nonempty := by
  obtain ⟨u⟩ := D.nonempty_Uo
  exact ⟨(D.ψk k u).1, (D.ψk k u).2⟩

scoped instance nonempty_O (k : Fin D.m) : Nonempty (D.O k : Scheme.{u}) := by
  obtain ⟨x, hx⟩ := D.V_nonempty k
  exact ⟨⟨x, D.V_le_preimage_Ω k hx⟩⟩

scoped instance isProper_ek (k : Fin D.m) : IsProper (D.ek k) := by
  have : IsClosedImmersion (D.ιΩ k) := D.isClosedImmersion_ιΩ k
  have : IsProper (D.ek k ≫ (D.ιι ∣_ D.Ω k)) := by rw [ek_comp]; infer_instance
  exact IsProper.of_comp _ (D.ιι ∣_ D.Ω k)

theorem V_eq_O (k : Fin D.m) : D.V k = D.O k := by
  refine le_antisymm (D.V_le_preimage_Ω k) ?_
  have hclopen : IsClopen (Set.range (D.ek k)) :=
    ⟨(D.ek k).isClosedMap.isClosed_range, (D.ek k).isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range (D.ek k)).Nonempty := by
    obtain ⟨x, hx⟩ := D.V_nonempty k
    exact ⟨_, ⟨⟨x, hx⟩, rfl⟩⟩
  have huniv := hclopen.eq_univ hne
  intro x hx
  obtain ⟨v, hv⟩ : (⟨x, hx⟩ : (D.O k : Scheme.{u})) ∈ Set.range (D.ek k) := by
    rw [huniv]; trivial
  have h1 : ((D.ek k) v).1 = x := congrArg Subtype.val hv
  have hvx : v.1 = x :=
    (Scheme.homOfLE_apply (D.V_le_preimage_Ω k) v).symm.trans h1
  exact hvx ▸ v.2

end ChartData

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


end Step2

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


section Step4

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

namespace ChartData

scoped instance isClosedImmersion_restrict (k : Fin D.m) : IsClosedImmersion (D.ιι ∣_ D.Ω k) := by
  have : IsClosedImmersion (D.ιΩ k) := D.isClosedImmersion_ιΩ k
  have : Epi (D.ek k).base := by
    rw [TopCat.epi_iff_surjective]
    rintro ⟨x, hx⟩
    have hx' : x ∈ D.V k := by rw [D.V_eq_O k]; exact hx
    exact ⟨⟨x, hx'⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  have : IsIso (D.ek k) := (isIso_iff_isOpenImmersion_and_epi_base _).mpr ⟨inferInstance, ‹_›⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (D.ek k), ek_comp]
  infer_instance

/-- The union of the ambient affine charts. -/
def Ωall : D.PiS.Opens := ⨆ k, D.Ω k

omit [IsSeparated f] in
lemma range_ιι_subset : Set.range D.ιι ⊆ Set.range D.Ωall.ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι, Ωall, SetLike.mem_coe, Opens.mem_iSup]
  have hx : D.π x ∈ (⊤ : X.Opens) := trivial
  rw [← D.hcov, Opens.mem_iSup] at hx
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, D.V_le_preimage_Ω k hk⟩

/-- The factorization of the image map through the union of ambient charts. -/
def ιall : D.X' ⟶ (D.Ωall : Scheme.{u}) := IsOpenImmersion.lift D.Ωall.ι D.ιι D.range_ιι_subset

omit [IsSeparated f] in
@[scoped simp] lemma ιall_ι : D.ιall ≫ D.Ωall.ι = D.ιι := IsOpenImmersion.lift_fac ..

scoped instance isClosedImmersion_ιall : IsClosedImmersion D.ιall := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun k => D.Ωall.ι ⁻¹ᵁ D.Ω k) ?_ fun k => ?_
  · apply le_antisymm le_top
    rintro ⟨w, hw⟩ -
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show w ∈ D.Ωall from hw)
    exact Opens.mem_iSup.mpr ⟨k, hk⟩
  · have h1 : IsClosedImmersion ((D.ιall ≫ D.Ωall.ι) ∣_ D.Ω k) := by rw [ιall_ι]; infer_instance
    rw [morphismRestrict_comp] at h1
    have : IsIso (D.Ωall.ι ∣_ D.Ω k) := by
      have : Epi (D.Ωall.ι ∣_ D.Ω k).base := by
        rw [TopCat.epi_iff_surjective]
        rintro ⟨w, hw⟩
        have hw' : w ∈ D.Ωall := by rw [Ωall, Opens.mem_iSup]; exact ⟨k, hw⟩
        exact ⟨⟨⟨w, hw'⟩, hw⟩, Subtype.ext (morphismRestrict_base_coe _ _ _)⟩
      exact (isIso_iff_isOpenImmersion_and_epi_base _).mpr ⟨inferInstance, ‹_›⟩
    exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ (D.Ωall.ι ∣_ D.Ω
      k)).mp h1

scoped instance isImmersion_ιι : IsImmersion D.ιι := by rw [← ιall_ι]; infer_instance

scoped instance isNoetherian_X' : IsNoetherian D.X' := by
  have := D.isNoetherian_X
  have : IsLocallyNoetherian D.PiS := LocallyOfFiniteType.isLocallyNoetherian D.prπ
  have : IsLocallyNoetherian D.XP := inferInstance
  have : IsLocallyNoetherian D.X' := LocallyOfFiniteType.isLocallyNoetherian D.α
  exact {}

scoped instance quasiCompact_ιι : QuasiCompact D.ιι := inferInstance

scoped instance surjective_π : Surjective D.π := by
  have := D.isNoetherian_X
  constructor
  rw [← Set.range_eq_univ]
  have hdense : Dense ((D.Uo : X.Opens) : Set X) := (D.Uo).isOpen.dense D.Uo_nonempty
  have hsub : ((D.Uo : X.Opens) : Set X) ⊆ Set.range D.π := by
    rw [← Scheme.Opens.range_ι, ← D.ψ'_π, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  have hclosed : IsClosed (Set.range D.π) := D.π.isClosedMap.isClosed_range
  exact Set.eq_univ_of_univ_subset ((hdense.mono hsub).closure_eq ▸ hclosed.closure_subset)

include D in
theorem chow : ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
    IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f :=
  ⟨D.X', D.ιι.image, D.π, D.ιι.toImage, D.ιι.imageι ≫ D.prπ, inferInstance, inferInstance,
    inferInstance, inferInstance, by rw [← Category.assoc, Scheme.Hom.toImage_imageι, π_comp_f]⟩

end ChartData

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


end Step4

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


theorem main {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨D⟩ := nonempty_chartData f
  exact D.chow

end SolCHint

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData",
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


end

open Lean Elab Command in
run_cmd
  for word in ([
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint.ChartData",
      "AlgebraicCurves.Geometry.Schemes.Proofs.Compactification.SolCHint"
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f :=
  SolCHint.main f
end AlgebraicCurves.Geometry.Schemes.Proofs.Compactification
end ProofImplementation

attribute [-instance] AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-simp] AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
