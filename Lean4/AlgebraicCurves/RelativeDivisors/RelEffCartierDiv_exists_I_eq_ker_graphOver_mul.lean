/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_graphOver_mul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import AlgebraicCurves.RelativeDivisors.Cartier
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Algebra.Module.LocalizedModule.Exact
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import AlgebraicCurves.Foundations.Algebra.Module_rankAtStalk_eq_of_forall_localizedModule_equiv
import AlgebraicCurves.Foundations.Algebra.Module_finitePresentation_of_rankAtStalk_eq

/-!
# Splitting a relative divisor along a section

Splits a relative divisor into the graph of a section and a residual divisor.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_I_eq_ker_graphOver_mul

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ResidualSplitting

section ring

variable {R : Type*} [CommRing R]

open _root_.Ideal

theorem eq_span_singleton_mul_colon (I : Ideal R) (f : R) (h : I ≤ span {f}) :
    I = span {f} * I.colon {f} := by
  refine le_antisymm (fun x hx => ?_) (span_singleton_mul_le_iff.mpr fun z hz => ?_)
  · obtain ⟨a, rfl⟩ := mem_span_singleton'.mp (h hx)
    exact mem_span_singleton_mul.mpr ⟨a, Submodule.mem_colon_singleton.mpr hx, mul_comm f a⟩
  · have := Submodule.mem_colon_singleton.mp hz
    rwa [smul_eq_mul, mul_comm] at this

theorem span_singleton_mul_right_injective_of_mem {f : R} (hf : f ∈ nonZeroDivisors R)
    {J J' : Ideal R} (h : span {f} * J = span {f} * J') : J = J' := by
  suffices key : ∀ {A B : Ideal R}, span {f} * A ≤ span {f} * B → A ≤ B from
    le_antisymm (key h.le) (key h.ge)
  intro A B hAB z hz
  obtain ⟨z', hz', e⟩ := span_singleton_mul_le_span_singleton_mul.mp hAB z hz
  obtain rfl : z = z' := by
    have := sub_eq_zero.mpr e
    rw [← mul_sub] at this
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp hf) _ (by rwa [mul_comm] at this))
  exact hz'

theorem map_colon_of_finite (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization M S] (I : Ideal R) {T : Set R} (hT : T.Finite) :
    (I.colon T).map (algebraMap R S) = (I.map (algebraMap R S)).colon (algebraMap R S '' T) := by
  classical
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) fun y hy => ?_
  · rw [Ideal.mem_comap, Submodule.mem_colon]
    rintro _ ⟨t, ht, rfl⟩
    rw [smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ (Submodule.mem_colon.mp hx t ht)
  · obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective M y
    have key : ∀ t ∈ T, ∃ m ∈ M, m * (t * x) ∈ I := fun t ht => by
      have h1 := Submodule.mem_colon.mp hy (algebraMap R S t) ⟨t, ht, rfl⟩
      rwa [smul_eq_mul, mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul,
        IsLocalization.mk'_mem_map_algebraMap_iff M] at h1
    choose! m hmM hmI using key
    refine (IsLocalization.mk'_mem_map_algebraMap_iff M S _ x s).mpr
      ⟨∏ t ∈ hT.toFinset, m t, prod_mem fun t ht => hmM t (hT.mem_toFinset.mp ht), ?_⟩
    refine Submodule.mem_colon.mpr fun t ht => ?_
    rw [smul_eq_mul, ← Finset.mul_prod_erase _ _ (hT.mem_toFinset.mpr ht)]
    have e : m t * (∏ t' ∈ hT.toFinset.erase t, m t') * x * t =
        (∏ t' ∈ hT.toFinset.erase t, m t') * (m t * (t * x)) := by ring
    rw [e]
    exact I.mul_mem_left _ (hmI t ht)

theorem map_colon_span_of_finite (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization M S] (I : Ideal R) {T : Set R} (hT : T.Finite) :
    (I.colon (Ideal.span T)).map (algebraMap R S) =
      (I.map (algebraMap R S)).colon ((Ideal.span T).map (algebraMap R S)) := by
  rw [Ideal.colon_span, Ideal.map_span, Ideal.colon_span]
  exact map_colon_of_finite M S I hT

theorem ker_mkQ_comp_toSpanSingleton (I : Ideal R) (f : R) :
    LinearMap.ker (I.mkQ ∘ₗ LinearMap.toSpanSingleton R R f) = I.colon {f} := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_colon_singleton]

theorem range_mkQ_comp_toSpanSingleton (I : Ideal R) (f : R) :
    LinearMap.range (I.mkQ ∘ₗ LinearMap.toSpanSingleton R R f) =
      Submodule.map I.mkQ (Ideal.span {f}) := by
  rw [LinearMap.range_comp, ← LinearMap.span_singleton_eq_range]

/-- Multiplication by `f` identifies the quotient by the colon ideal with the image of `(f)` in
  `R/I`. -/
noncomputable def quotColonEquivMapSpan (I : Ideal R) (f : R) :
    (R ⧸ I.colon {f}) ≃ₗ[R] ↥(Submodule.map I.mkQ (Ideal.span {f})) :=
  Submodule.quotEquivOfEq _ _ (ker_mkQ_comp_toSpanSingleton I f).symm ≪≫ₗ
    (I.mkQ ∘ₗ LinearMap.toSpanSingleton R R f).quotKerEquivRange ≪≫ₗ
      LinearEquiv.ofEq _ _ (range_mkQ_comp_toSpanSingleton I f)

end ring

section sheaf

variable {X : Scheme.{u}}

open _root_.AlgebraicGeometry.Scheme


/-- The ideal sheaf whose affine ideals are `I : 𝔞`, using finite generation to commute with
  localization. -/
noncomputable def colonSheaf (I 𝔞 : X.IdealSheafData)
    (h𝔞 : ∀ U : X.affineOpens, (𝔞.ideal U).FG) : X.IdealSheafData where
  ideal U := (I.ideal U).colon (𝔞.ideal U)
  map_ideal_basicOpen U f := by
    obtain ⟨T, hT⟩ := h𝔞 U
    have := U.2.isLocalization_basicOpen f
    have key := map_colon_span_of_finite (Submonoid.powers f) Γ(X, X.basicOpen f)
      (I.ideal U) (T := (T : Set Γ(X, U.1))) T.finite_toSet
    rw [hT] at key
    have halg : algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) =
        (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom := rfl
    rw [halg] at key
    exact key.trans (congrArg₂ (fun (J K : Ideal Γ(X, X.basicOpen f)) => J.colon K)
      (I.map_ideal_basicOpen U f) (𝔞.map_ideal_basicOpen U f))

@[scoped simp] lemma ideal_colonSheaf (I 𝔞 : X.IdealSheafData)
    (h𝔞 : ∀ U : X.affineOpens, (𝔞.ideal U).FG) (U : X.affineOpens) :
    (colonSheaf I 𝔞 h𝔞).ideal U = (I.ideal U).colon (𝔞.ideal U) := rfl

end sheaf

end ResidualSplitting

namespace ResidualSplitting

open _root_.AlgebraicGeometry.Scheme

variable {C S₀ : Scheme.{u}} {c : C ⟶ S₀}
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]
  {T : Scheme.{u}} {t : T ⟶ S₀}

/-- The graph of `a₀` in the fibre product over its fixed base morphism. -/
noncomputable abbrev graphHom (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t) : T ⟶ pullback c t :=
  graphOver c a₀ h₀

theorem exists_affineOpen_ker_graph_eq_span_nonZeroDivisor (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t)
    (x : ↥(pullback c t)) :
    ∃ U : (pullback c t).affineOpens, x ∈ U.1 ∧
      ∃ g ∈ nonZeroDivisors Γ(pullback c t, U.1), (graphHom a₀ h₀).ker.ideal U = Ideal.span {g}
        := by
  have hbase : MorphismProperty.IsStableUnderBaseChange
      (C := Scheme.{u}) (fun {_ _} f => SmoothOfRelativeDimension 1 f) :=
    smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} f => SmoothOfRelativeDimension 1 f)
      (IsPullback.of_hasPullback c t) inferInstance
  obtain ⟨U, u, hxu, g, hg, hU⟩ := Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (graphOver c a₀ h₀) (graphOver_snd c a₀ h₀) x
  exact ⟨(pullback c t).affineBasicOpen u, hxu, g, hg, hU⟩


theorem fg_ideal_of_forall_exists_span {X : Scheme.{u}} (𝔞 : X.IdealSheafData)
    (hloc : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∃ g : Γ(X, V.1), 𝔞.ideal V = Ideal.span {g})
    (U : X.affineOpens) : (𝔞.ideal U).FG := by
  classical
  set s : Set Γ(X, U.1) := {f | (𝔞.ideal (X.affineBasicOpen f)).IsPrincipal} with hs
  have hcov : U.1 ≤ ⨆ f : s, X.basicOpen f.1 := by
    intro x hxU
    obtain ⟨V, hxV, g, hg⟩ := hloc x
    obtain ⟨h₁, hle₁, hx₁⟩ := V.2.exists_basicOpen_le (V := U.1 ⊓ V.1) ⟨x, hxU, hxV⟩ hxV
    obtain ⟨f, hle₂, hx₂⟩ := U.2.exists_basicOpen_le (V := X.basicOpen h₁) ⟨x, hx₁⟩ hxU
    have hf : f ∈ s := by
      have hW₁ : 𝔞.ideal (X.affineBasicOpen h₁) =
          Ideal.span {(X.presheaf.map (homOfLE <| X.basicOpen_le h₁).op).hom g} := by
        rw [← 𝔞.map_ideal_basicOpen V h₁, hg, Ideal.map_span, Set.image_singleton]
      have hWle : (X.affineBasicOpen h₁).1 ≤ U.1 := hle₁.trans inf_le_left
      set f₁ : Γ(X, (X.affineBasicOpen h₁).1) :=
        (X.presheaf.map (homOfLE hWle).op).hom f with hf₁
      have hopen : X.basicOpen f₁ = X.basicOpen f := by
        rw [hf₁, Scheme.basicOpen_res]
        exact inf_eq_right.mpr hle₂
      have heq : X.affineBasicOpen f = X.affineBasicOpen f₁ := by
        exact Subtype.ext hopen.symm
      rw [hs, Set.mem_ofPred_eq, heq, ← 𝔞.map_ideal_basicOpen (X.affineBasicOpen h₁) f₁]
      have hprincipal : (𝔞.ideal (X.affineBasicOpen h₁)).IsPrincipal := by
        rw [hW₁]
        exact ⟨_, rfl⟩
      exact (inferInstance : (Ideal.map
        (X.presheaf.map (homOfLE <| X.basicOpen_le f₁).op).hom
        (𝔞.ideal (X.affineBasicOpen h₁))).IsPrincipal)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hx₂⟩
  have hspan : Ideal.span s = ⊤ := U.2.self_le_iSup_basicOpen_iff.mp hcov
  have : ∀ f : s, IsLocalization.Away f.1 Γ(X, X.basicOpen f.1) :=
    fun f => U.2.isLocalization_basicOpen f.1
  have hfin : Module.Finite Γ(X, U.1) (𝔞.ideal U) := by
    refine Module.Finite.of_localizationSpan' (M := ↥(𝔞.ideal U)) s hspan
      (Rₚ := fun f => Γ(X, X.basicOpen f.1))
      (Mₚ := fun f => ↥((𝔞.ideal U).localized' Γ(X, X.basicOpen f.1)
        (Submonoid.powers f.1) (Algebra.linearMap Γ(X, U.1) Γ(X, X.basicOpen f.1))))
      (fun f => (𝔞.ideal U).toLocalized' Γ(X, X.basicOpen f.1)
        (Submonoid.powers f.1) (Algebra.linearMap Γ(X, U.1) Γ(X, X.basicOpen f.1))) (fun f => ?_)
    have hloc' : (𝔞.ideal U).localized' Γ(X, X.basicOpen f.1)
        (Submonoid.powers f.1) (Algebra.linearMap Γ(X, U.1) Γ(X, X.basicOpen f.1)) =
        𝔞.ideal (X.affineBasicOpen f.1) := by
      rw [Submodule.localized'_eq_span, ← 𝔞.map_ideal_basicOpen U f.1]
      rfl
    have hfg : (𝔞.ideal (X.affineBasicOpen f.1)).FG := by
      obtain ⟨a, ha⟩ := f.2
      exact ha ▸ Submodule.fg_span_singleton a
    rw [Module.Finite.iff_fg]
    exact hloc' ▸ hfg
  exact Module.Finite.iff_fg.mp hfin

theorem ker_graphHom_fg (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t) (U : (pullback c t).affineOpens) :
    ((graphHom a₀ h₀).ker.ideal U).FG :=
  fg_ideal_of_forall_exists_span _
    (fun x => by
      obtain ⟨V, hxV, g, -, hg⟩ :=
        exists_affineOpen_ker_graph_eq_span_nonZeroDivisor a₀ h₀ x
      exact ⟨V, hxV, g, hg⟩) U

/-- The residual ideal of `D` obtained by taking its colon by the graph ideal. -/
noncomputable def residualSheaf {r : ℕ} (D : RelEffCartierDiv c (r + 1) t)
    (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t) : (pullback c t).IdealSheafData :=
  colonSheaf D.I (graphHom a₀ h₀).ker (ker_graphHom_fg a₀ h₀)

theorem I_eq_ker_mul_residualSheaf {r : ℕ} (D : RelEffCartierDiv c (r + 1) t)
    (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t)
    (hle : D.I ≤ (graphHom a₀ h₀).ker) :
    D.I = (graphHom a₀ h₀).ker * residualSheaf D a₀ h₀ := by
  choose U hxU g hgnzd hker using
    fun x => exists_affineOpen_ker_graph_eq_span_nonZeroDivisor a₀ h₀ x
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U ?_ fun x => ?_
  · rw [eq_top_iff]
    exact fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxU y⟩
  · have hch : (graphHom a₀ h₀).ker.ideal (U x) = Ideal.span {g x} := hker x
    have hle' : D.I.ideal (U x) ≤ Ideal.span {g x} :=
      (Scheme.IdealSheafData.le_def.mp hle (U x)).trans_eq hch
    change D.I.ideal (U x) =
      (graphHom a₀ h₀).ker.ideal (U x) *
        (D.I.ideal (U x)).colon ((graphHom a₀ h₀).ker.ideal (U x))
    rw [hch, Ideal.colon_span]
    exact eq_span_singleton_mul_colon _ _ hle'

theorem isClosedImmersion_inclusion {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J) :
    IsClosedImmersion (Scheme.IdealSheafData.inclusion h) := by
  have : IsClosedImmersion (Scheme.IdealSheafData.inclusion h ≫ I.subschemeι) := by
    rw [Scheme.IdealSheafData.inclusion_subschemeι]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ I.subschemeι

theorem le_residualSheaf {r : ℕ} (D : RelEffCartierDiv c (r + 1) t)
    (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t) : D.I ≤ residualSheaf D a₀ h₀ :=
  Scheme.IdealSheafData.le_def.mpr fun U x hx =>
    Submodule.mem_colon.mpr fun a _ => by
      rw [smul_eq_mul]; exact Ideal.mul_mem_right a _ hx

theorem isFinite_residualSheaf {r : ℕ} (D : RelEffCartierDiv c (r + 1) t)
    (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t) :
    IsFinite ((residualSheaf D a₀ h₀).subschemeι ≫ pullback.snd c t) := by
  have := D.isFinite
  have := isClosedImmersion_inclusion (le_residualSheaf D a₀ h₀)
  have hfac : (residualSheaf D a₀ h₀).subschemeι ≫ pullback.snd c t =
      Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
        (D.I.subschemeι ≫ pullback.snd c t) := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  rw [hfac]
  infer_instance

section moduleGrain

variable {R : Type*} [CommRing R]

theorem flat_ker_of_surjective {A B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Flat R A] [Module.Projective R B]
    (f : A →ₗ[R] B) (hf : Function.Surjective f) :
    Module.Flat R (LinearMap.ker f) := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hmem : ∀ x : A, x - s (f x) ∈ LinearMap.ker f := fun x => by
    simp only [LinearMap.mem_ker, map_sub]
    rw [show f (s (f x)) = (f ∘ₗ s) (f x) from rfl, hs]
    simp
  refine Module.Flat.of_retract (LinearMap.ker f).subtype
    ((LinearMap.id - s ∘ₗ f).codRestrict _ hmem) ?_
  ext ⟨x, hx⟩
  simp [LinearMap.mem_ker.mp hx]

end moduleGrain

universe v in
theorem flat_localizedModule_of_flat {R₀ A : Type v} [CommRing R₀] [CommRing A] [Algebra R₀ A]
    (p : Submonoid A)
    {M : Type v} [AddCommGroup M] [Module R₀ M] [Module A M] [IsScalarTower R₀ A M]
    [Module.Flat R₀ M] : Module.Flat R₀ (LocalizedModule p M) := by
  rw [Module.Flat.iff_lTensor_exact]
  intro N N' N'' _ _ _ _ _ _ f g hfg
  have hM : Function.Exact (LinearMap.lTensor M f) (LinearMap.lTensor M g) :=
    Module.Flat.iff_lTensor_exact.mp ‹Module.Flat R₀ M› hfg
  have hM' : Function.Exact (TensorProduct.AlgebraTensorModule.lTensor A M f)
      (TensorProduct.AlgebraTensorModule.lTensor A M g) := by
    simpa only [TensorProduct.AlgebraTensorModule.coe_lTensor] using hM
  have key := IsLocalizedModule.map_exact p
      (TensorProduct.AlgebraTensorModule.rTensor R₀ N (LocalizedModule.mkLinearMap p M))
      (TensorProduct.AlgebraTensorModule.rTensor R₀ N' (LocalizedModule.mkLinearMap p M))
      (TensorProduct.AlgebraTensorModule.rTensor R₀ N'' (LocalizedModule.mkLinearMap p M))
      (TensorProduct.AlgebraTensorModule.lTensor A M f)
      (TensorProduct.AlgebraTensorModule.lTensor A M g) hM'
  rw [IsLocalizedModule.map_lTensor, IsLocalizedModule.map_lTensor] at key
  simpa only [TensorProduct.AlgebraTensorModule.coe_lTensor] using key

theorem hom_predicate_seam {Z Y : Scheme.{u}} (q : Z ⟶ Y) (U : Y.Opens)
    (P : ∀ {R S : CommRingCat.{u}}, (R ⟶ S) → Prop) :
    P ((q ∣_ U).appTop) ↔ P (q.appLE U (q ⁻¹ᵁ U) le_rfl) := by
  rw [morphismRestrict_appTop, q.app_eq_appLE, Scheme.Hom.appLE_map]
  exact (Scheme.Hom.appLE_congr (f := q) le_rfl
    (Scheme.Opens.ι_image_top U).symm
    (show q ⁻¹ᵁ U = (q ⁻¹ᵁ U).ι ''ᵁ ((q ∣_ U) ⁻¹ᵁ ⊤) by
      rw [TopologicalSpace.Opens.map_top, Scheme.Opens.ι_image_top]) P).symm

theorem exists_affineOpen_le_span_nonZeroDivisor (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t)
    {V₀ : TopologicalSpace.Opens ↥(pullback c t)} {x : ↥(pullback c t)} (hx : x ∈ V₀) :
    ∃ W : (pullback c t).affineOpens, x ∈ W.1 ∧ W.1 ≤ V₀ ∧
      ∃ g ∈ nonZeroDivisors Γ(pullback c t, W.1),
        (graphHom a₀ h₀).ker.ideal W = Ideal.span {g} := by
  obtain ⟨V, hxV, g, hgnzd, hg⟩ :=
    exists_affineOpen_ker_graph_eq_span_nonZeroDivisor a₀ h₀ x
  obtain ⟨f, hle, hxf⟩ := V.2.exists_basicOpen_le (V := V₀ ⊓ V.1) ⟨x, hx, hxV⟩ hxV
  let := ((pullback c t).presheaf.map
    (homOfLE <| (pullback c t).basicOpen_le f).op).hom.toAlgebra
  have hloc : IsLocalization.Away f Γ(pullback c t, (pullback c t).basicOpen f) :=
    V.2.isLocalization_basicOpen f
  refine ⟨(pullback c t).affineBasicOpen f, hxf, hle.trans inf_le_left,
    algebraMap Γ(pullback c t, V.1) Γ(pullback c t, (pullback c t).basicOpen f) g, ?_, ?_⟩
  · have hreg : IsSMulRegular Γ(pullback c t, V.1) g := fun a b hab => by
      have h0 : (a - b) * g = 0 := by
        rw [sub_mul, sub_eq_zero]
        simpa [smul_eq_mul, mul_comm] using hab
      exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hgnzd).2 _ h0)
    have hreg' := hreg.of_isLocalization
      Γ(pullback c t, (pullback c t).basicOpen f) (Submonoid.powers f)
    have hcancel : ∀ y,
        y * algebraMap Γ(pullback c t, V.1)
          Γ(pullback c t, (pullback c t).basicOpen f) g = 0 → y = 0 := fun y hy => by
      have h2 : algebraMap Γ(pullback c t, V.1)
            Γ(pullback c t, (pullback c t).basicOpen f) g • y =
          algebraMap Γ(pullback c t, V.1)
            Γ(pullback c t, (pullback c t).basicOpen f) g • (0 : Γ(pullback c t,
              (pullback c t).basicOpen f)) := by
        simpa [smul_eq_mul, mul_comm] using hy
      exact hreg' h2
    exact mem_nonZeroDivisors_iff.mpr
      ⟨fun y hy => hcancel y ((mul_comm (show Γ(pullback c t,
        (pullback c t).basicOpen f) from y) _).trans hy), hcancel⟩
  · rw [← (graphHom a₀ h₀).ker.map_ideal_basicOpen V f, hg, Ideal.map_span,
      Set.image_singleton]
    rfl

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem graphHom_snd (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t) :
    graphHom a₀ h₀ ≫ pullback.snd c t = 𝟙 T :=
  graphOver_snd c a₀ h₀

scoped instance isClosedImmersion_graphHom (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t) :
    IsClosedImmersion (graphHom a₀ h₀) := by
  have : IsClosedImmersion (graphHom a₀ h₀ ≫ pullback.snd c t) := by
    rw [graphHom_snd]; infer_instance
  exact IsClosedImmersion.of_comp (graphHom a₀ h₀) (pullback.snd c t)

scoped instance isIso_ker_graphHom_subschemeι_snd (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t) :
    IsIso ((graphHom a₀ h₀).ker.subschemeι ≫ pullback.snd c t) := by
  have he : (graphHom a₀ h₀).ker.subschemeι =
      (asIso (graphHom a₀ h₀).toImage).inv ≫ graphHom a₀ h₀ :=
    ((asIso (graphHom a₀ h₀).toImage).eq_inv_comp).mpr ((graphHom a₀ h₀).toImage_imageι)
  rw [he, Category.assoc, graphHom_snd, Category.comp_id]
  infer_instance


theorem mk_subschemeObjIso_inclusion_appLE {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : I ≤ J) (W : X.affineOpens) :
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal W)) ≫ ((I.subschemeObjIso W).inv ≫
      ((Scheme.IdealSheafData.inclusion h).app (I.subschemeι ⁻¹ᵁ W.1) ≫
        J.subscheme.presheaf.map (eqToHom (by
          rw [← Scheme.IdealSheafData.inclusion_subschemeι h]; rfl :
            J.subschemeι ⁻¹ᵁ W.1 =
              Scheme.IdealSheafData.inclusion h ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ W.1))).op) ≫
      (J.subschemeObjIso W).hom) =
    CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal W)) := by
  have h1 := Scheme.Hom.congr_app (Scheme.IdealSheafData.inclusion_subschemeι h) W.1
  rw [Scheme.Hom.comp_app] at h1
  simp only [← Category.assoc]
  rw [← Scheme.IdealSheafData.subschemeι_app, h1]
  have hpre : J.subschemeι ⁻¹ᵁ W.1 =
      Scheme.IdealSheafData.inclusion h ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ W.1) := by
    rw [← Scheme.IdealSheafData.inclusion_subschemeι h]
    rfl
  change ((J.subschemeι.app W.1 ≫ J.subscheme.presheaf.map (eqToHom hpre.symm).op) ≫
    J.subscheme.presheaf.map (eqToHom hpre).op) ≫ (J.subschemeObjIso W).hom = _
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp, eqToHom_trans,
    eqToHom_refl, op_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Scheme.IdealSheafData.subschemeι_app,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem presheaf_map_injective_of_eq {X : Scheme.{u}} {U V : X.Opens} (hUV : U = V)
    (i : Opposite.op V ⟶ Opposite.op U) : Function.Injective (X.presheaf.map i).hom := by
  subst hUV
  obtain rfl : i = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [CategoryTheory.Functor.map_id]
  exact fun a b hab => hab


theorem inclusion_app_mk_eq_zero_iff {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J)
    (W : X.affineOpens) (y : Γ(X, W.1)) :
    ((Scheme.IdealSheafData.inclusion h).app (I.subschemeι ⁻¹ᵁ W.1)).hom
        ((I.subschemeObjIso W).inv.hom (Ideal.Quotient.mk (I.ideal W) y)) = 0 ↔
      y ∈ J.ideal W := by
  have KB := mk_subschemeObjIso_inclusion_appLE h W
  obtain ⟨φ, hφ, hφinj⟩ : ∃ φ : Γ(J.subscheme, Scheme.IdealSheafData.inclusion h ⁻¹ᵁ
        (I.subschemeι ⁻¹ᵁ W.1)) →+* (Γ(X, W.1) ⧸ J.ideal W),
      (∀ y, φ (((Scheme.IdealSheafData.inclusion h).app (I.subschemeι ⁻¹ᵁ W.1)).hom
        ((I.subschemeObjIso W).inv.hom (Ideal.Quotient.mk (I.ideal W) y))) =
          Ideal.Quotient.mk (J.ideal W) y) ∧ Function.Injective φ := by
    refine ⟨(J.subscheme.presheaf.map (eqToHom (by
        rw [← Scheme.IdealSheafData.inclusion_subschemeι h]; rfl :
          J.subschemeι ⁻¹ᵁ W.1 =
            Scheme.IdealSheafData.inclusion h ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ W.1))).op ≫
        (J.subschemeObjIso W).hom).hom, fun y => ?_, ?_⟩
    · have := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom KB) y
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using this
    · exact (ConcreteCategory.bijective_of_isIso _).1
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hφ y, map_eq_zero_iff φ hφinj]

theorem subschemeObjIso_inv_mk_surjective {X : Scheme.{u}} (I : X.IdealSheafData)
    (W : X.affineOpens) :
    Function.Surjective fun y : Γ(X, W.1) =>
      (I.subschemeObjIso W).inv.hom (Ideal.Quotient.mk (I.ideal W) y) :=
  (ConcreteCategory.bijective_of_isIso (I.subschemeObjIso W).inv).2.comp
    Ideal.Quotient.mk_surjective

theorem finite_ker_of_surjective {R : Type*} [CommRing R] {A B : Type*} [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] [Module.Finite R A] [Module.Projective R B]
    (f : A →ₗ[R] B) (hf : Function.Surjective f) :
    Module.Finite R (LinearMap.ker f) := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hmem : ∀ x : A, x - s (f x) ∈ LinearMap.ker f := fun x => by
    simp only [LinearMap.mem_ker, map_sub]
    rw [show f (s (f x)) = (f ∘ₗ s) (f x) from rfl, hs]
    simp
  refine Module.Finite.of_surjective ((LinearMap.id - s ∘ₗ f).codRestrict _ hmem) ?_
  rintro ⟨x, hx⟩
  exact ⟨x, Subtype.ext (by simp [LinearMap.mem_ker.mp hx])⟩

theorem nonempty_linearEquiv_prod_of_surjective {R : Type*} [CommRing R] {A B : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [Module.Projective R B]
    (f : A →ₗ[R] B) (hf : Function.Surjective f) :
    Nonempty (A ≃ₗ[R] (LinearMap.ker f × B)) := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hfs : ∀ b, f (s b) = b := fun b => LinearMap.congr_fun hs b
  have hmem : ∀ a : A, a - s (f a) ∈ LinearMap.ker f := fun a => by
    simp [LinearMap.mem_ker, hfs]
  refine ⟨LinearEquiv.ofLinearMap
    (LinearMap.prod ((LinearMap.id - s ∘ₗ f).codRestrict _ hmem) f)
    ((LinearMap.ker f).subtype ∘ₗ LinearMap.fst R _ B + s ∘ₗ LinearMap.snd R _ B) ?_ ?_⟩
  · apply LinearMap.ext
    rintro ⟨⟨k, hk⟩, b⟩
    have hk0 : f k = 0 := LinearMap.mem_ker.mp hk
    ext
    · simp [hk0, hfs]
    · simp [hk0, hfs]
  · apply LinearMap.ext
    intro a
    simp

theorem forall_finrank_eq_iff_of_isAffine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : X ⟶ Y) [Flat g] [IsFinite g] (n : ℕ) :
    (∀ y : Y, g.finrank y = n) ↔
      ∀ x : PrimeSpectrum Γ(Y, ⊤), g.appTop.hom.finrank x = n := by
  have hfl : g.appTop.hom.Flat := g.flat_appTop
  have hfi : g.appTop.hom.Finite := g.finite_appTop
  have : Flat (Spec.map g.appTop) := Flat.SpecMap_iff.mpr hfl
  have : IsFinite (Spec.map g.appTop) := (IsFinite.SpecMap_iff _).mpr hfi
  have H : IsPullback X.isoSpec.hom g (Spec.map g.appTop) Y.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality g⟩
  have key : ∀ y, g.finrank y = g.appTop.hom.finrank (Y.isoSpec.hom y) := fun y => by
    rw [← Scheme.Hom.finrank_SpecMap_eq_finrank hfi hfl,
      Scheme.Hom.finrank_of_isPullback _ _ _ _ H y]
  simp_rw [key]
  exact (Y.isoSpec.hom.homeomorph.surjective.forall
    (p := fun x => g.appTop.hom.finrank x = n)).symm

theorem forall_mem_finrank_eq_iff {Z Y : Scheme.{u}} (q : Z ⟶ Y) [Flat q] [IsFinite q]
    (U : Y.affineOpens) (n : ℕ) :
    (∀ s ∈ U.1, q.finrank s = n) ↔
      ∀ x : PrimeSpectrum Γ(Y, U.1), (q.appLE U.1 (q ⁻¹ᵁ U.1) le_rfl).hom.finrank x = n := by
  have : IsAffine (U.1 : Y.Opens) := U.2
  have : IsAffine (q ⁻¹ᵁ U.1) := U.2.preimage q
  have : Flat (q ∣_ U.1) := inferInstance
  have : IsFinite (q ∣_ U.1) := inferInstance
  have h1 : (∀ s ∈ U.1, q.finrank s = n) ↔ ∀ y : U.1, (q ∣_ U.1).finrank y = n := by
    rw [Subtype.forall]
    refine forall₂_congr fun s hs => ?_
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict q U.1).flip ⟨s, hs⟩]
    rfl
  exact h1.trans ((forall_finrank_eq_iff_of_isAffine (q ∣_ U.1) n).trans
    (hom_predicate_seam q U.1
      (fun {R S} φ => ∀ x : PrimeSpectrum R, (CommRingCat.Hom.hom φ).finrank x = n)))

section chartModules

variable {r : ℕ} (D : RelEffCartierDiv c (r + 1) t) (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t)
  (hle : D.I ≤ (graphHom a₀ h₀).ker) (U : T.affineOpens)

local notation "Rᵤ" => Functor.obj (D := CommRingCat) (PresheafedSpace.presheaf
  (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace (T)))))
  (Opposite.op (Subtype.val U))
local notation "Aᵤ" => Functor.obj (D := CommRingCat) (PresheafedSpace.presheaf
  (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace
      (Scheme.IdealSheafData.subscheme (RelEffCartierDiv.I D))))))
  (Opposite.op (Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
    (LocallyRingedSpace.Hom.toHom
      (Scheme.Hom.toLRSHom (Scheme.IdealSheafData.subschemeι (RelEffCartierDiv.I D) ≫
        pullback.snd c t))))) (Subtype.val U)))
local notation "Bᵤ" => Functor.obj (D := CommRingCat) (PresheafedSpace.presheaf
  (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace
      (Scheme.IdealSheafData.subscheme (residualSheaf D a₀ h₀))))))
  (Opposite.op (Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
    (LocallyRingedSpace.Hom.toHom
      (Scheme.Hom.toLRSHom (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
        (Scheme.IdealSheafData.subschemeι (RelEffCartierDiv.I D) ≫ pullback.snd c t))))))
        (Subtype.val U)))
local notation "Cᵤ" => Functor.obj (D := CommRingCat) (PresheafedSpace.presheaf
  (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace
      (Scheme.IdealSheafData.subscheme (Scheme.Hom.ker (graphHom a₀ h₀)))))))
  (Opposite.op (Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
    (LocallyRingedSpace.Hom.toHom
      (Scheme.Hom.toLRSHom (Scheme.IdealSheafData.inclusion hle ≫
        (Scheme.IdealSheafData.subschemeι (RelEffCartierDiv.I D) ≫ pullback.snd c t))))))
        (Subtype.val U)))

noncomputable scoped instance algRA : Algebra Rᵤ Aᵤ :=
  ((D.I.subschemeι ≫ pullback.snd c t).appLE U.1
    ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra

noncomputable scoped instance algAB : Algebra Aᵤ Bᵤ :=
  ((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).appLE
    ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) _ le_rfl).hom.toAlgebra

noncomputable scoped instance algRB : Algebra Rᵤ Bᵤ :=
  (((D.I.subschemeι ≫ pullback.snd c t).app U.1) ≫
    (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).appLE
      ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) _ le_rfl).hom.toAlgebra

scoped instance towerRAB : IsScalarTower Rᵤ Aᵤ Bᵤ :=
  IsScalarTower.of_algebraMap_eq' (by
    change (((D.I.subschemeι ≫ pullback.snd c t).app U.1) ≫
        (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).appLE
          ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) _ le_rfl).hom =
      ((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).appLE
          ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) _ le_rfl).hom.comp
        ((D.I.subschemeι ≫ pullback.snd c t).appLE U.1
          ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) le_rfl).hom
    rw [Scheme.Hom.app_eq_appLE]
    rfl)

scoped instance isFinite_subschemeι_comp_snd : IsFinite (D.I.subschemeι ≫ pullback.snd c t) :=
  D.isFinite

scoped instance flat_subschemeι_comp_snd : Flat (D.I.subschemeι ≫ pullback.snd c t) := D.flat

noncomputable scoped instance algRC : Algebra Rᵤ Cᵤ :=
  ((Scheme.IdealSheafData.inclusion hle ≫
    (D.I.subschemeι ≫ pullback.snd c t)).app U.1).hom.toAlgebra

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem flat_A : Module.Flat Rᵤ Aᵤ := by
  have := D.flat
  have : IsAffine (U.1 : T.Opens) := U.2
  have : IsAffine ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ (U.1 : T.Opens)) :=
    U.2.preimage _
  exact (hom_predicate_seam (D.I.subschemeι ≫ pullback.snd c t) U.1
    (fun {R S} g => (CommRingCat.Hom.hom g).Flat)).mp
    (((D.I.subschemeι ≫ pullback.snd c t) ∣_ U.1).flat_appTop)

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem finite_A : Module.Finite Rᵤ Aᵤ := by
  have := D.isFinite
  have : IsAffine (U.1 : T.Opens) := U.2
  have : IsAffine ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ (U.1 : T.Opens)) :=
    U.2.preimage _
  exact (hom_predicate_seam (D.I.subschemeι ≫ pullback.snd c t) U.1
    (fun {R S} g => (CommRingCat.Hom.hom g).Finite)).mp
    (((D.I.subschemeι ≫ pullback.snd c t) ∣_ U.1).finite_appTop)

theorem inclusion_comp_eq_subschemeι :
    Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
      (D.I.subschemeι ≫ pullback.snd c t) =
    (residualSheaf D a₀ h₀).subschemeι ≫ pullback.snd c t := by
  rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]

scoped instance isFinite_inclusion_comp :
    IsFinite (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
      (D.I.subschemeι ≫ pullback.snd c t)) := by
  rw [inclusion_comp_eq_subschemeι]
  exact isFinite_residualSheaf D a₀ h₀

theorem finite_B : Module.Finite Rᵤ Bᵤ := by
  have : IsAffine (U.1 : T.Opens) := U.2
  have : IsAffine ((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
      (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ (U.1 : T.Opens)) :=
    U.2.preimage _
  have h := (hom_predicate_seam (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
      (D.I.subschemeι ≫ pullback.snd c t)) U.1
    (fun {R S} g => (CommRingCat.Hom.hom g).Finite)).mp
    (((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
      (D.I.subschemeι ≫ pullback.snd c t)) ∣_ U.1).finite_appTop)
  rw [Scheme.Hom.comp_appLE] at h
  exact h

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem inclusion_comp_eq_ker_subschemeι :
    Scheme.IdealSheafData.inclusion hle ≫ (D.I.subschemeι ≫ pullback.snd c t) =
      (graphHom a₀ h₀).ker.subschemeι ≫ pullback.snd c t := by
  rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]

scoped instance isIso_inclusion_comp :
    IsIso (Scheme.IdealSheafData.inclusion hle ≫ (D.I.subschemeι ≫ pullback.snd c t)) := by
  rw [inclusion_comp_eq_ker_subschemeι]
  infer_instance

scoped instance isIso_app_inclusion_comp :
    IsIso ((Scheme.IdealSheafData.inclusion hle ≫
      (D.I.subschemeι ≫ pullback.snd c t)).app U.1) :=
  inferInstance

/-- The sections of the graph subscheme are identified with the base sections via its projection. -/
noncomputable def algEquivC : Rᵤ ≃ₐ[Rᵤ] Cᵤ :=
  AlgEquiv.ofRingEquiv
    (f := (asIso ((Scheme.IdealSheafData.inclusion hle ≫
      (D.I.subschemeι ≫ pullback.snd c t)).app U.1)).commRingCatIsoToRingEquiv)
    (fun x => by
      simp only [Algebra.algebraMap_self, RingHom.id_apply,
        RingHom.algebraMap_toAlgebra]
      rfl)

scoped instance free_C : Module.Free Rᵤ Cᵤ :=
  Module.Free.of_equiv (algEquivC D a₀ h₀ hle U).toLinearEquiv

scoped instance finite_C : Module.Finite Rᵤ Cᵤ :=
  Module.Finite.equiv (algEquivC D a₀ h₀ hle U).toLinearEquiv

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem inclusion_app_comp_algebraMap :
    ((Scheme.IdealSheafData.inclusion hle).app
        ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)).hom.comp (algebraMap Rᵤ Aᵤ) =
      algebraMap Rᵤ Cᵤ := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, Scheme.Hom.comp_app,
    ← Scheme.Hom.app_eq_appLE]
  rfl

/-- The restriction of sections from the divisor subscheme to the contained graph subscheme. -/
noncomputable def πC : Aᵤ →ₐ[Rᵤ] Cᵤ :=
  AlgHom.mk' ((Scheme.IdealSheafData.inclusion hle).app
      ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)).hom
    (fun cc x => by
      let φ : Aᵤ →+* Cᵤ := ((Scheme.IdealSheafData.inclusion hle).app
        ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)).hom
      change φ ((algebraMap Rᵤ Aᵤ) cc * x) = (algebraMap Rᵤ Cᵤ) cc * φ x
      exact (map_mul φ _ _).trans
        (congrArg (fun y : Cᵤ => y * φ x)
          (DFunLike.congr_fun (inclusion_app_comp_algebraMap D a₀ h₀ hle U) cc)))

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem πC_surjective : Function.Surjective (πC D a₀ h₀ hle U) :=
  haveI : IsClosedImmersion (Scheme.IdealSheafData.inclusion hle) :=
    isClosedImmersion_inclusion hle
  (Scheme.IdealSheafData.inclusion hle).app_surjective _ (U.2.preimage _)

/-- The canonical linear equivalence between the ring kernel and linear kernel of this
  restriction. -/
noncomputable def kerπCEquiv : (RingHom.ker (πC D a₀ h₀ hle U).toRingHom) ≃ₗ[Rᵤ]
    ↥(LinearMap.ker (πC D a₀ h₀ hle U).toLinearMap) :=
  { toFun := fun x => ⟨x.1,
      LinearMap.mem_ker.mpr
        ((RingHom.mem_ker (f := (πC D a₀ h₀ hle U).toRingHom)).mp x.2)⟩
    invFun := fun x => ⟨x.1,
      (RingHom.mem_ker (f := (πC D a₀ h₀ hle U).toRingHom)).mpr
        (LinearMap.mem_ker.mp x.2)⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

omit [SmoothOfRelativeDimension 1 c] in
theorem flat_kerπC : Module.Flat Rᵤ (RingHom.ker (πC D a₀ h₀ hle U).toRingHom) :=
  haveI := flat_A D U
  haveI := flat_ker_of_surjective (πC D a₀ h₀ hle U).toLinearMap (πC_surjective D a₀ h₀ hle U)
  Module.Flat.of_linearEquiv (kerπCEquiv D a₀ h₀ hle U)

omit [SmoothOfRelativeDimension 1 c] in
theorem finite_kerπC : Module.Finite Rᵤ (RingHom.ker (πC D a₀ h₀ hle U).toRingHom) :=
  haveI := finite_A D U
  haveI := finite_ker_of_surjective (πC D a₀ h₀ hle U).toLinearMap
    (πC_surjective D a₀ h₀ hle U)
  Module.Finite.equiv (kerπCEquiv D a₀ h₀ hle U).symm

section localizedChart

noncomputable local instance residualBasicOpenAlgebra (h : Aᵤ) : Algebra
      Γ((residualSheaf D a₀ h₀).subscheme,
        (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
          (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
      Γ((residualSheaf D a₀ h₀).subscheme,
        (residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
              (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
                (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) :=
    (((residualSheaf D a₀ h₀).subscheme.presheaf.map (homOfLE
      ((residualSheaf D a₀ h₀).subscheme.basicOpen_le _)).op).hom).toAlgebra

noncomputable local instance divisorBasicOpenAlgebra (h : Aᵤ) : Algebra Γ(D.I.subscheme,
  (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
      Γ(D.I.subscheme, D.I.subscheme.basicOpen h) :=
    ((D.I.subscheme.presheaf.map (homOfLE
      (D.I.subscheme.basicOpen_le h)).op).hom).toAlgebra

noncomputable local instance residualBasicOpenAlgebraOverDivisor (h : Aᵤ) : Algebra
  Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
      Γ((residualSheaf D a₀ h₀).subscheme,
        (residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
              (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
                (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) :=
    ((algebraMap Γ((residualSheaf D a₀ h₀).subscheme,
        (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
          (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
        Γ((residualSheaf D a₀ h₀).subscheme,
        (residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
              (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
                (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h))).comp
      (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
        Γ((residualSheaf D a₀ h₀).subscheme,
        (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
          (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1))).toAlgebra

local instance divisorBasicOpenIsLocalization (h : Aᵤ) :
    IsLocalization.Away h Γ(D.I.subscheme, D.I.subscheme.basicOpen h) :=
  (U.2.preimage (D.I.subschemeι ≫ pullback.snd c t)).isLocalization_basicOpen h

private theorem basicOpen_sections_equiv_kernel
    (W : (pullback c t).affineOpens) (hWle : W.1 ≤ (pullback.snd c t) ⁻¹ᵁ U.1)
    (g : Γ(pullback c t, W.1)) (hgspan : (graphHom a₀ h₀).ker.ideal W = Ideal.span {g})
    (h : Aᵤ) (hhle : D.I.subscheme.basicOpen h ≤ D.I.subschemeι ⁻¹ᵁ W.1) :
    Nonempty (Γ((residualSheaf D a₀ h₀).subscheme,
        (residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
              (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
                (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) ≃ₗ[Γ(D.I.subscheme,
                  (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)]
      ↥((RingHom.ker (πC D a₀ h₀ hle U).toRingHom).localized'
        Γ(D.I.subscheme, D.I.subscheme.basicOpen h) (Submonoid.powers h)
        (Algebra.linearMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
          Γ(D.I.subscheme, D.I.subscheme.basicOpen h)))) := by
  have : IsClosedImmersion
      (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)) :=
    isClosedImmersion_inclusion _
  have : IsClosedImmersion (Scheme.IdealSheafData.inclusion hle) :=
    isClosedImmersion_inclusion hle
  have hopen : (residualSheaf D a₀ h₀).subscheme.basicOpen
      (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
        Γ((residualSheaf D a₀ h₀).subscheme,
      (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
        (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h) =
      Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ⁻¹ᵁ
        (D.I.subscheme.basicOpen h) := by
    rw [Scheme.preimage_basicOpen]
    change (residualSheaf D a₀ h₀).subscheme.basicOpen
      (((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).appLE
        ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) _ le_rfl).hom h) = _
    rw [Scheme.Hom.app_eq_appLE]
  have hsurjB' : Function.Surjective
      ((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).appLE
        (D.I.subscheme.basicOpen h)
        ((residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
      (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
        (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) hopen.le) := by
    have hs := (Scheme.IdealSheafData.inclusion
      (le_residualSheaf D a₀ h₀)).app_surjective (D.I.subscheme.basicOpen h)
      ((U.2.preimage (D.I.subschemeι ≫ pullback.snd c t)).basicOpen h)
    rw [Scheme.Hom.app_eq_appLE] at hs
    exact ((Scheme.IdealSheafData.inclusion
      (le_residualSheaf D a₀ h₀)).appLE_congr _ rfl hopen.symm
      (fun f => Function.Surjective f)).mp hs
  have hsq : D.I.subscheme.presheaf.map (homOfLE
        (D.I.subscheme.basicOpen_le h)).op ≫
      (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).appLE
        (D.I.subscheme.basicOpen h)
        ((residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
      (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
        (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) hopen.le =
      (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).appLE
        ((D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
        ((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
          (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) le_rfl ≫
      (residualSheaf D a₀ h₀).subscheme.presheaf.map (homOfLE (by
        rw [hopen]
        exact Scheme.Hom.preimage_mono _ (D.I.subscheme.basicOpen_le h))).op := by
    exact ((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).map_appLE
      hopen.le (homOfLE (D.I.subscheme.basicOpen_le h)).op).trans
      ((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).appLE_map
        le_rfl _).symm
  set πB' : Γ(D.I.subscheme, D.I.subscheme.basicOpen h) →ₐ[Γ(D.I.subscheme, (D.I.subschemeι ≫
    pullback.snd c t) ⁻¹ᵁ U.1)]
      Γ((residualSheaf D a₀ h₀).subscheme,
        (residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
      (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
        (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) :=
    { toRingHom := ((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).appLE
        (D.I.subscheme.basicOpen h)
        ((residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
      (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
        (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) hopen.le).hom
      commutes' a := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hsq) a }
    with hπB'
  have eQuot := Ideal.quotientKerAlgEquivOfSurjective (f := πB') hsurjB'
  have hWD : D.I.subschemeι ⁻¹ᵁ W.1 ≤
      (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1 :=
    Scheme.Hom.preimage_mono _ hWle
  obtain ⟨htil, hhtil⟩ := D.I.subschemeι.app_surjective W.1 W.2
    ((D.I.subscheme.presheaf.map (homOfLE hWD).op).hom h)
  have hDh : D.I.subschemeι ⁻¹ᵁ ((pullback c t).basicOpen htil) =
      D.I.subscheme.basicOpen h := by
    rw [Scheme.preimage_basicOpen, hhtil, Scheme.basicOpen_res]
    exact inf_eq_right.mpr hhle
  have hkerWt : (graphHom a₀ h₀).ker.ideal ((pullback c t).affineBasicOpen htil) =
      Ideal.span {((pullback c t).presheaf.map (homOfLE
        ((pullback c t).basicOpen_le htil)).op).hom g} := by
    rw [← (graphHom a₀ h₀).ker.map_ideal_basicOpen W htil, hgspan, Ideal.map_span,
      Set.image_singleton]
  let Wt : (pullback c t).affineOpens := (pullback c t).affineBasicOpen htil
  let gt : Γ(pullback c t, Wt.1) :=
    ((pullback c t).presheaf.map (homOfLE ((pullback c t).basicOpen_le htil)).op).hom g
  let VD : D.I.subscheme.affineOpens :=
    ⟨(D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1,
      U.2.preimage (D.I.subschemeι ≫ pullback.snd c t)⟩
  let resh : Γ(D.I.subscheme, D.I.subschemeι ⁻¹ᵁ Wt.1) ⟶
      Γ(D.I.subscheme, D.I.subscheme.basicOpen h) :=
    D.I.subscheme.presheaf.map (eqToHom hDh.symm).op
  have hreshinj : Function.Injective resh.hom :=
    presheaf_map_injective_of_eq hDh.symm _
  have hreshsurj : Function.Surjective resh.hom :=
    (ConcreteCategory.bijective_of_isIso
      (D.I.subscheme.presheaf.map (eqToHom hDh.symm).op)).2
  have hsurjI := subschemeObjIso_inv_mk_surjective D.I Wt
  have hisoIinj : Function.Injective (D.I.subschemeObjIso Wt).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (D.I.subschemeObjIso Wt).inv).1
  let gq : Γ(D.I.subscheme, D.I.subschemeι ⁻¹ᵁ Wt.1) :=
    (D.I.subschemeObjIso Wt).inv.hom (Ideal.Quotient.mk (D.I.ideal Wt) gt)
  let ghat : Γ(D.I.subscheme, D.I.subscheme.basicOpen h) := resh.hom gq
  have h𝔟 : (RingHom.ker (πC D a₀ h₀ hle U).toRingHom).localized'
        Γ(D.I.subscheme, D.I.subscheme.basicOpen h) (Submonoid.powers h)
        (Algebra.linearMap
          Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
          Γ(D.I.subscheme, D.I.subscheme.basicOpen h)) =
      Ideal.span {ghat} := by
    have hkerC : RingHom.ker (πC D a₀ h₀ hle U).toRingHom =
        (Scheme.IdealSheafData.inclusion hle).ker.ideal VD := by
      rw [Scheme.Hom.ker_apply]
      rfl
    have e1 : (RingHom.ker (πC D a₀ h₀ hle U).toRingHom).localized'
          Γ(D.I.subscheme, D.I.subscheme.basicOpen h) (Submonoid.powers h)
          (Algebra.linearMap
            Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ(D.I.subscheme, D.I.subscheme.basicOpen h)) =
        (Scheme.IdealSheafData.inclusion hle).ker.ideal
          (D.I.subscheme.affineBasicOpen (U := VD) h) := by
      rw [Submodule.localized'_eq_span,
        ← (Scheme.IdealSheafData.inclusion hle).ker.map_ideal_basicOpen VD h, hkerC]
      rfl
    have e2 : (Scheme.IdealSheafData.inclusion hle).ker.ideal
        ⟨D.I.subschemeι ⁻¹ᵁ Wt.1, Wt.2.preimage D.I.subschemeι⟩ = Ideal.span {gq} := by
      rw [Scheme.Hom.ker_apply]
      apply le_antisymm
      · intro x' hx'
        obtain ⟨y, rfl⟩ := hsurjI x'
        have hy := (inclusion_app_mk_eq_zero_iff hle Wt y).mp hx'
        rw [hkerWt] at hy
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
        change (D.I.subschemeObjIso Wt).inv.hom (Ideal.Quotient.mk _ (a * gt)) ∈ _
        rw [map_mul, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      · rw [Ideal.span_singleton_le_iff_mem]
        refine (inclusion_app_mk_eq_zero_iff hle Wt gt).mpr ?_
        rw [hkerWt]
        exact Ideal.mem_span_singleton_self _
    have e3 : (Scheme.IdealSheafData.inclusion hle).ker.ideal
        (D.I.subscheme.affineBasicOpen (U := VD) h) = Ideal.span {ghat} := by
      rw [← (Scheme.IdealSheafData.inclusion hle).ker.map_ideal'
          (U := D.I.subscheme.affineBasicOpen (U := VD) h)
          (V := ⟨D.I.subschemeι ⁻¹ᵁ Wt.1, Wt.2.preimage D.I.subschemeι⟩)
          (eqToHom hDh.symm).op,
        e2, Ideal.map_span, Set.image_singleton]
      rfl
    exact e1.trans e3
  have hreshB : ∀ x' : Γ(D.I.subscheme, D.I.subschemeι ⁻¹ᵁ Wt.1),
      πB' (resh.hom x') = 0 ↔
        ((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).app
          (D.I.subschemeι ⁻¹ᵁ Wt.1)).hom x' = 0 := by
    intro x'
    have hcomp := (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).map_appLE
      hopen.le (eqToHom hDh.symm).op
    have HH := hopen.trans (congrArg (fun O => (Scheme.IdealSheafData.inclusion
      (le_residualSheaf D a₀ h₀)) ⁻¹ᵁ O) hDh.symm)
    change (D.I.subscheme.presheaf.map (eqToHom hDh.symm).op ≫
      (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).appLE _ _
        hopen.le).hom x' = 0 ↔ _
    rw [hcomp, Scheme.Hom.appLE]
    change ((residualSheaf D a₀ h₀).subscheme.presheaf.map (homOfLE _).op).hom
      (((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)).app _).hom x') = 0 ↔ _
    beta_reduce at HH
    exact map_eq_zero_iff _ (presheaf_map_injective_of_eq HH _)
  have hJiff : ∀ y : Γ(pullback c t, Wt.1),
      y ∈ (residualSheaf D a₀ h₀).ideal Wt ↔ y * gt ∈ D.I.ideal Wt := by
    intro y
    have hker : (graphHom a₀ h₀).ker.ideal Wt =
        Ideal.span ({gt} : Set Γ(pullback c t, Wt.1)) := hkerWt
    rw [residualSheaf, ideal_colonSheaf, hker]
    exact Ideal.mem_colon_span_singleton
  have hleWt : D.I.ideal Wt ≤ (residualSheaf D a₀ h₀).ideal Wt :=
    Scheme.IdealSheafData.le_def.mp (le_residualSheaf D a₀ h₀) Wt
  have hK : (RingHom.ker πB'.toRingHom : Ideal Γ(D.I.subscheme, D.I.subscheme.basicOpen h)) =
      LinearMap.ker (LinearMap.toSpanSingleton Γ(D.I.subscheme, D.I.subscheme.basicOpen h)
        Γ(D.I.subscheme, D.I.subscheme.basicOpen h) ghat) := by
    ext x
    obtain ⟨x', rfl⟩ := hreshsurj x
    obtain ⟨y, rfl⟩ := hsurjI x'
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul, RingHom.mem_ker]
    change πB' (resh.hom _) = 0 ↔ _
    rw [hreshB, inclusion_app_mk_eq_zero_iff (le_residualSheaf D a₀ h₀) Wt y, hJiff,
      show ghat = resh.hom ((D.I.subschemeObjIso Wt).inv.hom
        (Ideal.Quotient.mk (D.I.ideal Wt) gt)) from rfl,
      ← map_mul, map_eq_zero_iff _ hreshinj, ← map_mul,
      map_eq_zero_iff _ hisoIinj, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨eQuot.symm.toLinearEquiv ≪≫ₗ
    ((Submodule.quotEquivOfEq _ _ hK ≪≫ₗ
      (LinearMap.toSpanSingleton Γ(D.I.subscheme, D.I.subscheme.basicOpen h)
        Γ(D.I.subscheme, D.I.subscheme.basicOpen h) ghat).quotKerEquivRange ≪≫ₗ
      LinearEquiv.ofEq _ _ ((LinearMap.span_singleton_eq_range _ _ ghat).symm.trans
        h𝔟.symm)).restrictScalars
      Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1))⟩

private theorem localizedModule_equiv_of_chart
    (W : (pullback c t).affineOpens) (hWle : W.1 ≤ (pullback.snd c t) ⁻¹ᵁ U.1)
    (g : Γ(pullback c t, W.1)) (hgspan : (graphHom a₀ h₀).ker.ideal W = Ideal.span {g})
    (h : Aᵤ) (hhle : D.I.subscheme.basicOpen h ≤ D.I.subschemeι ⁻¹ᵁ W.1) :
    Nonempty (LocalizedModule (Submonoid.powers h) Bᵤ ≃ₗ[Aᵤ]
      LocalizedModule (Submonoid.powers h) (RingHom.ker (πC D a₀ h₀ hle U).toRingHom)) := by
  have : IsClosedImmersion
      (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)) :=
    isClosedImmersion_inclusion _
  have : IsClosedImmersion (Scheme.IdealSheafData.inclusion hle) :=
    isClosedImmersion_inclusion hle
  have hBloc : IsLocalization.Away
      (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
        Γ((residualSheaf D a₀ h₀).subscheme,
          (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
            (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)
      Γ((residualSheaf D a₀ h₀).subscheme,
        (residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
              (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
                (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) :=
    (U.2.preimage (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
      (D.I.subschemeι ≫ pullback.snd c t))).isLocalization_basicOpen _
  have htower2 : IsScalarTower Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
      Γ((residualSheaf D a₀ h₀).subscheme,
        (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
          (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
      Γ((residualSheaf D a₀ h₀).subscheme,
        (residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
              (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
                (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hBloc' : IsLocalization
      (Algebra.algebraMapSubmonoid Γ((residualSheaf D a₀ h₀).subscheme,
        (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
          (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
        (Submonoid.powers h))
      Γ((residualSheaf D a₀ h₀).subscheme,
        (residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
              (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
                (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) := by
    have heq : Algebra.algebraMapSubmonoid Γ((residualSheaf D a₀ h₀).subscheme,
        (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
          (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
        (Submonoid.powers h) = Submonoid.powers (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫
          pullback.snd c t) ⁻¹ᵁ U.1)
          Γ((residualSheaf D a₀ h₀).subscheme,
        (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
          (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h) :=
      Submonoid.map_powers _ _
    exact heq ▸ hBloc
  have hBmod : IsLocalizedModule (Submonoid.powers h)
      (IsScalarTower.toAlgHom Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
        Γ((residualSheaf D a₀ h₀).subscheme,
        (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
          (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
        Γ((residualSheaf D a₀ h₀).subscheme,
        (residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
              (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
                (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h))).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr hBloc'
  have middle := basicOpen_sections_equiv_kernel D a₀ h₀ hle U W hWle g hgspan h hhle
  have eB : LocalizedModule (Submonoid.powers h)
      Γ((residualSheaf D a₀ h₀).subscheme,
        (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
          (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) ≃ₗ[Γ(D.I.subscheme, (D.I.subschemeι ≫
            pullback.snd c t) ⁻¹ᵁ U.1)]
      Γ((residualSheaf D a₀ h₀).subscheme,
        (residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
              (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
                (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h)) :=
    IsLocalizedModule.iso (Submonoid.powers h)
      (IsScalarTower.toAlgHom Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
        Γ((residualSheaf D a₀ h₀).subscheme,
        (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
          (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1)
        Γ((residualSheaf D a₀ h₀).subscheme,
        (residualSheaf D a₀ h₀).subscheme.basicOpen
          (algebraMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
            Γ((residualSheaf D a₀ h₀).subscheme,
              (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
                (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) h))).toLinearMap
  have e𝔞 : LocalizedModule (Submonoid.powers h) (RingHom.ker (πC D a₀ h₀ hle U).toRingHom)
    ≃ₗ[Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)]
      ↥((RingHom.ker (πC D a₀ h₀ hle U).toRingHom).localized'
        Γ(D.I.subscheme, D.I.subscheme.basicOpen h) (Submonoid.powers h)
        (Algebra.linearMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
          Γ(D.I.subscheme, D.I.subscheme.basicOpen h))) :=
    IsLocalizedModule.iso (Submonoid.powers h)
      ((RingHom.ker (πC D a₀ h₀ hle U).toRingHom).toLocalized'
        Γ(D.I.subscheme, D.I.subscheme.basicOpen h) (Submonoid.powers h)
        (Algebra.linearMap Γ(D.I.subscheme, (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1)
          Γ(D.I.subscheme, D.I.subscheme.basicOpen h)))
  exact ⟨eB.trans ((Classical.choice middle).trans e𝔞.symm)⟩

end localizedChart

theorem exists_basicOpen_localizedModule_equiv (z : D.I.subscheme)
    (hz : z ∈ (D.I.subschemeι ≫ pullback.snd c t) ⁻¹ᵁ U.1) :
    ∃ h : Aᵤ, z ∈ D.I.subscheme.basicOpen h ∧
      Nonempty (LocalizedModule (Submonoid.powers h) Bᵤ ≃ₗ[Aᵤ]
        LocalizedModule (Submonoid.powers h) (RingHom.ker (πC D a₀ h₀ hle U).toRingHom)) := by
  have hCIE : IsClosedImmersion
      (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀)) :=
    isClosedImmersion_inclusion _
  have hCI𝔞 : IsClosedImmersion (Scheme.IdealSheafData.inclusion hle) :=
    isClosedImmersion_inclusion hle
  have hx : (D.I.subschemeι.base z : ↥(pullback c t)) ∈
      (pullback.snd c t) ⁻¹ᵁ (U.1 : T.Opens) := hz
  obtain ⟨W, hxW, hWle, g, hgnzd, hgspan⟩ :=
    exists_affineOpen_le_span_nonZeroDivisor a₀ h₀ (V₀ := (pullback.snd c t) ⁻¹ᵁ U.1) hx
  obtain ⟨h, hhle, hzh⟩ := (U.2.preimage (D.I.subschemeι ≫ pullback.snd c t) :
      IsAffineOpen _).exists_basicOpen_le
    (V := D.I.subschemeι ⁻¹ᵁ W.1) ⟨z, hxW⟩ hz
  have hgood := localizedModule_equiv_of_chart D a₀ h₀ hle U W hWle g hgspan h hhle
  exact ⟨h, hzh, hgood⟩

theorem span_setOf_localizedModule_equiv_eq_top :
    Ideal.span {h : Aᵤ | Nonempty (LocalizedModule (Submonoid.powers h) Bᵤ ≃ₗ[Aᵤ]
      LocalizedModule (Submonoid.powers h) (RingHom.ker (πC D a₀ h₀ hle U).toRingHom))} =
    ⊤ := by
  refine (U.2.preimage (D.I.subschemeι ≫ pullback.snd c t)).self_le_iSup_basicOpen_iff.mp
    (fun z hz => ?_)
  obtain ⟨h, hzh, hgood⟩ := exists_basicOpen_localizedModule_equiv D a₀ h₀ hle U z hz
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨h, hgood⟩, hzh⟩

include hle in
theorem flat_B : Module.Flat Rᵤ Bᵤ :=
  haveI := flat_kerπC D a₀ h₀ hle U
  Module.flat_of_isLocalized_span (S := Aᵤ)
    (spn := span_setOf_localizedModule_equiv_eq_top D a₀ h₀ hle U)
    (Mₛ := fun h => LocalizedModule (Submonoid.powers h.1)
      (RingHom.ker (πC D a₀ h₀ hle U).toRingHom))
    (g := fun h => (Classical.choice h.2).toLinearMap ∘ₗ
      LocalizedModule.mkLinearMap (Submonoid.powers h.1) _)
    (H := fun h => flat_localizedModule_of_flat (Submonoid.powers h.1))

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem rankAtStalk_A (x : PrimeSpectrum Rᵤ) : Module.rankAtStalk (R := Rᵤ) Aᵤ x = r + 1 :=
  (forall_mem_finrank_eq_iff (D.I.subschemeι ≫ pullback.snd c t) U (r + 1)).mp
    (fun s _ => D.finrank_eq s) x

omit [SmoothOfRelativeDimension 1 c] in
theorem rankAtStalk_kerπC (x : PrimeSpectrum Rᵤ) :
    Module.rankAtStalk (R := Rᵤ) (RingHom.ker (πC D a₀ h₀ hle U).toRingHom) x = r := by
  have := flat_A D U
  have := finite_A D U
  have := flat_ker_of_surjective (πC D a₀ h₀ hle U).toLinearMap (πC_surjective D a₀ h₀ hle U)
  have := finite_ker_of_surjective (πC D a₀ h₀ hle U).toLinearMap
    (πC_surjective D a₀ h₀ hle U)
  have : Nontrivial Rᵤ := ⟨⟨0, 1, fun h01 => x.2.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h01 ▸ x.asIdeal.zero_mem))⟩⟩
  obtain ⟨e⟩ := nonempty_linearEquiv_prod_of_surjective (πC D a₀ h₀ hle U).toLinearMap
    (πC_surjective D a₀ h₀ hle U)
  have hA := rankAtStalk_A D U x
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod, Pi.add_apply,
    ← Module.rankAtStalk_eq_of_equiv (kerπCEquiv D a₀ h₀ hle U),
    ← Module.rankAtStalk_eq_of_equiv (algEquivC D a₀ h₀ hle U).toLinearEquiv,
    Module.rankAtStalk_self, Pi.one_apply] at hA
  exact Nat.add_right_cancel hA

include hle in
theorem rankAtStalk_B (x : PrimeSpectrum Rᵤ) : Module.rankAtStalk (R := Rᵤ) Bᵤ x = r := by
  have := finite_A D U
  have := finite_B D a₀ h₀ U
  have := flat_B D a₀ h₀ hle U
  have := flat_kerπC D a₀ h₀ hle U
  have := finite_kerπC D a₀ h₀ hle U
  rw [Module.rankAtStalk_eq_of_forall_localizedModule_equiv (R := Rᵤ) (A := Aᵤ) Bᵤ
    (RingHom.ker (πC D a₀ h₀ hle U).toRingHom) _
    (span_setOf_localizedModule_equiv_eq_top D a₀ h₀ hle U) (fun h hh => hh)]
  exact rankAtStalk_kerπC D a₀ h₀ hle U x

include hle in
theorem finitePresentation_B : Module.FinitePresentation Rᵤ Bᵤ :=
  haveI := finite_B D a₀ h₀ U
  haveI := flat_B D a₀ h₀ hle U
  Module.finitePresentation_of_rankAtStalk_eq Bᵤ r (rankAtStalk_B D a₀ h₀ hle U)

end chartModules

theorem flat_residualSheaf {r : ℕ} (D : RelEffCartierDiv c (r + 1) t)
    (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t) (hle : D.I ≤ (graphHom a₀ h₀).ker) :
    Flat ((residualSheaf D a₀ h₀).subschemeι ≫ pullback.snd c t) := by
  let : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  rw [← inclusion_comp_eq_subschemeι]
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Flat) _ (iSup_affineOpens_eq_top T)]
  intro U
  have hU : IsAffine (U.1 : T.Opens) := U.2
  have hV : IsAffine ((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
      (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) :=
    U.2.preimage _
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  refine (hom_predicate_seam _ _ (fun {R S} g => (CommRingCat.Hom.hom g).Flat)).mpr ?_
  rw [Scheme.Hom.comp_appLE]
  exact flat_B D a₀ h₀ hle U

theorem locallyOfFinitePresentation_residualSheaf {r : ℕ} (D : RelEffCartierDiv c (r + 1) t)
    (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t) (hle : D.I ≤ (graphHom a₀ h₀).ker) :
    LocallyOfFinitePresentation ((residualSheaf D a₀ h₀).subschemeι ≫ pullback.snd c t) := by
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  rw [← inclusion_comp_eq_subschemeι]
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
    (iSup_affineOpens_eq_top T)]
  intro U
  have hU : IsAffine (U.1 : T.Opens) := U.2
  have hV : IsAffine ((Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
      (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1) :=
    U.2.preimage _
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  refine (hom_predicate_seam _ _
    (fun {R S} g => (CommRingCat.Hom.hom g).FinitePresentation)).mpr ?_
  rw [Scheme.Hom.comp_appLE]
  have := finitePresentation_B D a₀ h₀ hle U
  exact (Algebra.FinitePresentation.of_finitePresentation _ _ :
    Algebra.FinitePresentation Γ(T, U.1) Γ((residualSheaf D a₀ h₀).subscheme,
      (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
        (D.I.subschemeι ≫ pullback.snd c t)) ⁻¹ᵁ U.1))

theorem finrank_residualSheaf {r : ℕ} (D : RelEffCartierDiv c (r + 1) t)
    (a₀ : T ⟶ C) (h₀ : a₀ ≫ c = t) (hle : D.I ≤ (graphHom a₀ h₀).ker) (s : T) :
    ((residualSheaf D a₀ h₀).subschemeι ≫ pullback.snd c t).finrank s = r := by
  rw [← inclusion_comp_eq_subschemeι D a₀ h₀]
  have : Flat (Scheme.IdealSheafData.inclusion (le_residualSheaf D a₀ h₀) ≫
      (D.I.subschemeι ≫ pullback.snd c t)) := by
    rw [inclusion_comp_eq_subschemeι]
    exact flat_residualSheaf D a₀ h₀ hle
  obtain ⟨U, hsU⟩ : ∃ U : T.affineOpens, s ∈ U.1 := by
    have hs : s ∈ (⊤ : T.Opens) := trivial
    rw [← iSup_affineOpens_eq_top T] at hs
    exact TopologicalSpace.Opens.mem_iSup.mp hs
  refine (forall_mem_finrank_eq_iff _ U r).mpr (fun x => ?_) s hsU
  rw [Scheme.Hom.comp_appLE]
  exact rankAtStalk_B D a₀ h₀ hle U x

end ResidualSplitting

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_graphOver_mul
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f] {r : ℕ}
    {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f (r + 1) g)
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) (hle : D.I ≤ (graphOver f a ha).ker) :
    ∃ E : RelEffCartierDiv f r g, D.I = (graphOver f a ha).ker * E.I :=
  ⟨{ I := ResidualSplitting.residualSheaf D a ha
     isFinite := ResidualSplitting.isFinite_residualSheaf D a ha
     flat := ResidualSplitting.flat_residualSheaf D a ha hle
     locallyOfFinitePresentation :=
       ResidualSplitting.locallyOfFinitePresentation_residualSheaf D a ha hle
     finrank_eq := ResidualSplitting.finrank_residualSheaf D a ha hle },
   ResidualSplitting.I_eq_ker_mul_residualSheaf D a ha hle⟩
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_I_eq_ker_graphOver_mul
end ProofImplementation

open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
attribute [-simp] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
