/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_isRepresentable_supportedIn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivRestrict
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_isUniversal_of_isAffine
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isUniversal_empty

/-!
Representability of the presheaf of relative divisors supported in an open.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_isRepresentable_supportedIn
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
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
attribute [-simp]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
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

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
namespace ChartRep
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {r : ℕ} {V : S.Opens} {U : 𝒞.Opens}
  {hUV : U ≤ f ⁻¹ᵁ V}

lemma extendAlong_congr {T : Scheme.{u}} {gV₁ gV₂ : T ⟶ V} (hV : gV₁ = gV₂) {g : T ⟶ S}
    (hg₁ : gV₁ ≫ V.ι = g) (hg₂ : gV₂ ≫ V.ι = g)
    (D₁ : RelEffCartierDiv (f.resLE V U hUV) r gV₁) (D₂ : RelEffCartierDiv (f.resLE V U hUV) r gV₂)
    (hD : HEq D₁ D₂) :
    extendAlong f r V U hUV gV₁ g hg₁ D₁ = extendAlong f r V U hUV gV₂ g hg₂ D₂ := by
  subst hV
  rw [eq_of_heq hD]

lemma extendAlong_heq {T : Scheme.{u}} {gV₁ gV₂ : T ⟶ V} (hV : gV₁ = gV₂) {g₁ g₂ : T ⟶ S}
    (hg : g₁ = g₂) (hg₁ : gV₁ ≫ V.ι = g₁) (hg₂ : gV₂ ≫ V.ι = g₂)
    (D₁ : RelEffCartierDiv (f.resLE V U hUV) r gV₁) (D₂ : RelEffCartierDiv (f.resLE V U hUV) r gV₂)
    (hD : HEq D₁ D₂) :
    HEq (extendAlong f r V U hUV gV₁ g₁ hg₁ D₁) (extendAlong f r V U hUV gV₂ g₂ hg₂ D₂) := by
  subst hV; subst hg
  rw [eq_of_heq hD]
omit [IsSeparated f] in
lemma pullbackAlong_heq' {T T' : Scheme.{u}} {y : T' ⟶ V} (D : RelEffCartierDiv (f.resLE V U
    hUV) r y)
    {φ₁ φ₂ : T ⟶ T'} (hφ : φ₁ = φ₂) {g₁ g₂ : T ⟶ V} (h₁ : φ₁ ≫ y = g₁) (h₂ : φ₂ ≫ y = g₂) :
    HEq (D.pullbackAlong φ₁ h₁) (D.pullbackAlong φ₂ h₂) := by
  subst hφ
  obtain rfl : g₁ = g₂ := h₁.symm.trans h₂
  rfl

end AlgebraicGeometry.RelEffCartierDiv.ChartRep

open _root_.AlgebraicGeometry
    RelEffCartierDiv_isRepresentable_supportedIn.AlgebraicGeometry
      _root_.AlgebraicGeometry.RelEffCartierDiv
        RelEffCartierDiv_isRepresentable_supportedIn.AlgebraicGeometry.RelEffCartierDiv
    RelEffCartierDiv_isRepresentable_supportedIn.AlgebraicGeometry.RelEffCartierDiv.ChartRep in
theorem _root_.AlgebraicGeometry.RelEffCartierDiv.isRepresentable_supportedIn
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f] (r : ℕ)
    (V : S.affineOpens) (U : 𝒞.affineOpens) (hUV : (U : 𝒞.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)) :
    ∃ X : Scheme.{u}, (0 < r → IsAffine X) ∧
      Nonempty ((RelEffCartierDiv.supportedIn f r U).toFunctor.RepresentableBy X) := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨S, fun h => absurd h (lt_irrefl 0), ⟨?_⟩⟩
    have hall : ∀ (T : Scheme.{u}ᵒᵖ) (x : (RelEffCartierDiv.functor f 0).obj T),
        x ∈ (RelEffCartierDiv.supportedIn f 0 (U : 𝒞.Opens)).obj T := by
      rintro T ⟨g, D⟩
      change D.SupportedIn U
      intro z hz
      rw [D.I_eq_top_of_degree_zero, Scheme.IdealSheafData.support_top] at hz
      exact absurd hz (Set.notMem_empty z)
    let e0 : RelEffCartierDiv.functor f 0 ≅ (RelEffCartierDiv.supportedIn f 0 (U :
      𝒞.Opens)).toFunctor :=
      NatIso.ofComponents (fun T => Equiv.toIso
        { toFun := fun x => ⟨x, hall T x⟩
          invFun := fun x => x.1
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }) (by intros; rfl)
    exact (isUniversal_empty f).representableBy.ofIso e0
  · have : IsAffine (U : Scheme.{u}) := U.2
    have : IsAffine ((V : S.Opens) : Scheme.{u}) := V.2
    set V' : S.Opens := (V : S.Opens) with hV'
    set U' : 𝒞.Opens := (U : 𝒞.Opens) with hU'
    let fU : (U' : Scheme.{u}) ⟶ (V' : Scheme.{u}) := f.resLE V' U' hUV
    have : MorphismProperty.IsStableUnderBaseChange
        (fun {X Y : Scheme.{u}} (g : X ⟶ Y) => SmoothOfRelativeDimension 1 g) :=
      smoothOfRelativeDimension_isStableUnderBaseChange 1
    have : SmoothOfRelativeDimension 1 (f ∣_ V') :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := fun {X Y : Scheme.{u}} (g : X ⟶ Y) => SmoothOfRelativeDimension 1 g)
        (isPullback_morphismRestrict f V').flip inferInstance
    have : SmoothOfRelativeDimension 1 fU := by
      change SmoothOfRelativeDimension 1 (Scheme.Hom.resLE f V' U' hUV)
      delta Scheme.Hom.resLE
      exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (𝒞.homOfLE hUV ≫ f ∣_ V'))
    obtain ⟨Yc, hYc, yc, Dc, hUc⟩ := exists_isUniversal_of_isAffine fU r
    have hrange : ∀ {T : Scheme.{u}} (x : (RelEffCartierDiv.supportedIn f r U').toFunctor.obj
      (op T)),
        Set.range x.1.1 ⊆ Set.range V'.ι := fun x =>
      range_subset_of_supportedIn f r V' U' hUV x.1.2 x.2 hr
    let ℓ : ∀ {T : Scheme.{u}} (x : (RelEffCartierDiv.supportedIn f r U').toFunctor.obj (op T)),
      T ⟶ V' :=
      fun x => IsOpenImmersion.lift V'.ι x.1.1 (hrange x)
    have hℓ : ∀ {T : Scheme.{u}} (x : (RelEffCartierDiv.supportedIn f r U').toFunctor.obj (op T)),
        ℓ x ≫ V'.ι = x.1.1 := fun x => IsOpenImmersion.lift_fac _ _ _
    let fwd : ∀ {T : Scheme.{u}}, (T ⟶ Yc) → (RelEffCartierDiv.supportedIn f r U').toFunctor.obj
      (op T) :=
      fun φ => ⟨⟨φ ≫ (yc ≫ V'.ι), extendAlong f r V' U' hUV (φ ≫ yc) (φ ≫ (yc ≫ V'.ι))
          (Category.assoc _ _ _) (Dc.pullbackAlong φ rfl)⟩,
        extendAlong_supportedIn f r V' U' hUV _ _ _ _⟩
    let bwd : ∀ {T : Scheme.{u}}, (RelEffCartierDiv.supportedIn f r U').toFunctor.obj (op T) →
      (T ⟶ Yc) :=
      fun x => hUc.lift (restrictAlong f r V' U' hUV (ℓ x) x.1.1 (hℓ x) x.1.2 x.2)
    have hleft_aux : ∀ {T : Scheme.{u}} (φ : T ⟶ Yc) (L : T ⟶ V') (hL : L = φ ≫ yc)
        (hLfac : L ≫ V'.ι = φ ≫ (yc ≫ V'.ι))
        (hsupp : (extendAlong f r V' U' hUV (φ ≫ yc) (φ ≫ (yc ≫ V'.ι)) (Category.assoc _ _ _)
          (Dc.pullbackAlong φ rfl)).SupportedIn U'),
        hUc.lift (restrictAlong f r V' U' hUV L (φ ≫ (yc ≫ V'.ι)) hLfac
          (extendAlong f r V' U' hUV (φ ≫ yc) (φ ≫ (yc ≫ V'.ι)) (Category.assoc _ _ _)
            (Dc.pullbackAlong φ rfl)) hsupp) = φ := by
      intro T φ L hL hLfac hsupp
      subst hL
      rw [restrictAlong_extendAlong]
      exact hUc.lift_pullbackAlong φ
    have hleft : ∀ {T : Scheme.{u}} (φ : T ⟶ Yc), bwd (fwd φ) = φ := by
      intro T φ
      refine hleft_aux φ (ℓ (fwd φ)) ?_ (hℓ (fwd φ)) (fwd φ).2
      exact (IsOpenImmersion.lift_uniq _ _ _ (φ ≫ yc) (Category.assoc _ _ _)).symm
    have hright : ∀ {T : Scheme.{u}} (x : (RelEffCartierDiv.supportedIn f r U').toFunctor.obj
      (op T)),
        fwd (bwd x) = x := by
      intro T x
      obtain ⟨⟨g, D⟩, hD⟩ := x
      set D'' := restrictAlong f r V' U' hUV (ℓ ⟨⟨g, D⟩, hD⟩) g (hℓ ⟨⟨g, D⟩, hD⟩) D hD with hD''
      have h1 : hUc.lift D'' ≫ yc = ℓ ⟨⟨g, D⟩, hD⟩ := hUc.lift_comp D''
      have hg : hUc.lift D'' ≫ (yc ≫ V'.ι) = g := by
        rw [← Category.assoc, h1, hℓ]
      apply Subtype.ext
      refine Sigma.ext hg ?_
      change HEq (extendAlong f r V' U' hUV (hUc.lift D'' ≫ yc) (hUc.lift D'' ≫ (yc ≫ V'.ι))
        (Category.assoc _ _ _) (Dc.pullbackAlong (hUc.lift D'') rfl)) D
      have h2 : extendAlong f r V' U' hUV (ℓ ⟨⟨g, D⟩, hD⟩) g (hℓ ⟨⟨g, D⟩, hD⟩)
          (Dc.pullbackAlong (hUc.lift D'') (hUc.lift_comp D'')) = D := by
        rw [hUc.pullbackAlong_lift D'', hD'']
        exact extendAlong_restrictAlong f r V' U' hUV
          (ℓ ⟨⟨g, D⟩, hD⟩) g (hℓ ⟨⟨g, D⟩, hD⟩) D hD
      exact (extendAlong_heq h1 hg _ _ _ _ (pullbackAlong_heq' Dc rfl rfl _)).trans (heq_of_eq h2)
    have hnat : ∀ {T₁ T₂ : Scheme.{u}} (φ : T₁ ⟶ T₂) (ψ : T₂ ⟶ Yc),
        fwd (φ ≫ ψ) = (RelEffCartierDiv.supportedIn f r U').toFunctor.map φ.op (fwd ψ) := by
      intro T₁ T₂ φ ψ
      apply Subtype.ext
      change (⟨(φ ≫ ψ) ≫ (yc ≫ V'.ι), _⟩ : Σ g : T₁ ⟶ S, RelEffCartierDiv f r g) =
        ⟨φ ≫ (ψ ≫ (yc ≫ V'.ι)), (extendAlong f r V' U' hUV (ψ ≫ yc) (ψ ≫ (yc ≫ V'.ι))
          (Category.assoc _ _ _) (Dc.pullbackAlong ψ rfl)).pullbackAlong φ rfl⟩
      refine Sigma.ext (Category.assoc _ _ _) ?_
      rw [← extendAlong_pullbackAlong f r V' U' hUV (gV₁ := φ ≫ ψ ≫ yc) (by simp only
        [Category.assoc])
        (Category.assoc _ _ _) (Dc.pullbackAlong ψ rfl) φ rfl rfl, Dc.pullbackAlong_comp ψ rfl φ
          rfl]
      exact extendAlong_heq (Category.assoc _ _ _) (Category.assoc _ _ _) _ _ _ _
        (pullbackAlong_heq' Dc rfl _ _)
    refine ⟨Yc, fun _ => hYc, ⟨Functor.representableByEquiv.symm (NatIso.ofComponents
      (fun T => Equiv.toIso { toFun := fwd, invFun := bwd, left_inv := hleft, right_inv := hright })
      ?_)⟩⟩
    intro T₁ T₂ φ
    ext ψ
    exact hnat φ.unop ψ
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_isRepresentable_supportedIn
end ProofImplementation

open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
attribute [-simp]
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
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
