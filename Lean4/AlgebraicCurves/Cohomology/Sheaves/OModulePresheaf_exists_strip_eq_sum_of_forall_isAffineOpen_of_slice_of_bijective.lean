/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayDoubleComplex
import AlgebraicCurves.Geometry.Schemes.Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
import AlgebraicCurves.Geometry.Schemes.Scheme_exists_forall_eq_appLE_of_forall_map_eq_of_bijective

/-!
# OModule Presheaf exists strip eq sum of forall is Affine Open of slice of bijective
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.StripAffineAssembly

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct

universe u

namespace G5Body

section Alg

variable {k : Type u} [Field k]
  {C0 C1 C2 : Type u} [AddCommGroup C0] [Module k C0] [AddCommGroup C1] [Module k C1]
  [AddCommGroup C2] [Module k C2]
  (d0 : C0 →ₗ[k] C1) (d1 : C1 →ₗ[k] C2)

/-- The subspace of cocycles for the second differential. -/
abbrev ZZ : Submodule k C1 := LinearMap.ker d1

/-- The subspace of cocycles that are boundaries of the first differential. -/
abbrev BB : Submodule k (ZZ d1) := (LinearMap.range d0).comap (ZZ d1).subtype

/-- The quotient of cocycles by boundaries. -/
abbrev HH : Type u := ZZ d1 ⧸ BB d0 d1

theorem exists_r : ∃ r : C1 →ₗ[k] HH d0 d1, r ∘ₗ (ZZ d1).subtype = (BB d0 d1).mkQ :=
  LinearMap.exists_extend _

variable (r : C1 →ₗ[k] HH d0 d1) (hr : r ∘ₗ (ZZ d1).subtype = (BB d0 d1).mkQ)
  (hdd : d1 ∘ₗ d0 = 0)
include hr in
theorem r_apply_of_mem (z : C1) (hz : z ∈ ZZ d1) : r z = (BB d0 d1).mkQ ⟨z, hz⟩ := by
  have := LinearMap.congr_fun hr ⟨z, hz⟩
  simpa using this

include hr hdd in
theorem r_comp_d0 : r ∘ₗ d0 = 0 := by
  ext c
  have hz : d0 c ∈ ZZ d1 := by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hdd, LinearMap.zero_apply]
  rw [LinearMap.comp_apply, LinearMap.zero_apply, r_apply_of_mem d0 d1 r hr _ hz,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨c, rfl⟩

variable (A : Type u) [AddCommGroup A] [Module k A]

/-- The tensor extension of the chosen map to cohomology. -/
abbrev cl : A ⊗[k] C1 →ₗ[k] A ⊗[k] HH d0 d1 := LinearMap.lTensor A r

include hr hdd in
theorem cl_lTensor_d0 (w : A ⊗[k] C0) : cl d0 d1 r A (LinearMap.lTensor A d0 w) = 0 := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, r_comp_d0 d0 d1 r hr hdd,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- The first differential with codomain restricted to the boundary subspace. -/
def d0' : C0 →ₗ[k] BB d0 d1 :=
  LinearMap.codRestrict (BB d0 d1)
    (LinearMap.codRestrict (ZZ d1) d0 (fun c => by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hdd, LinearMap.zero_apply]))
    (fun c => ⟨c, rfl⟩)

theorem d0'_surjective : Function.Surjective (d0' d0 d1 hdd) := by
  rintro ⟨⟨z, hz⟩, ⟨c, hc⟩⟩
  exact ⟨c, Subtype.ext (Subtype.ext hc)⟩

theorem subtype_comp_subtype_comp_d0' :
    (ZZ d1).subtype ∘ₗ (BB d0 d1).subtype ∘ₗ d0' d0 d1 hdd = d0 := by
  ext c; rfl

include hr hdd in
theorem exists_of_cl_eq_zero (z : A ⊗[k] C1) (hz : LinearMap.lTensor A d1 z = 0)
    (hcl : cl d0 d1 r A z = 0) : ∃ w : A ⊗[k] C0, LinearMap.lTensor A d0 w = z := by
  have hex1 : Function.Exact (LinearMap.lTensor A (ZZ d1).subtype) (LinearMap.lTensor A d1) :=
    Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map d1)
  obtain ⟨ζ, rfl⟩ := (hex1 z).mp hz
  have hq : LinearMap.lTensor A (BB d0 d1).mkQ ζ = 0 := by
    rw [← hr, LinearMap.lTensor_comp, LinearMap.comp_apply]
    exact hcl
  have hex2 : Function.Exact (LinearMap.lTensor A (BB d0 d1).subtype)
      (LinearMap.lTensor A (BB d0 d1).mkQ) :=
    lTensor_exact A (LinearMap.exact_subtype_mkQ (BB d0 d1)) (Submodule.mkQ_surjective _)
  obtain ⟨β, rfl⟩ := (hex2 ζ).mp hq
  obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective A (d0'_surjective d0 d1 hdd) β
  refine ⟨w, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    ← LinearMap.lTensor_comp, LinearMap.comp_assoc, subtype_comp_subtype_comp_d0']

include hr in
theorem cl_tmul_of_mem (a : A) (z : C1) (hz : z ∈ ZZ d1) :
    cl d0 d1 r A (a ⊗ₜ[k] z) = a ⊗ₜ[k] (BB d0 d1).mkQ ⟨z, hz⟩ := by
  rw [LinearMap.lTensor_tmul, r_apply_of_mem d0 d1 r hr z hz]

theorem map_cl {A' : Type u} [AddCommGroup A'] [Module k A'] (φ : A →ₗ[k] A') (x : A ⊗[k] C1) :
    TensorProduct.map φ LinearMap.id (cl d0 d1 r A x) = cl d0 d1 r A' (TensorProduct.map φ
      LinearMap.id x) := by
  simp only [LinearMap.lTensor_def, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    LinearMap.id_comp,
    LinearMap.comp_id]

end Alg

end G5Body

namespace G5Body

section Coord

variable {k : Type u} [Field k] {H : Type u} [AddCommGroup H] [Module k H]
  {Λ : Type u} (bH : Module.Basis Λ k H)

/-- Tensor coordinates in a fixed basis of the second factor. -/
noncomputable def coord (A : Type u) [AddCommGroup A] [Module k A] : A ⊗[k] H ≃ₗ[k] (Λ →₀ A) := by
  classical
  exact (LinearEquiv.lTensor A bH.repr).trans (TensorProduct.finsuppScalarRight k k A Λ)

theorem coord_tmul (A : Type u) [AddCommGroup A] [Module k A] (a : A) (h : H) (l : Λ) :
    coord bH A (a ⊗ₜ[k] h) l = bH.repr h l • a := by
  classical
  simp only [coord, LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul,
    TensorProduct.finsuppScalarRight_apply_tmul, Finsupp.sum_apply]
  rw [Finsupp.sum, Finset.sum_eq_single l]
  · simp
  · intro b _ hb; rw [Finsupp.single_apply, ite_eq_right hb]
  · intro hl; simp [Finsupp.notMem_support_iff.mp hl]

theorem coord_map {A A' : Type u} [AddCommGroup A] [Module k A] [AddCommGroup A'] [Module k A']
    (φ : A →ₗ[k] A') (x : A ⊗[k] H) (l : Λ) :
    coord bH A' (TensorProduct.map φ LinearMap.id x) l = φ (coord bH A x l) := by
  induction x using TensorProduct.inductionOn with
  | tmul a h => rw [TensorProduct.map_tmul, LinearMap.id_apply, coord_tmul, coord_tmul, map_smul]
  | add x y hx hy =>
      rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]

end Coord

end G5Body

namespace G5Body

section Generic

variable {P X : Scheme.{u}} (p₁ : P ⟶ X)

theorem res_res {U V W : P.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h₁).op).hom ((P.presheaf.map (homOfLE h₂).op).hom x)
      = (P.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

theorem res_self {U : P.Opens} (h : U ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h).op).hom x = x := by
  rw [Subsingleton.elim (homOfLE h).op (𝟙 (op U)), P.presheaf.map_id]; rfl

theorem res_any {U W : P.Opens} (i : op U ⟶ op W) (h : W ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map i).hom x = (P.presheaf.map (homOfLE h).op).hom x := by
  rw [Subsingleton.elim i (homOfLE h).op]

theorem res_appLE {U : X.Opens} {V W : P.Opens} (e : V ≤ p₁ ⁻¹ᵁ U)
    (h : W ≤ V) (y : Γ(X, U)) :
    (P.presheaf.map (homOfLE h).op).hom ((p₁.appLE U V e).hom y) = (p₁.appLE U W (h.trans e)).hom y
      := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res {U U' : X.Opens} {V : P.Opens} (e : V ≤ p₁ ⁻¹ᵁ U)
    (h : U ≤ U') (y : Γ(X, U')) :
    (p₁.appLE U V e).hom ((X.presheaf.map (homOfLE h).op).hom y)
      = (p₁.appLE U' V (e.trans (p₁.preimage_mono h))).hom y := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem appLE_of_eq_id (f : X ⟶ X) (hf : f = 𝟙 X) {U V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : V ≤ U) (y : Γ(X, U)) :
    (f.appLE U V e).hom y = (X.presheaf.map (homOfLE h).op).hom y := by
  subst hf
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  change (X.presheaf.map (homOfLE e).op).hom ((𝟙 Γ(X, U) : Γ(X, U) ⟶ Γ(X, U)).hom y) = _
  rw [CommRingCat.id_apply]
  exact res_any _ h y

theorem appLE_top_congr {S : Scheme.{u}} (g g' : P ⟶ S) (hg : g = g') (W : P.Opens) (y : Γ(S, ⊤)) :
    (g.appLE ⊤ W le_top).hom y = (g'.appLE ⊤ W le_top).hom y := by
  subst hg; rfl

end Generic

section Strip

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y)

/-- The module presheaf of sections on a strip of the fibre product. -/
noncomputable def strip (hw : p₁ ≫ fX = p₂ ≫ fY) (U : X.Opens) : OModulePresheaf fY where
  obj V := Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
  addCommGroup _ := inferInstance
  module V := (Scheme.TwoAffineOpenCover.algebraOfHom (p₁ ≫ fX) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)).toModule
  moduleSections V := Module.compHom _ (p₂.appLE V (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_right).hom
  isScalarTower V := by
    let := Scheme.TwoAffineOpenCover.algebraOfHom fY V
    let := Scheme.TwoAffineOpenCover.algebraOfHom (p₁ ≫ fX) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
    let : Module Γ(Y, V) Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) :=
      Module.compHom _ (p₂.appLE V (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_right).hom
    refine ⟨fun r a x => ?_⟩
    change (p₂.appLE V _ inf_le_right).hom
          ((fY.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r) * a) * x
      = ((p₁ ≫ fX).appLE ⊤ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r)
          * ((p₂.appLE V _ inf_le_right).hom a * x)
    rw [map_mul, ← mul_assoc]
    congr 2
    rw [← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE p₂ fY ⊤ V (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) le_top inf_le_right,
      appLE_top_congr (p₂ ≫ fY) (p₁ ≫ fX) hw.symm]
  res h := (OModulePresheaf.unit (p₁ ≫ fX)).res (inf_le_inf_left _ (p₂.preimage_mono h))
  res_smul {V V'} h a x := by
    change (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U) (p₂.preimage_mono h))).op).hom
          ((p₂.appLE V' _ inf_le_right).hom a * x)
      = (p₂.appLE V _ inf_le_right).hom ((Y.presheaf.map (homOfLE h).op).hom a)
          * (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U) (p₂.preimage_mono h))).op).hom x
    rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply (f := Y.presheaf.map _),
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  res_refl V := (OModulePresheaf.unit (p₁ ≫ fX)).res_refl _
  res_comp h h' := (OModulePresheaf.unit (p₁ ≫ fX)).res_comp _ _

variable (hw : p₁ ≫ fX = p₂ ≫ fY)

theorem strip_obj (U : X.Opens) (V : Y.Opens) :
    (strip fX fY p₁ p₂ hw U).obj V = Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) := rfl

theorem strip_res_apply (U : X.Opens) {V V' : Y.Opens} (h : V ≤ V') (x : Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ
  V')) :
    (strip fX fY p₁ p₂ hw U).res h (show (strip fX fY p₁ p₂ hw U).obj V' from x)
      = (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U) (p₂.preimage_mono h))).op).hom x := rfl

end Strip

end G5Body

namespace G5Body

section Phi

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
  (𝒱 : Y.OrderedAffineCover)

/-- The affine tensor comparison on one intersection of the cover. -/
noncomputable def Φσ (U : X.affineOpens) {n : ℕ} (σ : 𝒱.Idx n) :
    (OModulePresheaf.unit fX).obj U.1 ⊗[k] (OModulePresheaf.unit fY).obj (𝒱.inter σ)
      ≃ₗ[k] (strip fX fY p₁ p₂ hP.w U.1).obj (𝒱.inter σ) :=
  (AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback fX fY
    p₁ p₂ hP
    U.1 U.2 (𝒱.inter σ) (Scheme.OrderedAffineCover.isAffineOpen_inter fY 𝒱 σ)).2.choose

theorem Φσ_tmul (U : X.affineOpens) {n : ℕ} (σ : 𝒱.Idx n) (a : Γ(X, U.1)) (b : Γ(Y, 𝒱.inter σ)) :
    Φσ fX fY p₁ p₂ hP 𝒱 U σ (a ⊗ₜ[k] b)
      = (p₁.appLE U.1 (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_left).hom a *
          (p₂.appLE (𝒱.inter σ) (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right).hom b :=
  (AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback fX fY
    p₁ p₂ hP
    U.1 U.2 (𝒱.inter σ) (Scheme.OrderedAffineCover.isAffineOpen_inter fY 𝒱 σ)).2.choose_spec a b

/-- The affine tensor comparison on cochains of the cover. -/
noncomputable def Φ (U : X.affineOpens) (n : ℕ) :
    (OModulePresheaf.unit fX).obj U.1 ⊗[k] (OModulePresheaf.unit fY).cochain 𝒱 n
      ≃ₗ[k] (strip fX fY p₁ p₂ hP.w U.1).cochain 𝒱 n := by
  classical
  exact (TensorProduct.piRight k k ((OModulePresheaf.unit fX).obj U.1)
    (fun σ : 𝒱.Idx n => (OModulePresheaf.unit fY).obj (𝒱.inter σ))).trans
      (LinearEquiv.piCongrRight (fun σ => Φσ fX fY p₁ p₂ hP 𝒱 U σ))

theorem Φ_tmul (U : X.affineOpens) (n : ℕ) (a : Γ(X, U.1)) (f : (OModulePresheaf.unit fY).cochain 𝒱
  n)
    (σ : 𝒱.Idx n) :
    Φ fX fY p₁ p₂ hP 𝒱 U n ((show (OModulePresheaf.unit fX).obj U.1 from a) ⊗ₜ[k] f) σ
      = (p₁.appLE U.1 (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_left).hom a *
          (p₂.appLE (𝒱.inter σ) (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right).hom (f σ) := by
  classical
  simp only [Φ, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
  exact Φσ_tmul fX fY p₁ p₂ hP 𝒱 U σ a (f σ)

theorem Φ_lTensor_d (U : X.affineOpens) (n : ℕ)
    (w : (OModulePresheaf.unit fX).obj U.1 ⊗[k] (OModulePresheaf.unit fY).cochain 𝒱 n) :
    Φ fX fY p₁ p₂ hP 𝒱 U (n + 1) (LinearMap.lTensor _ ((OModulePresheaf.unit fY).d 𝒱 n) w)
      = (strip fX fY p₁ p₂ hP.w U.1).d 𝒱 n (Φ fX fY p₁ p₂ hP 𝒱 U n w) := by
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul a f =>
    rw [LinearMap.lTensor_tmul]
    funext σ
    erw [Φ_tmul, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (p₂.appLE (𝒱.inter σ) (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right).hom
        (((-1 : ℤ) ^ (j : ℕ)) • (OModulePresheaf.unit fY).res (𝒱.inter_le_inter_face σ j) (f
          (𝒱.face σ j)))
        = ((-1 : ℤ) ^ (j : ℕ)) • (p₂.appLE (𝒱.inter (𝒱.face σ j)) (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)
            (inf_le_right.trans (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))).hom (f (𝒱.face σ
              j)) := by
      erw [map_zsmul]
      exact congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) (appLE_res p₂ _ _ _)
    have h2 : (strip fX fY p₁ p₂ hP.w U.1).res (𝒱.inter_le_inter_face σ j)
        (Φ fX fY p₁ p₂ hP 𝒱 U n ((show (OModulePresheaf.unit fX).obj U.1 from a) ⊗ₜ[k] f) (𝒱.face σ
          j))
        = (p₁.appLE U.1 (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_left).hom a *
          (p₂.appLE (𝒱.inter (𝒱.face σ j)) (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)
            (inf_le_right.trans (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))).hom (f (𝒱.face σ
              j)) := by
      rw [Φ_tmul fX fY p₁ p₂ hP 𝒱 U n a f (𝒱.face σ j)]
      erw [strip_res_apply, map_mul, res_appLE, res_appLE]
    erw [h1, h2, mul_smul_comm]
    rfl

/-- Restriction of strip cochains along an inclusion of affine opens. -/
noncomputable def resS {U U' : X.affineOpens} (hle : U'.1 ≤ U.1) (n : ℕ)
    (x : (strip fX fY p₁ p₂ hP.w U.1).cochain 𝒱 n) : (strip fX fY p₁ p₂ hP.w U'.1).cochain 𝒱 n :=
  fun σ => (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) (p₁.preimage_mono hle) :
    p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (x σ)

omit [IsSeparated fY] in
theorem resS_apply {U U' : X.affineOpens} (hle : U'.1 ≤ U.1) (n : ℕ)
    (x : (strip fX fY p₁ p₂ hP.w U.1).cochain 𝒱 n) (σ : 𝒱.Idx n) :
    resS fX fY p₁ p₂ hP 𝒱 hle n x σ = (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
      (p₁.preimage_mono hle) : p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter
        σ)).op).hom (x σ) :=
  rfl

theorem resS_Φ {U U' : X.affineOpens} (hle : U'.1 ≤ U.1) (n : ℕ)
    (x : (OModulePresheaf.unit fX).obj U.1 ⊗[k] (OModulePresheaf.unit fY).cochain 𝒱 n) :
    resS fX fY p₁ p₂ hP 𝒱 hle n (Φ fX fY p₁ p₂ hP 𝒱 U n x)
      = Φ fX fY p₁ p₂ hP 𝒱 U' n (TensorProduct.map ((OModulePresheaf.unit fX).res hle) LinearMap.id
        x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a f =>
    funext σ
    rw [resS_apply, TensorProduct.map_tmul, LinearMap.id_apply]
    erw [OModulePresheaf.unit_res_apply (π := fX), Φ_tmul, Φ_tmul,
      map_mul, res_appLE, res_appLE, appLE_res]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, ← hx, ← hy]; funext σ; simp only [resS_apply, Pi.add_apply]
    exact (P.presheaf.map _).hom.map_add _ _

end Phi

end G5Body

namespace G5Body

section Eval

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
  (x₀ : Spec (CommRingCat.of k) ⟶ X)
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
  (iY : Y ⟶ P) (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
  (𝒱 : Y.OrderedAffineCover) (U₀ : X.affineOpens) (hU₀ : x₀ ⁻¹ᵁ U₀.1 = ⊤)

include fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀

omit [IsSeparated fY] hP 𝒱 fX in
theorem hEle (V : Y.Opens) : V ≤ iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U₀.1 ⊓ p₂ ⁻¹ᵁ V) := by
  intro y hy
  refine ⟨?_, ?_⟩
  · change y ∈ (iY ≫ p₁) ⁻¹ᵁ U₀.1
    rw [hiY₁, Scheme.Hom.comp_preimage, hU₀]; trivial
  · change y ∈ (iY ≫ p₂) ⁻¹ᵁ V
    rw [hiY₂]; exact hy

/-- Evaluation of strip cochains along the given section of the second projection. -/
noncomputable def E (n : ℕ) (x : (strip fX fY p₁ p₂ hP.w U₀.1).cochain 𝒱 n) :
    (OModulePresheaf.unit fY).cochain 𝒱 n :=
  fun σ => (iY.appLE (p₁ ⁻¹ᵁ U₀.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) (𝒱.inter σ)
    (hEle fY x₀ p₁ p₂ iY hiY₁ hiY₂ U₀ hU₀ (𝒱.inter σ))).hom (x σ)

omit [IsSeparated fY] in
theorem E_apply (n : ℕ) (x : (strip fX fY p₁ p₂ hP.w U₀.1).cochain 𝒱 n) (σ : 𝒱.Idx n) :
    E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ n x σ
      = (iY.appLE (p₁ ⁻¹ᵁ U₀.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) (𝒱.inter σ)
          (hEle fY x₀ p₁ p₂ iY hiY₁ hiY₂ U₀ hU₀ (𝒱.inter σ))).hom (x σ) := rfl

omit [IsSeparated fY] in
theorem E_sub (n : ℕ) (x y : (strip fX fY p₁ p₂ hP.w U₀.1).cochain 𝒱 n) :
    E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ n (x - y)
      = E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ n x - E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ n
        y := by
  funext σ; simp only [E_apply, Pi.sub_apply]; exact map_sub _ _ _

omit [IsSeparated fY] in
theorem E_d (n : ℕ) (x : (strip fX fY p₁ p₂ hP.w U₀.1).cochain 𝒱 n) :
    E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ (n + 1) ((strip fX fY p₁ p₂ hP.w U₀.1).d 𝒱 n x)
      = (OModulePresheaf.unit fY).d 𝒱 n (E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ n x) := by
  funext σ
  rw [E_apply, OModulePresheaf.d_apply, OModulePresheaf.d_apply]
  erw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  erw [map_zsmul]
  erw [strip_res_apply, appLE_res, E_apply, OModulePresheaf.unit_res_apply (π := fY), res_appLE]
  rfl

theorem E_Φ_one_tmul (n : ℕ) (f : (OModulePresheaf.unit fY).cochain 𝒱 n) :
    E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ n
        (Φ fX fY p₁ p₂ hP 𝒱 U₀ n ((show (OModulePresheaf.unit fX).obj U₀.1 from (1 : Γ(X, U₀.1)))
          ⊗ₜ[k] f))
      = f := by
  funext σ
  rw [E_apply, Φ_tmul, map_one, one_mul]
  exact (congrArg (fun q : Γ(Y, 𝒱.inter σ) ⟶ Γ(Y, 𝒱.inter σ) => q.hom (f σ))
    (Scheme.Hom.appLE_comp_appLE iY p₂ (𝒱.inter σ)
      (p₁ ⁻¹ᵁ U₀.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) (𝒱.inter σ) inf_le_right
      (hEle fY x₀ p₁ p₂ iY hiY₁ hiY₂ U₀ hU₀ (𝒱.inter σ)))).trans
    ((appLE_of_eq_id _ hiY₂ _ le_rfl (f σ)).trans (res_self _ _))

end Eval

end G5Body

namespace G5Body

section YRes
variable {Y : Scheme.{u}}
theorem resY_res {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h₁).op).hom ((Y.presheaf.map (homOfLE h₂).op).hom x)
      = (Y.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
end YRes

section Assembly

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
  (𝒱 : Y.OrderedAffineCover)
  (r : (OModulePresheaf.unit fY).cochain 𝒱 1 →ₗ[k]
    HH ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1))
  {Λ : Type u} (bH : Module.Basis Λ k (HH ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit
    fY).d 𝒱 1)))
  (e : ∀ (U : X.affineOpens) (σ : 𝒱.Idx 1), Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))

/-- The tensor cochain corresponding to the supplied strip cocycle. -/
noncomputable def ζ (U : X.affineOpens) :
    (OModulePresheaf.unit fX).obj U.1 ⊗[k] (OModulePresheaf.unit fY).cochain 𝒱 1 :=
  (Φ fX fY p₁ p₂ hP 𝒱 U 1).symm (e U)

theorem Φ_ζ (U : X.affineOpens) : Φ fX fY p₁ p₂ hP 𝒱 U 1 (ζ fX fY p₁ p₂ hP 𝒱 e U) = e U :=
  LinearEquiv.apply_symm_apply _ _

/-- The tensor cohomology class of the supplied strip cocycle. -/
noncomputable def mcl (U : X.affineOpens) :
    (OModulePresheaf.unit fX).obj U.1 ⊗[k] HH ((OModulePresheaf.unit fY).d 𝒱 0)
      ((OModulePresheaf.unit fY).d 𝒱 1) :=
  cl _ _ r _ (ζ fX fY p₁ p₂ hP 𝒱 e U)

/-- A basis coordinate of the tensor cohomology class. -/
noncomputable def acoord (U : X.affineOpens) (l : Λ) : (OModulePresheaf.unit fX).obj U.1 :=
  coord bH _ (mcl fX fY p₁ p₂ hP 𝒱 r e U) l

theorem lTensor_d_ζ (U : X.affineOpens)
    (heU : ∀ ρ : 𝒱.Idx (1 + 1),
      ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
            ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom
              (e U (𝒱.face ρ j)) = 0) :
    LinearMap.lTensor _ ((OModulePresheaf.unit fY).d 𝒱 1) (ζ fX fY p₁ p₂ hP 𝒱 e U) = 0 := by
  apply (Φ fX fY p₁ p₂ hP 𝒱 U 2).injective
  rw [Φ_lTensor_d, Φ_ζ, map_zero]
  funext ρ
  rw [OModulePresheaf.d_apply (strip fX fY p₁ p₂ hP.w U.1) 𝒱 1 (e U) ρ,
    Pi.zero_apply]
  exact heU ρ

theorem res_acoord (hr : r ∘ₗ (ZZ _).subtype = (BB ((OModulePresheaf.unit fY).d 𝒱 0) _).mkQ)
    {U U' : X.affineOpens} (hle : U'.1 ≤ U.1)
    (g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i))
    (hg : ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          ((TopologicalSpace.Opens.map p₁.base).monotone (hle)) : p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤
            p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e U σ) - e U' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U'.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom
                (g (𝒱.face σ j)))
    (l : Λ) :
    (OModulePresheaf.unit fX).res hle (acoord fX fY p₁ p₂ hP 𝒱 r bH e U l)
      = acoord fX fY p₁ p₂ hP 𝒱 r bH e U' l := by
  have hdd : (OModulePresheaf.unit fY).d 𝒱 1 ∘ₗ (OModulePresheaf.unit fY).d 𝒱 0 = 0 :=
    AlgebraicGeometry.OModulePresheaf.Leray.d_d _ 𝒱 0
  have hw : TensorProduct.map ((OModulePresheaf.unit fX).res hle) LinearMap.id (ζ fX fY p₁ p₂ hP 𝒱
    e U)
      = ζ fX fY p₁ p₂ hP 𝒱 e U'
        + LinearMap.lTensor _ ((OModulePresheaf.unit fY).d 𝒱 0) ((Φ fX fY p₁ p₂ hP 𝒱 U' 0).symm g)
          := by
    apply (Φ fX fY p₁ p₂ hP 𝒱 U' 1).injective
    rw [← resS_Φ, Φ_ζ, map_add, Φ_ζ, Φ_lTensor_d]
    rw [LinearEquiv.apply_symm_apply (Φ fX fY p₁ p₂ hP 𝒱 U' 0) g]
    funext σ
    change _ = (show (strip fX fY p₁ p₂ hP.w U'.1).obj (𝒱.inter σ) from e U' σ)
      + (strip fX fY p₁ p₂ hP.w U'.1).d 𝒱 0 g σ
    exact sub_eq_iff_eq_add'.mp (hg σ)
  unfold acoord mcl
  rw [← coord_map, map_cl, hw, map_add, cl_lTensor_d0 _ _ r hr hdd, add_zero]

end Assembly

end G5Body

namespace G5Body

section Final

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
  (x₀ : Spec (CommRingCat.of k) ⟶ X)
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
  (iY : Y ⟶ P) (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
  (𝒱 : Y.OrderedAffineCover)
  (r : (OModulePresheaf.unit fY).cochain 𝒱 1 →ₗ[k]
    HH ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1))
  (hr : r ∘ₗ (ZZ _).subtype = (BB ((OModulePresheaf.unit fY).d 𝒱 0) _).mkQ)
  {Λ : Type u} (bH : Module.Basis Λ k (HH ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit
    fY).d 𝒱 1)))
  (e : ∀ (U : X.affineOpens) (σ : 𝒱.Idx 1), Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
  (c : Λ → k)
  (hc : ∀ (l : Λ) (U : X.affineOpens), acoord fX fY p₁ p₂ hP 𝒱 r bH e U l
    = (fX.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c l)))
  (U₀ : X.affineOpens) (hU₀ : x₀ ⁻¹ᵁ U₀.1 = ⊤)

include hr hc hU₀ hiY₁ hiY₂

theorem c_eq_zero
    (hzU₀ : LinearMap.lTensor _ ((OModulePresheaf.unit fY).d 𝒱 1) (ζ fX fY p₁ p₂ hP 𝒱 e U₀) = 0)
    (g : ∀ i : 𝒱.Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U₀.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i)))
    (hg : ∀ σ : 𝒱.Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U₀.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).hom (e U₀ σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone
              (inf_le_inf_left (p₁ ⁻¹ᵁ U₀.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ
                j))))).op).hom (g (𝒱.face σ j)))
    (l : Λ) : c l = 0 := by
  classical
  have hdd : (OModulePresheaf.unit fY).d 𝒱 1 ∘ₗ (OModulePresheaf.unit fY).d 𝒱 0 = 0 :=
    AlgebraicGeometry.OModulePresheaf.Leray.d_d _ 𝒱 0
  have : Nontrivial Γ(Spec (CommRingCat.of k), x₀ ⁻¹ᵁ U₀.1) := by rw [hU₀]; infer_instance
  have : Nontrivial Γ(X, U₀.1) := RingHom.domain_nontrivial (x₀.app U₀.1).hom
  have hinj : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appLE ⊤ U₀.1 le_top).hom :=
    RingHom.injective _
  have hc0 : ∀ l, acoord fX fY p₁ p₂ hP 𝒱 r bH e U₀ l = 0 → c l = 0 := by
    intro l hl
    apply hinj
    rw [CommRingCat.comp_apply, ← hc l U₀, hl]
    exact (map_zero _).symm
  let f₀ : Λ →₀ k := Finsupp.onFinset (coord bH _ (mcl fX fY p₁ p₂ hP 𝒱 r e U₀)).support (fun l =>
    c l)
    (fun l hl => by
      by_contra h'
      exact hl (hc0 l (Finsupp.notMem_support_iff.mp h')))
  have hf₀ : ∀ l, f₀ l • (show (OModulePresheaf.unit fX).obj U₀.1 from (1 : Γ(X, U₀.1)))
      = acoord fX fY p₁ p₂ hP 𝒱 r bH e U₀ l := by
    intro l
    rw [Finsupp.onFinset_apply, hc l U₀]
    change (fX.appLE ⊤ U₀.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c l)) * 1 = _
    rw [mul_one]
  have hm₀ : mcl fX fY p₁ p₂ hP 𝒱 r e U₀
      = (show (OModulePresheaf.unit fX).obj U₀.1 from (1 : Γ(X, U₀.1))) ⊗ₜ[k] bH.repr.symm f₀ := by
    apply (coord bH _).injective
    ext l
    rw [coord_tmul, LinearEquiv.apply_symm_apply, hf₀]
    rfl
  obtain ⟨z₀, hz₀⟩ := Submodule.mkQ_surjective
    (BB ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1)) (bH.repr.symm f₀)
  have hcl0 : cl ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1) r _
      (ζ fX fY p₁ p₂ hP 𝒱 e U₀ - (show (OModulePresheaf.unit fX).obj U₀.1 from (1 : Γ(X, U₀.1)))
        ⊗ₜ[k] z₀.1) = 0 := by
    rw [map_sub, cl_tmul_of_mem _ _ r hr _ _ z₀.1 z₀.2]
    change mcl fX fY p₁ p₂ hP 𝒱 r e U₀ - _ = 0
    rw [hm₀, ← hz₀, sub_eq_zero]
  have hz0 : LinearMap.lTensor _ ((OModulePresheaf.unit fY).d 𝒱 1)
      (ζ fX fY p₁ p₂ hP 𝒱 e U₀ - (show (OModulePresheaf.unit fX).obj U₀.1 from (1 : Γ(X, U₀.1)))
        ⊗ₜ[k] z₀.1) = 0 := by
    rw [map_sub, hzU₀, LinearMap.lTensor_tmul, LinearMap.mem_ker.mp z₀.2, TensorProduct.tmul_zero,
      sub_zero]
  obtain ⟨w₀, hw₀⟩ := exists_of_cl_eq_zero _ _ r hr hdd _ _ hz0 hcl0
  let ĝ : (OModulePresheaf.unit fY).cochain 𝒱 0 := fun i =>
    (Y.presheaf.map (homOfLE (hEle fY x₀ p₁ p₂ iY hiY₁ hiY₂ U₀ hU₀ (𝒱.inter i))).op).hom (g i)
  have hE : E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ 1 (e U₀) = (OModulePresheaf.unit fY).d 𝒱 0 ĝ
    := by
    funext σ
    rw [E_apply fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ 1 (e U₀) σ,
      Scheme.Hom.appLE, CommRingCat.comp_apply, hg σ, map_sum, OModulePresheaf.d_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, resY_res, OModulePresheaf.unit_res_apply, resY_res]
    rfl
  have hkey : z₀.1 = (OModulePresheaf.unit fY).d 𝒱 0
      (ĝ - E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ 0 (Φ fX fY p₁ p₂ hP 𝒱 U₀ 0 w₀)) := by
    have h1 := congrArg (Φ fX fY p₁ p₂ hP 𝒱 U₀ 1) hw₀
    rw [Φ_lTensor_d, map_sub, Φ_ζ] at h1
    have h2 := congrArg (E fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 U₀ hU₀ 1) h1
    rw [E_d] at h2
    erw [E_sub, hE, E_Φ_one_tmul] at h2
    rw [map_sub, h2, sub_sub_cancel]
  have hB : z₀ ∈ BB ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1) := ⟨_,
    hkey.symm⟩
  have hh₀ : bH.repr.symm f₀ = 0 := by rw [← hz₀]; exact (Submodule.Quotient.mk_eq_zero _).mpr hB
  have hf₀0 : f₀ = 0 := by
    have : bH.repr (bH.repr.symm f₀) = f₀ := LinearEquiv.apply_symm_apply _ _
    rw [← this, hh₀, map_zero]
  have : f₀ l = c l := Finsupp.onFinset_apply
  rw [← this, hf₀0, Finsupp.zero_apply]

end Final

end G5Body

namespace G5Body

theorem main
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (_hx₀ : x₀ ≫ fX = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iY : Y ⟶ P) (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒱 : Y.OrderedAffineCover)
    (e : ∀ (U : X.affineOpens) (σ : 𝒱.Idx 1), Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (he : ∀ U : X.affineOpens, ∀ ρ : 𝒱.Idx (1 + 1),
      ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
            ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom
              (e U (𝒱.face ρ j)) = 0)
    (hcompat : ∀ (U U' : X.affineOpens) (hle : U'.1 ≤ U.1),
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          ((TopologicalSpace.Opens.map p₁.base).monotone (hle)) : p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤
            p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e U σ) - e U' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U'.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom
                (g (𝒱.face σ j)))
    (hslice : ∀ U : X.affineOpens, x₀ ⁻¹ᵁ U.1 = ⊤ →
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i)),
      ∀ σ : 𝒱.Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).hom (e U σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone
              (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ
                j))))).op).hom (g (𝒱.face σ j))) :
    ∀ U : X.affineOpens, ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), e U σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom
                (g (𝒱.face σ j))  := by
  classical
  obtain ⟨r, hr⟩ := exists_r ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1)
  have hdd : (OModulePresheaf.unit fY).d 𝒱 1 ∘ₗ (OModulePresheaf.unit fY).d 𝒱 0 = 0 :=
    AlgebraicGeometry.OModulePresheaf.Leray.d_d _ 𝒱 0
  let bH := Module.Free.chooseBasis k
    (HH ((OModulePresheaf.unit fY).d 𝒱 0) ((OModulePresheaf.unit fY).d 𝒱 1))
  have hz : ∀ U : X.affineOpens,
      LinearMap.lTensor _ ((OModulePresheaf.unit fY).d 𝒱 1) (ζ fX fY p₁ p₂ hP 𝒱 e U) = 0 :=
    fun U => lTensor_d_ζ fX fY p₁ p₂ hP 𝒱 e U (he U)
  have hcoord : ∀ (U U' : X.affineOpens) (hle : U'.1 ≤ U.1) (l : _),
      (OModulePresheaf.unit fX).res hle (acoord fX fY p₁ p₂ hP 𝒱 r bH e U l)
        = acoord fX fY p₁ p₂ hP 𝒱 r bH e U' l := by
    intro U U' hle l
    obtain ⟨g, hg⟩ := hcompat U U' hle
    exact res_acoord fX fY p₁ p₂ hP 𝒱 r bH e hr hle g hg l
  have hconst : ∀ l, ∃ c : k, ∀ U : X.affineOpens, acoord fX fY p₁ p₂ hP 𝒱 r bH e U l
      = (fX.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) :=
    fun l => AlgebraicGeometry.Scheme.exists_forall_eq_appLE_of_forall_map_eq_of_bijective fX hX
      (fun U => acoord fX fY p₁ p₂ hP 𝒱 r bH e U l) (fun U U' h => hcoord U U' h l)
  choose c hc using hconst
  let pt : ↥(Spec (CommRingCat.of k)) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨U₀', hU₀'aff, hmem, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens X))
      (show x₀.base pt ∈ (⊤ : X.Opens) from trivial)
  have hU₀ : x₀ ⁻¹ᵁ U₀' = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have : y = pt := Subsingleton.elim _ _
    rw [this]; exact hmem
  obtain ⟨g, hg⟩ := hslice ⟨U₀', hU₀'aff⟩ hU₀
  have hall : ∀ l, c l = 0 :=
    c_eq_zero fX fY x₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 r hr bH e c hc ⟨U₀', hU₀'aff⟩ hU₀ (hz _) g hg
  intro U
  have hmU : mcl fX fY p₁ p₂ hP 𝒱 r e U = 0 := by
    apply (coord bH _).injective
    ext l
    change acoord fX fY p₁ p₂ hP 𝒱 r bH e U l = _
    rw [map_zero, Finsupp.zero_apply, hc l U, hall l, map_zero, map_zero]
    rfl
  obtain ⟨w, hw⟩ := exists_of_cl_eq_zero _ _ r hr hdd _ (ζ fX fY p₁ p₂ hP 𝒱 e U) (hz U) hmU
  refine ⟨Φ fX fY p₁ p₂ hP 𝒱 U 0 w, fun σ => ?_⟩
  have h1 := congrArg (Φ fX fY p₁ p₂ hP 𝒱 U 1) hw
  rw [Φ_lTensor_d, Φ_ζ] at h1
  rw [← h1, OModulePresheaf.d_apply]
  rfl

end G5Body

end AlgebraicCurves.Cohomology.Sheaves.Proofs.StripAffineAssembly

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
open AlgebraicCurves.Cohomology.Sheaves.Proofs.StripAffineAssembly

universe u

theorem exists_strip_eq_sum_of_forall_isAffineOpen_of_slice_of_bijective
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iY : Y ⟶ P) (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒱 : Y.OrderedAffineCover)
    (e : ∀ (U : X.affineOpens) (σ : 𝒱.Idx 1), Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (he : ∀ U : X.affineOpens, ∀ ρ : 𝒱.Idx (1 + 1),
      ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
            ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom
              (e U (𝒱.face ρ j)) = 0)
    (hcompat : ∀ (U U' : X.affineOpens) (hle : U'.1 ≤ U.1),
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          ((TopologicalSpace.Opens.map p₁.base).monotone (hle)) : p₁ ⁻¹ᵁ U'.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤
            p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e U σ) - e U' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U'.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom
                (g (𝒱.face σ j)))
    (hslice : ∀ U : X.affineOpens, x₀ ⁻¹ᵁ U.1 = ⊤ →
      ∃ g : ∀ i : 𝒱.Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i)),
      ∀ σ : 𝒱.Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).hom (e U σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone
              (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ
                j))))).op).hom (g (𝒱.face σ j))) :
    ∀ U : X.affineOpens, ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U.1 ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), e U σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U.1)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom
                (g (𝒱.face σ j)) := by
  exact G5Body.main fX fY hX x₀ hx₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒱 e he hcompat hslice
end AlgebraicGeometry.OModulePresheaf
end ProofImplementation

attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
