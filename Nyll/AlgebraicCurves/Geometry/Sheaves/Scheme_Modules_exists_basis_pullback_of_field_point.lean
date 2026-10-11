/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_basis_pullback_of_field_point.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullback_locally_mem_span_unit

/-!
# Bases after pullback to a field-valued point

Local bases of a module give bases after pullback along a point valued in a field.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_basis_pullback_of_field_point

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace Ws14DG

namespace FieldPoint

/-- Restrict a module section to a smaller open subset. -/
noncomputable abbrev res {Z : Scheme.{u}} (M : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W) (s : Γ(M,
  W)) :
    Γ(M, W') :=
  M.presheaf.map (homOfLE h).op s

lemma res_res {Z : Scheme.{u}} (M : Z.Modules) {W₁ W₂ W₃ : Z.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂)
    (s : Γ(M, W₁)) : res M h₃₂ (res M h₂₁ s) = res M (h₃₂.trans h₂₁) s := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) s = _
  rw [← Functor.map_comp]
  rfl

lemma res_self {Z : Scheme.{u}} (M : Z.Modules) {W : Z.Opens} (h : W ≤ W) (s : Γ(M, W)) : res M h
  s = s := by
  change M.presheaf.map (homOfLE h).op s = s
  rw [Subsingleton.elim (homOfLE h) (𝟙 W), op_id, M.presheaf.map_id]
  rfl

lemma res_eq_map {Z : Scheme.{u}} (M : Z.Modules) {W' W : Z.Opens} (f : W' ⟶ W) (s : Γ(M, W)) :
    M.presheaf.map f.op s = res M f.le s := by
  rw [Subsingleton.elim f (homOfLE f.le)]

lemma res_smul {Z : Scheme.{u}} (M : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W) (r : Γ(Z, W)) (s :
  Γ(M, W)) :
    res M h (r • s) = Z.presheaf.map (homOfLE h).op r • res M h s :=
  Scheme.Modules.map_smul M (homOfLE h) r s

lemma res_add {Z : Scheme.{u}} (M : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W) (s t : Γ(M, W)) :
    res M h (s + t) = res M h s + res M h t := map_add _ s t

lemma res_sum {Z : Scheme.{u}} (M : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W) {ι : Type*} (T :
  Finset ι)
    (s : ι → Γ(M, W)) : res M h (∑ t ∈ T, s t) = ∑ t ∈ T, res M h (s t) := map_sum _ s T

lemma str_map_map {Z : Scheme.{u}} {A B C : Z.Opens} (h₁ : B ≤ A) (h₂ : C ≤ B) (h₃ : C ≤ A) (r :
  Γ(Z, A)) :
    Z.presheaf.map (homOfLE h₂).op (Z.presheaf.map (homOfLE h₁).op r) = Z.presheaf.map (homOfLE
      h₃).op r := by
  change (Z.presheaf.map (homOfLE h₁).op ≫ Z.presheaf.map (homOfLE h₂).op) r = _
  rw [← Functor.map_comp]
  rfl

lemma str_map_self {Z : Scheme.{u}} {A : Z.Opens} (h : A ≤ A) (r : Γ(Z, A)) :
    Z.presheaf.map (homOfLE h).op r = r := by
  rw [Subsingleton.elim (homOfLE h) (𝟙 A), op_id, Z.presheaf.map_id]
  rfl

variable {X : Scheme.{u}} {M : X.Modules} {n : ℕ} {U : X.Opens} (e : Fin n → Γ(M, U))
  (he : ∀ (W : X.Opens) (hW : W ≤ U), ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W),
    ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i))

/-- Choose the stipulated basis on a smaller open subset. -/
noncomputable def bas (W : X.Opens) (hW : W ≤ U) : Module.Basis (Fin n) Γ(X, W) Γ(M, W) :=
  (he W hW).choose

lemma bas_apply (W : X.Opens) (hW : W ≤ U) (i : Fin n) : bas e he W hW i = res M hW (e i) :=
  (he W hW).choose_spec i

lemma repr_res {W W' : X.Opens} (hW : W ≤ U) (h : W' ≤ W) (m : Γ(M, W)) (j : Fin n) :
    (bas e he W' (h.trans hW)).repr (res M h m) j =
      X.presheaf.map (homOfLE h).op ((bas e he W hW).repr m j) := by
  have hm : res M h m =
      ∑ k, X.presheaf.map (homOfLE h).op ((bas e he W hW).repr m k) • bas e he W' (h.trans hW) k
        := by
    conv_lhs => rw [← (bas e he W hW).sum_repr m]
    rw [res_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [res_smul, bas_apply, bas_apply, res_res]
  rw [hm, Module.Basis.repr_sum_self]

variable {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ X)
  (hs : s.base (IsLocalRing.closedPoint K) ∈ U)

lemma pt_eq (q : Spec (CommRingCat.of K)) : q = IsLocalRing.closedPoint K :=
  @Subsingleton.elim _ (inferInstanceAs (Subsingleton (PrimeSpectrum K))) _ _

include hs in
lemma preimage_le (W : X.Opens) : s ⁻¹ᵁ W ≤ s ⁻¹ᵁ (W ⊓ U) := by
  intro q hq
  obtain rfl := pt_eq (K := K) q
  exact ⟨hq, hs⟩

lemma le_of_mem {W₁ W₂ : (Spec (CommRingCat.of K)).Opens} (h : IsLocalRing.closedPoint K ∈ W₂) :
  W₁ ≤ W₂ := by
  intro q _
  obtain rfl := pt_eq (K := K) q
  exact h

/-- The module pulled back to the field-valued point. -/
noncomputable abbrev N : (Spec (CommRingCat.of K)).Modules := (Scheme.Modules.pullback s).obj M

/-- Map a section to the pullback using the adjunction unit. -/
noncomputable def eta (V : X.Opens) (m : Γ(M, V)) : Γ(N s (M := M), s ⁻¹ᵁ V) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction s).unit.app M).app V m

lemma eta_add (V : X.Opens) (m m' : Γ(M, V)) : eta s V (m + m') = eta s V m + eta s V m' :=
  map_add _ m m'

lemma eta_sum (V : X.Opens) {ι : Type*} (T : Finset ι) (f : ι → Γ(M, V)) :
    eta s V (∑ t ∈ T, f t) = ∑ t ∈ T, eta s V (f t) :=
  map_sum (((Scheme.Modules.pullbackPushforwardAdjunction s).unit.app M).app V).hom f T

lemma eta_smul (V : X.Opens) (r : Γ(X, V)) (m : Γ(M, V)) :
    eta s V (r • m) = s.app V r • eta s V m :=
  Scheme.Modules.Hom.app_smul _ r m

lemma res_eta {V V' : X.Opens} (h : V' ≤ V) (m : Γ(M, V)) :
    res (N s (M := M)) (s.preimage_mono h) (eta s V m) = eta s V' (res M h m) := by
  have hnat := ((Scheme.Modules.pullbackPushforwardAdjunction s).unit.app M).mapPresheaf.naturality
    (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hx
  rw [res_eq_map] at hx
  exact hx.symm

include he hs in
lemma span_eta_eq_top :
    ⊤ ≤ Submodule.span ((Spec (CommRingCat.of K)).presheaf.obj (op (s ⁻¹ᵁ U))) (Set.range fun k :
      Fin n => eta s U (e k)) := by
  intro y _
  obtain ⟨U', W', i, j, hU'U, hxW', hmem⟩ :=
    Scheme.Modules.pullback_locally_mem_span_unit s M (W := s ⁻¹ᵁ U) y (x :=
      IsLocalRing.closedPoint K) hs
      (U₀ := U) hs
  obtain rfl : W' = s ⁻¹ᵁ U := le_antisymm i (le_of_mem hxW')
  rw [show ((Scheme.Modules.pullback s).obj M).presheaf.map (homOfLE i).op y = y from res_self _
    i y] at hmem
  refine (Submodule.span_le.mpr ?_) hmem
  rintro _ ⟨m, rfl⟩
  have hm : m = ∑ k, (bas e he U' hU'U).repr m k • res M hU'U (e k) := by
    conv_lhs => rw [← (bas e he U' hU'U).sum_repr m]
    simp only [bas_apply]
  change res (N s (M := M)) j (eta s U' m) ∈ _
  rw [hm, eta_sum, res_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [eta_smul, res_smul, ← res_eta, res_res, res_self]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- Push the unit module on the field-valued point forward to the scheme. -/
noncomputable abbrev P : X.Modules :=
  (Scheme.Modules.pushforward s).obj (SheafOfModules.unit (Spec (CommRingCat.of K)).ringCatSheaf)

/-- Take a basis coordinate after restricting a section near the field-valued point. -/
noncomputable def kapFun (j : Fin n) (W : X.Opens) (m : Γ(M, W)) : Γ(Spec (CommRingCat.of K), s
  ⁻¹ᵁ W) :=
  (Spec (CommRingCat.of K)).presheaf.map (homOfLE (preimage_le s hs W)).op
    (s.app (W ⊓ U) ((bas e he (W ⊓ U) inf_le_right).repr (res M inf_le_left m) j))

lemma kapFun_add (j : Fin n) (W : X.Opens) (m m' : Γ(M, W)) :
    kapFun e he s hs j W (m + m') = kapFun e he s hs j W m + kapFun e he s hs j W m' := by
  simp only [kapFun, map_add, Finsupp.add_apply]

lemma kapFun_smul (j : Fin n) (W : X.Opens) (r : Γ(X, W)) (m : Γ(M, W)) :
    kapFun e he s hs j W (r • m) = s.app W r * kapFun e he s hs j W m := by
  simp only [kapFun, res_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  congr 1
  have hnat := ConcreteCategory.congr_hom (s.naturality (homOfLE (inf_le_left : W ⊓ U ≤ W)).op) r
  simp only [ConcreteCategory.comp_apply, Quiver.Hom.unop_op] at hnat
  rw [hnat]
  rw [Subsingleton.elim ((Opens.map s.base).map (homOfLE (inf_le_left : W ⊓ U ≤ W)))
    (homOfLE (s.preimage_mono (inf_le_left : W ⊓ U ≤ W)))]
  exact str_map_map _ _ le_rfl _ |>.trans (str_map_self _ _)

lemma kapFun_res (j : Fin n) {W W' : X.Opens} (h : W' ≤ W) (m : Γ(M, W)) :
    kapFun e he s hs j W' (res M h m) =
      (Spec (CommRingCat.of K)).presheaf.map (homOfLE (s.preimage_mono h)).op (kapFun e he s hs j
        W m) := by
  simp only [kapFun]
  have h' : W' ⊓ U ≤ W ⊓ U := inf_le_inf_right U h
  rw [res_res, show (inf_le_left : W' ⊓ U ≤ W').trans h = h'.trans inf_le_left from rfl, ←
    res_res M inf_le_left h',
    show bas e he (W' ⊓ U) inf_le_right = bas e he (W' ⊓ U) (h'.trans inf_le_right) from rfl,
    repr_res e he inf_le_right h']
  have hnat := ConcreteCategory.congr_hom (s.naturality (homOfLE h').op)
    ((bas e he (W ⊓ U) inf_le_right).repr (res M inf_le_left m) j)
  simp only [ConcreteCategory.comp_apply, Quiver.Hom.unop_op] at hnat
  rw [hnat, Subsingleton.elim ((Opens.map s.base).map (homOfLE h')) (homOfLE (s.preimage_mono h'))]
  have h₃ : s ⁻¹ᵁ W' ≤ s ⁻¹ᵁ (W ⊓ U) := (s.preimage_mono h).trans (preimage_le s hs W)
  rw [str_map_map _ _ h₃, str_map_map _ _ h₃]

/-- View a structure sheaf section as a section of the pushed-forward unit module. -/
def toP (W : X.Opens) (t : Γ(Spec (CommRingCat.of K), s ⁻¹ᵁ W)) : Γ(P s, W) := t

lemma toP_add (W : X.Opens) (t t' : Γ(Spec (CommRingCat.of K), s ⁻¹ᵁ W)) :
    toP s W (t + t') = toP s W t + toP s W t' := rfl

lemma smul_toP (W : X.Opens) (r : Γ(X, W)) (t : Γ(Spec (CommRingCat.of K), s ⁻¹ᵁ W)) :
    r • toP s W t = toP s W (s.app W r * t) := rfl

lemma map_toP {W W' : X.Opens} (i : W' ⟶ W) (t : Γ(Spec (CommRingCat.of K), s ⁻¹ᵁ W)) :
    (P s).presheaf.map i.op (toP s W t) =
      toP s W' ((Spec (CommRingCat.of K)).presheaf.map ((Opens.map s.base).map i).op t) := rfl

/-- The natural map of abelian presheaves given by a basis coordinate. -/
noncomputable def kapAb (j : Fin n) : M.presheaf ⟶ (P s).presheaf where
  app W := AddCommGrpCat.ofHom (X := Γ(M, W.unop)) (Y := Γ(P s, W.unop))
    { toFun := fun m => toP s W.unop (kapFun e he s hs j W.unop m)
      map_zero' := by
        have h := kapFun_add e he s hs j W.unop 0 0
        rw [add_zero] at h
        rw [show kapFun e he s hs j W.unop 0 = 0 from left_eq_add.mp h]
        rfl
      map_add' := fun m m' => by rw [kapFun_add]; rfl }
  naturality W W' g := by
    ext m
    obtain ⟨g, rfl⟩ : ∃ g' : W'.unop ⟶ W.unop, g = g'.op := ⟨g.unop, rfl⟩
    change toP s W'.unop (kapFun e he s hs j W'.unop (M.presheaf.map g.op m)) =
      (P s).presheaf.map g.op (toP s W.unop (kapFun e he s hs j W.unop m))
    rw [res_eq_map, kapFun_res, map_toP,
      Subsingleton.elim ((Opens.map s.base).map g) (homOfLE (s.preimage_mono g.le))]

/-- The module sheaf morphism given by a basis coordinate. -/
noncomputable def kap (j : Fin n) : M ⟶ P s :=
  ⟨PresheafOfModules.homMk (kapAb e he s hs j) (fun W r m => by
    obtain ⟨W, rfl⟩ : ∃ W' : X.Opens, W = op W' := ⟨W.unop, rfl⟩
    exact (congrArg (toP s W) (kapFun_smul e he s hs j W r m)).trans (smul_toP s W r _).symm)⟩

lemma kap_app (j : Fin n) (W : X.Opens) (m : Γ(M, W)) :
    (kap e he s hs j).app W m = toP s W (kapFun e he s hs j W m) := rfl

/-- The adjoint basis-coordinate morphism on the pullback module. -/
noncomputable def kapSharp (j : Fin n) :
    Scheme.Modules.Hom (X := Spec (CommRingCat.of K)) (N s (M := M))
      (SheafOfModules.unit (Spec (CommRingCat.of K)).ringCatSheaf :
        (Spec (CommRingCat.of K)).Modules) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction s).homEquiv M _).symm (kap e he s hs j)

lemma kapSharp_eta (j : Fin n) (V : X.Opens) (m : Γ(M, V)) :
    (kapSharp e he s hs j).app (s ⁻¹ᵁ V) (eta s V m) = (kap e he s hs j).app V m := by
  have h : @Eq (Scheme.Modules.Hom (X := X) M (P s))
      (kap e he s hs j)
      ((Scheme.Modules.pullbackPushforwardAdjunction s).unit.app M ≫
        (Scheme.Modules.pushforward s).map (kapSharp e he s hs j)) :=
    (((Scheme.Modules.pullbackPushforwardAdjunction s).homEquiv M
      (SheafOfModules.unit (Spec (CommRingCat.of K)).ringCatSheaf :
        (Spec (CommRingCat.of K)).Modules)).apply_symm_apply (kap e he s hs j)).symm.trans
      ((Scheme.Modules.pullbackPushforwardAdjunction s).homEquiv_unit (X := M)
        (Y := (SheafOfModules.unit (Spec (CommRingCat.of K)).ringCatSheaf :
          (Spec (CommRingCat.of K)).Modules)) (f := kapSharp e he s hs j))
  exact (congrArg (fun φ : Scheme.Modules.Hom (X := X) M (P s) =>
    (φ.app V).hom m) h).symm

lemma kapFun_e (j i : Fin n) :
    kapFun e he s hs j U (e i) = if i = j then 1 else 0 := by
  simp only [kapFun]
  rw [← bas_apply e he, Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp only [map_one, map_zero]

include he hs in
lemma linearIndependent_eta :
    LinearIndependent ((Spec (CommRingCat.of K)).presheaf.obj (op (s ⁻¹ᵁ U))) (fun k : Fin n =>
      eta s U (e k)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let q : Γ(N s (M := M), s ⁻¹ᵁ U) →ₗ[Γ(Spec (CommRingCat.of K), s ⁻¹ᵁ U)]
      Γ(Spec (CommRingCat.of K), s ⁻¹ᵁ U) :=
    ((kapSharp e he s hs j).val.app (op (s ⁻¹ᵁ U))).hom
  have hcoeff (i : Fin n) : q (eta s U (e i)) = if i = j then 1 else 0 :=
    (kapSharp_eta e he s hs j U (e i)).trans
      ((kap_app e he s hs j U (e i)).trans
        (congrArg (toP s U) (kapFun_e e he s hs j i)))
  have hsum : (∑ i, c i * (if i = j then 1 else 0)) = 0 := by
    calc
      _ = ∑ i, q (c i • eta s U (e i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact ((q.map_smul (c i) (eta s U (e i))).trans
          (congrArg (fun z : Γ(Spec (CommRingCat.of K), s ⁻¹ᵁ U) => c i • z)
            (hcoeff i))).symm
      _ = q (∑ i, c i • eta s U (e i)) := (map_sum q _ Finset.univ).symm
      _ = q 0 := congrArg q hc
      _ = 0 := map_zero q
  have hsum_eq : (∑ i, c i * (if i = j then 1 else 0)) = c j := by
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left rfl, mul_one]
    · intro i _ hij
      rw [ite_eq_right hij, mul_zero]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  exact hsum_eq.symm.trans hsum

/-- The basis formed by the images of the local basis under the adjunction unit. -/
noncomputable def basisEta :
    Module.Basis (Fin n) ((Spec (CommRingCat.of K)).presheaf.obj (op (s ⁻¹ᵁ U))) Γ(N s (M := M),
      s ⁻¹ᵁ U) :=
  Module.Basis.mk (linearIndependent_eta e he s hs) (span_eta_eq_top e he s hs)

lemma basisEta_apply (i : Fin n) : basisEta e he s hs i = eta s U (e i) :=
  Module.Basis.mk_apply _ _ i

end FieldPoint

end Ws14DG

theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_basis_pullback_of_field_point
    {X : Scheme.{u}} {M : X.Modules} {n : ℕ} {U : X.Opens} (e : Fin n → Γ(M, U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U), ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W),
      ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i))
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ X)
    (hs : s.base (IsLocalRing.closedPoint K) ∈ U) :
    ∃ b : Module.Basis (Fin n) Γ(Spec (CommRingCat.of K), s ⁻¹ᵁ U)
        Γ((Scheme.Modules.pullback s).obj M, s ⁻¹ᵁ U),
      ∀ i, b i = ((Scheme.Modules.pullbackPushforwardAdjunction s).unit.app M).app U (e i) :=
  ⟨Ws14DG.FieldPoint.basisEta e he s hs, Ws14DG.FieldPoint.basisEta_apply e he s hs⟩
end Scheme_Modules_exists_basis_pullback_of_field_point
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
