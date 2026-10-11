/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Polarisation_locIsoOnBase_faces_pullback_cube_iff_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Product
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesPullbackMonoidalV2
import Nyll.AlgebraicCurves.Geometry.Picard.Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Nyll.AlgebraicCurves.Geometry.Picard.Polarisation_LocIsoOnBase_equivalence

/-!
# Polarisation loc Iso On Base faces pullback cube iff of is Pullback
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs
namespace Polarisation_locIsoOnBase_faces_pullback_cube_iff_of_isPullback


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Polarisation
open _root_.AlgebraicGeometry.RelPicard


noncomputable section

namespace FBC

open AlgebraicGeometry.Scheme.Modules

section lociso
variable {S' : Type} [CommRing S'] {X Y Z : Scheme.{0}}

theorem locIsoOnBase_of_iso (q : X ⟶ Spec (CommRingCat.of S')) {M M' : X.Modules} (e : M ≅ M') :
  LocIsoOnBase q M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

theorem locIsoOnBase_unit_congr (q : X ⟶ Spec (CommRingCat.of S')) {M M' : X.Modules} (e : M ≅ M') :
    LocIsoOnBase q M (𝟙_ _) ↔ LocIsoOnBase q M' (𝟙_ _) :=
  ⟨fun h => (LocIsoOnBase.equivalence q).trans (locIsoOnBase_of_iso q e.symm) h,
   fun h => (LocIsoOnBase.equivalence q).trans (locIsoOnBase_of_iso q e) h⟩

/-- The comparison isomorphism between iterated pullback and pullback along an equal composite. -/
def pullbackCompCongr {φ : X ⟶ Y} {ψ : Y ⟶ Z} {χ : X ⟶ Z} (h : φ ≫ ψ = χ) (M : Z.Modules) :
    (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback ψ).obj M) ≅ (Scheme.Modules.pullback
      χ).obj M :=
  (pullbackComp φ ψ).app M ≪≫ (pullbackCongr h).app M

theorem locIsoOnBase_unit_iff_of_iso (e : X ≅ Y) (qX : X ⟶ Spec (CommRingCat.of S')) (qY : Y ⟶ Spec
  (CommRingCat.of S'))
    (he : e.hom ≫ qY = qX) (K : Y.Modules) :
    LocIsoOnBase qX ((Scheme.Modules.pullback e.hom).obj K) (𝟙_ _) ↔ LocIsoOnBase qY K (𝟙_ _) := by
  constructor
  · intro h
    have h' := LocIsoOnBase.pullback_of_comp_eq qY e.inv (𝟙 _)
      (by rw [Category.comp_id, ← he, e.inv_hom_id_assoc]) h
    have eK : (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj K) ≅ K :=
      pullbackCompCongr e.inv_hom_id K ≪≫ (pullbackId _).app K
    exact (LocIsoOnBase.equivalence qY).trans ((LocIsoOnBase.equivalence qY).trans
      (locIsoOnBase_of_iso qY eK.symm) h')
      (locIsoOnBase_of_iso qY (pullbackTensorUnitObjIso e.inv))
  · intro h
    have h' := LocIsoOnBase.pullback_of_comp_eq qX e.hom (𝟙 _) (by rw [Category.comp_id, he]) h
    exact (LocIsoOnBase.equivalence qX).trans h' (locIsoOnBase_of_iso qX (pullbackTensorUnitObjIso
      e.hom))

end lociso

section square

variable {S₁ : Type} [CommRing S₁] {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} (L₁ :
  RelativeGroupLaw S₁ f₁)
  {S : Type} [CommRing S] (φ : S₁ →+* S) {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L :
    RelativeGroupLaw S f)
  (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
  (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
      ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)

theorem one_coe_eq {R : Type} [CommRing R] {B : Scheme.{0}} {g : B ⟶ Spec (CommRingCat.of R)} (G :
  RelativeGroupLaw R g)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : (G.one t).1 = t ≫ (G.one (𝟙 _)).1 :=
  (congrArg Subtype.val (G.one_natural (𝟙 _) t t (Category.comp_id t))).symm
include hLa in
theorem one_comp_a {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 ≫ a = (L₁.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
  let E : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) f₁ :=
    ⟨(L.one t).1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, (L.one t).2]⟩
  have hE : L₁.mul _ E E = E := by
    have h := hLa T t (L.one t) (L.one t)
    rw [L.one_mul] at h
    exact (Subtype.ext h).symm
  have : E = L₁.one _ := by
    calc E = L₁.mul _ (L₁.one _) E := (L₁.one_mul _ E).symm
    _ = L₁.mul _ (L₁.mul _ (L₁.inv _ E) E) E := by rw [L₁.inv_mul_cancel]
    _ = L₁.mul _ (L₁.inv _ E) (L₁.mul _ E E) := L₁.mul_assoc _ _ _ _
    _ = L₁.mul _ (L₁.inv _ E) E := by rw [hE]
    _ = L₁.one _ := L₁.inv_mul_cancel _ E
  exact congrArg Subtype.val this

/-- The morphism between the double fibre products induced by the given base change. -/
def aa : pullback f f ⟶ pullback f₁ f₁ :=
  pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm

@[scoped simp] theorem aa_fst : aa φ a ha ≫ pullback.fst f₁ f₁ = pullback.fst f f ≫ a :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem aa_snd : aa φ a ha ≫ pullback.snd f₁ f₁ = pullback.snd f f ≫ a :=
  pullback.lift_snd _ _ _

theorem aa_prodStr : aa φ a ha ≫ prodStr f₁ f₁ = prodStr f f ≫ Spec.map (CommRingCat.ofHom φ) := by
  change aa φ a ha ≫ pullback.fst f₁ f₁ ≫ f₁ = (pullback.fst f f ≫ f) ≫ _
  rw [← Category.assoc, aa_fst, Category.assoc, Category.assoc, ha.w]

/-- The morphism between the triple fibre products induced by the given base change. -/
def aaa : pullback (prodStr f f) f ⟶ pullback (prodStr f₁ f₁) f₁ :=
  pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm
              ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            change (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1,
              Category.assoc, ha.w])
          ha.w.symm

@[scoped simp] theorem aaa_fst : aaa φ a ha ≫ pullback.fst (prodStr f₁ f₁) f₁ = pullback.fst
  (prodStr f f) f ≫ aa φ a ha :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem aaa_snd : aaa φ a ha ≫ pullback.snd (prodStr f₁ f₁) f₁ = pullback.snd
  (prodStr f f) f ≫ a :=
  pullback.lift_snd _ _ _

/--
The isomorphism identifying the double fibre product with the base change of the original double
fibre product.
-/
def θ : pullback f f ≅ pullback (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)) where
  hom := pullback.lift (aa φ a ha) (prodStr f f) (aa_prodStr φ a ha)
  inv := pullback.lift
    (ha.lift (pullback.fst _ _ ≫ pullback.fst f₁ f₁) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition))
    (ha.lift (pullback.fst _ _ ≫ pullback.snd f₁ f₁) (pullback.snd _ _)
      (by rw [Category.assoc, pullback_snd_comp_eq_prodStr]; exact pullback.condition))
    (by rw [IsPullback.lift_snd, IsPullback.lift_snd])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      apply ha.hom_ext
      · rw [Category.assoc, IsPullback.lift_fst, pullback.lift_fst_assoc, aa_fst]
      · rw [Category.assoc, IsPullback.lift_snd, pullback.lift_snd]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      apply ha.hom_ext
      · rw [Category.assoc, IsPullback.lift_fst, pullback.lift_fst_assoc, aa_snd]
      · rw [Category.assoc, IsPullback.lift_snd, pullback.lift_snd]; exact pullback.condition (f :=
          f) (g := f)
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, aa_fst, pullback.lift_fst_assoc, IsPullback.lift_fst]
      · rw [Category.assoc, aa_snd, pullback.lift_snd_assoc, IsPullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      change _ ≫ pullback.fst f f ≫ f = _
      rw [pullback.lift_fst_assoc, IsPullback.lift_snd]

theorem θ_hom_fst : (θ φ a ha).hom ≫ pullback.fst _ _ = aa φ a ha := pullback.lift_fst _ _ _
theorem θ_hom_snd : (θ φ a ha).hom ≫ pullback.snd _ _ = prodStr f f := pullback.lift_snd _ _ _
include hLa in
theorem one_prodStr_comp_a : (L.one (prodStr f f)).1 ≫ a = aa φ a ha ≫ (L₁.one (prodStr f₁ f₁)).1
  := by
  rw [one_comp_a L₁ φ L a ha hLa, one_coe_eq L₁ (prodStr f f ≫ _), one_coe_eq L₁ (prodStr f₁ f₁), ←
    Category.assoc,
    aa_prodStr]

end square

section faces

variable {S₁ : Type} [CommRing S₁] {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} (L₁ :
  RelativeGroupLaw S₁ f₁)
  {S : Type} [CommRing S] (φ : S₁ →+* S) {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L :
    RelativeGroupLaw S f)
  (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
  (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
      ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)

/-- The first face map inserting the identity section as the first coordinate. -/
def F1 {R : Type} [CommRing R] {B : Scheme.{0}} {g : B ⟶ Spec (CommRingCat.of R)} (G :
  RelativeGroupLaw R g) :
    pullback g g ⟶ pullback (prodStr g g) g :=
  pullback.lift
    (pullback.lift (G.one (prodStr g g)).1 (pullback.fst g g) (by rw [(G.one _).2]))
    (pullback.snd g g)
    (by rw [pullback.lift_fst_assoc, (G.one _).2]; exact pullback.condition)

/-- The second face map inserting the identity section as the second coordinate. -/
def F2 {R : Type} [CommRing R] {B : Scheme.{0}} {g : B ⟶ Spec (CommRingCat.of R)} (G :
  RelativeGroupLaw R g) :
    pullback g g ⟶ pullback (prodStr g g) g :=
  pullback.lift
    (pullback.lift (pullback.fst g g) (G.one (prodStr g g)).1 (by rw [(G.one _).2]))
    (pullback.snd g g)
    (by rw [pullback.lift_fst_assoc]; exact pullback.condition)

/-- The third face map inserting the identity section as the third coordinate. -/
def F3 {R : Type} [CommRing R] {B : Scheme.{0}} {g : B ⟶ Spec (CommRingCat.of R)} (G :
  RelativeGroupLaw R g) :
    pullback g g ⟶ pullback (prodStr g g) g :=
  pullback.lift (𝟙 _) (G.one (prodStr g g)).1 (by rw [Category.id_comp, (G.one _).2])
include hLa in
theorem F1_comp : F1 L ≫ aaa φ a ha = aa φ a ha ≫ F1 L₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc, aaa_fst, Category.assoc]
    unfold F1
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, aa_fst, pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst,
        one_prodStr_comp_a L₁ φ L a ha hLa]
    · rw [Category.assoc, aa_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
        aa_fst]
  · rw [Category.assoc, aaa_snd, Category.assoc]
    unfold F1
    rw [pullback.lift_snd_assoc, pullback.lift_snd, aa_snd]
include hLa in
theorem F2_comp : F2 L ≫ aaa φ a ha = aa φ a ha ≫ F2 L₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc, aaa_fst, Category.assoc]
    unfold F2
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, aa_fst, pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst,
        aa_fst]
    · rw [Category.assoc, aa_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
        one_prodStr_comp_a L₁ φ L a ha hLa]
  · rw [Category.assoc, aaa_snd, Category.assoc]
    unfold F2
    rw [pullback.lift_snd_assoc, pullback.lift_snd, aa_snd]
include hLa in
theorem F3_comp : F3 L ≫ aaa φ a ha = aa φ a ha ≫ F3 L₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc, aaa_fst, Category.assoc]
    unfold F3
    rw [pullback.lift_fst_assoc, pullback.lift_fst, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, aaa_snd, Category.assoc]
    unfold F3
    rw [pullback.lift_snd_assoc, pullback.lift_snd, one_prodStr_comp_a L₁ φ L a ha hLa]

/-- The pullback comparison for a face map compatible with the base-change morphisms. -/
def faceIso {F : pullback f f ⟶ pullback (prodStr f f) f} {F₁ : pullback f₁ f₁ ⟶ pullback (prodStr
  f₁ f₁) f₁}
    (hF : F ≫ aaa φ a ha = aa φ a ha ≫ F₁) (N : (pullback (prodStr f₁ f₁) f₁).Modules) :
    (Scheme.Modules.pullback F).obj ((Scheme.Modules.pullback (aaa φ a ha)).obj N) ≅
      (Scheme.Modules.pullback (θ φ a ha).hom).obj
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom
          φ)))).obj
          ((Scheme.Modules.pullback F₁).obj N)) :=
  pullbackCompCongr hF N ≪≫ (pullbackCompCongr rfl N).symm ≪≫ (pullbackCompCongr (θ_hom_fst φ a ha)
    _).symm
omit hLa in
theorem face_iff {F : pullback f f ⟶ pullback (prodStr f f) f} {F₁ : pullback f₁ f₁ ⟶ pullback
  (prodStr f₁ f₁) f₁}
    (hF : F ≫ aaa φ a ha = aa φ a ha ≫ F₁) (N : (pullback (prodStr f₁ f₁) f₁).Modules) :
    LocIsoOnBase (prodStr f f) ((Scheme.Modules.pullback F).obj ((Scheme.Modules.pullback (aaa φ a
      ha)).obj N)) (𝟙_ _) ↔
      LocIsoOnBase (pullback.snd (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom
          φ)))).obj
          ((Scheme.Modules.pullback F₁).obj N)) (𝟙_ _) :=
  (locIsoOnBase_unit_congr _ (faceIso φ a ha hF N)).trans
    (locIsoOnBase_unit_iff_of_iso (θ φ a ha) _ _ (θ_hom_snd φ a ha) _)

end faces

end FBC

attribute [local simp] FBC.aa_fst
attribute [local simp] FBC.aa_snd
attribute [local simp] FBC.aaa_fst
attribute [local simp] FBC.aaa_snd


open FBC in
theorem _root_.AlgebraicGeometry.Polarisation.locIsoOnBase_faces_pullback_cube_iff_of_isPullback
    {S₁ : Type} [CommRing S₁] {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} (L₁ :
      RelativeGroupLaw S₁ f₁)
    {S : Type} [CommRing S] (φ : S₁ →+* S) {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L :
      RelativeGroupLaw S f)
    (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
    (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    (N : (pullback (prodStr f₁ f₁) f₁).Modules) :
    (LocIsoOnBase (prodStr f f)
        ((Scheme.Modules.pullback (pullback.lift
          (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc, (L.one _).2]; exact pullback.condition))).obj
          ((Scheme.Modules.pullback (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm
              ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            change (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1,
              Category.assoc, ha.w])
          ha.w.symm)).obj N)) (𝟙_ _) ↔
      LocIsoOnBase (pullback.snd (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom
          φ)))).obj
          ((Scheme.Modules.pullback (pullback.lift
          (pullback.lift (L₁.one (prodStr f₁ f₁)).1 (pullback.fst f₁ f₁) (by rw [(L₁.one _).2]))
          (pullback.snd f₁ f₁)
          (by rw [pullback.lift_fst_assoc, (L₁.one _).2]; exact pullback.condition))).obj
          N)) (𝟙_ _)) ∧
    (LocIsoOnBase (prodStr f f)
        ((Scheme.Modules.pullback (pullback.lift
          (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj
          ((Scheme.Modules.pullback (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm
              ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            change (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1,
              Category.assoc, ha.w])
          ha.w.symm)).obj N)) (𝟙_ _) ↔
      LocIsoOnBase (pullback.snd (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom
          φ)))).obj
          ((Scheme.Modules.pullback (pullback.lift
          (pullback.lift (pullback.fst f₁ f₁) (L₁.one (prodStr f₁ f₁)).1 (by rw [(L₁.one _).2]))
          (pullback.snd f₁ f₁)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj N)) (𝟙_ _)) ∧
    (LocIsoOnBase (prodStr f f)
        ((Scheme.Modules.pullback (pullback.lift (𝟙 _) (L.one (prodStr f f)).1
          (by rw [Category.id_comp, (L.one _).2]))).obj
          ((Scheme.Modules.pullback (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm)
          a (Spec.map (CommRingCat.ofHom φ))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm
              ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            change (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom φ) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom φ)) ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1,
              Category.assoc, ha.w])
          ha.w.symm)).obj N)) (𝟙_ _) ↔
      LocIsoOnBase (pullback.snd (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst (prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom
          φ)))).obj
          ((Scheme.Modules.pullback (pullback.lift (𝟙 _) (L₁.one (prodStr f₁ f₁)).1
            (by rw [Category.id_comp, (L₁.one _).2]))).obj N)) (𝟙_ _)) := by
  exact ⟨FBC.face_iff φ a ha (FBC.F1_comp L₁ φ L a ha hLa) N,
    FBC.face_iff φ a ha (FBC.F2_comp L₁ φ L a ha hLa) N,
    FBC.face_iff φ a ha (FBC.F3_comp L₁ φ L a ha hLa) N⟩
end
end Polarisation_locIsoOnBase_faces_pullback_cube_iff_of_isPullback
end AlgebraicCurves.Geometry.Picard.Proofs
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  pullback_monoidal
  isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
