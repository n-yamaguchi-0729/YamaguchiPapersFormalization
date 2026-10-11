/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Connected.Clopen
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Relative Group Law surjective scheme Nsmul of flat of field
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


namespace GoodReductionJacobian

export _root_.GoodReductionJacobian (schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw)

namespace RelativeGroupLaw

export _root_.GoodReductionJacobian.RelativeGroupLaw (nsmul nsmul_zero nsmul_succ nsmul_unit
  nsmul_natural idPoint schemeNsmul schemeNsmul_over IsCommutative pointGroup one_natural mul_assoc
  mul_one one mul_natural inv one_mul inv_mul_cancel mul)


open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian


variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f)

theorem schemeHomOverComp_mk {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (x : SchemeHomOver t f) :
    (schemeHomOverComp ψ rfl x).1 = ψ ≫ x.1 := rfl

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.inv_natural {T T' : Scheme.{u}} (t :
  T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (schemeHomOverComp ψ hψ x) := by
  let := G.pointGroup t'
  have h1 : schemeHomOverComp ψ hψ (G.inv t x) * schemeHomOverComp ψ hψ x = 1 := by
    change G.mul t' _ _ = G.one t'
    rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]
  have h2 : G.inv t' (schemeHomOverComp ψ hψ x) * schemeHomOverComp ψ hψ x = 1 :=
    G.inv_mul_cancel t' _
  exact mul_right_cancel (h1.trans h2.symm)
export _root_.GoodReductionJacobian.RelativeGroupLaw (inv_natural)


private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nsmul_coe {T : Scheme.{u}} (t : T ⟶
  Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x := by
    apply Subtype.ext
    simp [schemeHomOverComp]
  have := G.nsmul_natural f t x.1 x.2 n idPoint
  rw [hx] at this
  rw [← this]
  rfl
export _root_.GoodReductionJacobian.RelativeGroupLaw (nsmul_coe)


private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nsmul_mul (hc : G.IsCommutative) {T :
  Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x y : SchemeHomOver t f) : G.nsmul t n (G.mul t x y) = G.mul t (G.nsmul t n x) (G.nsmul t n y)
      := by
  induction n with
  | zero => simp only [nsmul_zero]; exact (G.one_mul t _).symm
  | succ n ih =>
      simp only [nsmul_succ, ih]
      let := G.pointGroup t
      change (G.nsmul t n x * G.nsmul t n y) * (x * y) = (G.nsmul t n x * x) * (G.nsmul t n y * y)
      have hcomm : ∀ a b : SchemeHomOver t f, a * b = b * a := fun a b => hc t a b
      rw [_root_.mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (G.nsmul t n y), hcomm (G.nsmul t
        n y) x, _root_.mul_assoc]
export _root_.GoodReductionJacobian.RelativeGroupLaw (nsmul_mul)

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nsmul_inv (hc : G.IsCommutative) {T :
  Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) : G.nsmul t n (G.inv t x) = G.inv t (G.nsmul t n x) := by
  let := G.pointGroup t
  have h : G.mul t (G.nsmul t n (G.inv t x)) (G.nsmul t n x) = G.one t := by
    rw [← G.nsmul_mul hc, G.inv_mul_cancel, G.nsmul_unit]
  have h2 : G.mul t (G.inv t (G.nsmul t n x)) (G.nsmul t n x) = G.one t := G.inv_mul_cancel t _
  exact mul_right_cancel (h.trans h2.symm : (_ : SchemeHomOver t f) * _ = _ * _)
export _root_.GoodReductionJacobian.RelativeGroupLaw (nsmul_inv)


section Shear

/-- The structure morphism of the double fibre product. -/
noncomputable abbrev prBase : pullback f f ⟶ Spec (CommRingCat.of R) := pullback.fst f f ≫ f

/-- The first projection as a point over the product base. -/
noncomputable abbrev ptFst : SchemeHomOver (prBase (f := f)) f := ⟨pullback.fst f f, rfl⟩

/-- The second projection as a point over the product base. -/
noncomputable abbrev ptSnd : SchemeHomOver (prBase (f := f)) f := ⟨pullback.snd f f,
  pullback.condition.symm⟩

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.mulHom : pullback f f ⟶ A
  := (G.mul prBase ptFst ptSnd).1
export _root_.GoodReductionJacobian.RelativeGroupLaw (mulHom)

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.mulHom_comp : G.mulHom ≫ f = prBase
  := (G.mul prBase ptFst ptSnd).2
export _root_.GoodReductionJacobian.RelativeGroupLaw (mulHom_comp)


private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.shear : pullback f f ⟶
  pullback f f :=
  pullback.lift G.mulHom (pullback.snd f f) (by rw [G.mulHom_comp]; exact pullback.condition)
export _root_.GoodReductionJacobian.RelativeGroupLaw (shear)


private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.shearInv : pullback f f ⟶
  pullback f f :=
  pullback.lift (G.mul prBase ptFst (G.inv prBase ptSnd)).1 (pullback.snd f f)
    (by rw [(G.mul prBase ptFst (G.inv prBase ptSnd)).2]; exact pullback.condition)
export _root_.GoodReductionJacobian.RelativeGroupLaw (shearInv)

@[scoped simp] theorem shear_fst : G.shear ≫ pullback.fst f f = G.mulHom := pullback.lift_fst _ _ _
@[scoped simp] theorem shear_snd : G.shear ≫ pullback.snd f f = pullback.snd f f :=
  pullback.lift_snd _ _ _
@[scoped simp] theorem shearInv_fst : G.shearInv ≫ pullback.fst f f = (G.mul prBase ptFst (G.inv
  prBase ptSnd)).1 :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem shearInv_snd : G.shearInv ≫ pullback.snd f f = pullback.snd f f :=
  pullback.lift_snd _ _ _

theorem comp_mul_val {S : Scheme.{u}} (s : S ⟶ pullback f f) (x y : SchemeHomOver (prBase (f := f))
  f) :
    s ≫ (G.mul prBase x y).1 = (G.mul (s ≫ prBase) (schemeHomOverComp s rfl x) (schemeHomOverComp s
      rfl y)).1 := by
  have := congrArg Subtype.val (G.mul_natural prBase (s ≫ prBase) s rfl x y)
  simpa only [schemeHomOverComp_coe] using this

theorem comp_inv_val {S : Scheme.{u}} (s : S ⟶ pullback f f) (x : SchemeHomOver (prBase (f := f))
  f) :
    s ≫ (G.inv prBase x).1 = (G.inv (s ≫ prBase) (schemeHomOverComp s rfl x)).1 := by
  have := congrArg Subtype.val (G.inv_natural prBase (s ≫ prBase) s rfl x)
  simpa only [schemeHomOverComp_coe] using this

end Shear

section Translate

variable {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver s f)

/-- The structure morphism of the pullback along the chosen base morphism. -/
noncomputable abbrev qBase : pullback s f ⟶ Spec (CommRingCat.of R) := pullback.fst s f ≫ s

/-- The chosen point pulled back along the first projection. -/
noncomputable abbrev qA : SchemeHomOver (qBase s (f := f)) f :=
  schemeHomOverComp (pullback.fst s f) rfl a

/-- The point given by the second projection of the pullback. -/
noncomputable abbrev qY : SchemeHomOver (qBase s (f := f)) f :=
  ⟨pullback.snd s f, pullback.condition.symm⟩

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.translate : pullback s f ⟶
  pullback s f :=
  pullback.lift (pullback.fst s f) (G.mul (qBase s) (qA s a) (qY s)).1
    (by rw [(G.mul (qBase s) (qA s a) (qY s)).2])
export _root_.GoodReductionJacobian.RelativeGroupLaw (translate)


private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.translateInv : pullback s f
  ⟶ pullback s f :=
  pullback.lift (pullback.fst s f) (G.mul (qBase s) (G.inv (qBase s) (qA s a)) (qY s)).1
    (by rw [(G.mul (qBase s) (G.inv (qBase s) (qA s a)) (qY s)).2])
export _root_.GoodReductionJacobian.RelativeGroupLaw (translateInv)

@[scoped simp] theorem translate_fst : G.translate s a ≫ pullback.fst s f = pullback.fst s f :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem translate_snd : G.translate s a ≫ pullback.snd s f = (G.mul (qBase s) (qA s
  a) (qY s)).1 :=
  pullback.lift_snd _ _ _
@[scoped simp] theorem translateInv_fst : G.translateInv s a ≫ pullback.fst s f = pullback.fst s f
  := pullback.lift_fst _ _ _
@[scoped simp] theorem translateInv_snd : G.translateInv s a ≫ pullback.snd s f =
    (G.mul (qBase s) (G.inv (qBase s) (qA s a)) (qY s)).1 := pullback.lift_snd _ _ _

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.comp_mul_val' {S' : Scheme.{u}} (r :
  S' ⟶ pullback s f) (t' : S' ⟶ Spec (CommRingCat.of R))
    (hr : r ≫ qBase s = t') (x y : SchemeHomOver (qBase s (f := f)) f) :
    r ≫ (G.mul (qBase s) x y).1 =
      (G.mul t' (schemeHomOverComp r hr x) (schemeHomOverComp r hr y)).1 := by
  simpa only [schemeHomOverComp_coe] using congrArg Subtype.val (G.mul_natural (qBase s) t' r hr x
    y)
export _root_.GoodReductionJacobian.RelativeGroupLaw (comp_mul_val')

theorem comp_inv_val' {S' : Scheme.{u}} (r : S' ⟶ pullback s f) (t' : S' ⟶ Spec (CommRingCat.of R))
    (hr : r ≫ qBase s = t') (x : SchemeHomOver (qBase s (f := f)) f) :
    r ≫ (G.inv (qBase s) x).1 = (G.inv t' (schemeHomOverComp r hr x)).1 := by
  simpa only [schemeHomOverComp_coe] using congrArg Subtype.val (G.inv_natural (qBase s) t' r hr x)

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.translate_base : G.translate s a ≫
  qBase s = qBase s := by
  rw [← Category.assoc, translate_fst]
export _root_.GoodReductionJacobian.RelativeGroupLaw (translate_base)

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.translateInv_base : G.translateInv s
  a ≫ qBase s = qBase s := by
  rw [← Category.assoc, translateInv_fst]
export _root_.GoodReductionJacobian.RelativeGroupLaw (translateInv_base)

theorem translate_qA : schemeHomOverComp (G.translate s a) (G.translate_base s a) (qA s a) = qA s a
  := by
  apply Subtype.ext
  simp only [schemeHomOverComp_coe]
  rw [← Category.assoc, translate_fst]

theorem translate_qY : schemeHomOverComp (G.translate s a) (G.translate_base s a) (qY s) =
    G.mul (qBase s) (qA s a) (qY s) := by
  apply Subtype.ext
  simp only [schemeHomOverComp_coe, translate_snd]

theorem translateInv_qA : schemeHomOverComp (G.translateInv s a) (G.translateInv_base s a) (qA s a)
  = qA s a := by
  apply Subtype.ext
  simp only [schemeHomOverComp_coe]
  rw [← Category.assoc, translateInv_fst]

theorem translateInv_qY : schemeHomOverComp (G.translateInv s a) (G.translateInv_base s a) (qY s) =
    G.mul (qBase s) (G.inv (qBase s) (qA s a)) (qY s) := by
  apply Subtype.ext
  simp only [schemeHomOverComp_coe, translateInv_snd]

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.translate_translateInv : G.translate
  s a ≫ G.translateInv s a = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · rw [Category.assoc, translateInv_snd, G.comp_mul_val' s _ _ (G.translate_base s a),
      Category.id_comp]
    have hinv : schemeHomOverComp (G.translate s a) (G.translate_base s a) (G.inv (qBase s) (qA s
      a)) =
        G.inv (qBase s) (qA s a) := by
      rw [G.inv_natural _ _ _ (G.translate_base s a), translate_qA]
    rw [hinv, translate_qY]
    let := G.pointGroup (qBase s (f := f))
    change ((qA s a)⁻¹ * (qA s a * qY s) : SchemeHomOver (qBase s (f := f)) f).1 = _
    rw [inv_mul_cancel_left]
export _root_.GoodReductionJacobian.RelativeGroupLaw (translate_translateInv)

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.translateInv_translate :
  G.translateInv s a ≫ G.translate s a = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · rw [Category.assoc, translate_snd, G.comp_mul_val' s _ _ (G.translateInv_base s a),
      Category.id_comp,
      translateInv_qA, translateInv_qY]
    let := G.pointGroup (qBase s (f := f))
    change ((qA s a) * ((qA s a)⁻¹ * qY s) : SchemeHomOver (qBase s (f := f)) f).1 = _
    rw [mul_inv_cancel_left]
export _root_.GoodReductionJacobian.RelativeGroupLaw (translateInv_translate)


private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.translateIso : pullback s f
  ≅ pullback s f :=
  ⟨G.translate s a, G.translateInv s a, G.translate_translateInv s a, G.translateInv_translate s a⟩
export _root_.GoodReductionJacobian.RelativeGroupLaw (translateIso)

end Translate

section C4

variable {k : Type u} [Field k] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of k)} (L :
  RelativeGroupLaw k g)

private noncomputable abbrev _root_.GoodReductionJacobian.RelativeGroupLaw.unitSec : Spec
  (CommRingCat.of k) ⟶ B := (L.one (𝟙 _)).1
export _root_.GoodReductionJacobian.RelativeGroupLaw (unitSec)

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.unitSec_comp : L.unitSec ≫ g = 𝟙 _ :=
  (L.one (𝟙 _)).2
export _root_.GoodReductionJacobian.RelativeGroupLaw (unitSec_comp)


private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.unitSec_schemeNsmul (n : ℕ) :
  L.unitSec ≫ L.schemeNsmul n = L.unitSec := by
  have := congrArg Subtype.val (L.nsmul_unit (𝟙 _) n)
  rw [L.nsmul_coe] at this
  exact this
export _root_.GoodReductionJacobian.RelativeGroupLaw (unitSec_schemeNsmul)


private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.pairUnit : B ⟶ pullback g g
  :=
  pullback.lift (𝟙 B) (g ≫ L.unitSec) (by rw [Category.assoc, L.unitSec_comp]; simp)
export _root_.GoodReductionJacobian.RelativeGroupLaw (pairUnit)

@[scoped simp] theorem pairUnit_fst : L.pairUnit ≫ pullback.fst g g = 𝟙 B := pullback.lift_fst _ _ _
@[scoped simp] theorem pairUnit_snd : L.pairUnit ≫ pullback.snd g g = g ≫ L.unitSec :=
  pullback.lift_snd _ _ _

theorem pairUnit_mulHom : L.pairUnit ≫ L.mulHom = 𝟙 B := by
  have hpu : L.pairUnit ≫ qBase g (f := g) = g := by
    change L.pairUnit ≫ pullback.fst g g ≫ g = g
    rw [← Category.assoc, pairUnit_fst, Category.id_comp]
  rw [mulHom, L.comp_mul_val' g L.pairUnit g hpu]
  have h1 : schemeHomOverComp L.pairUnit hpu (ptFst (f := g)) = (⟨𝟙 B, Category.id_comp g⟩ :
    SchemeHomOver g g) := by
    apply Subtype.ext; simp [schemeHomOverComp]
  have h2 : schemeHomOverComp L.pairUnit hpu (ptSnd (f := g)) = L.one g := by
    rw [← L.one_natural (𝟙 _) g g (Category.comp_id g)]
    apply Subtype.ext; simp [schemeHomOverComp]
  rw [h1, h2, L.mul_one]

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.symmetry_mulHom (hc :
  L.IsCommutative) : (pullbackSymmetry g g).hom ≫ L.mulHom = L.mulHom := by
  have hσ : (pullbackSymmetry g g).hom ≫ qBase g (f := g) = qBase g (f := g) := by
    change (pullbackSymmetry g g).hom ≫ pullback.fst g g ≫ g = pullback.fst g g ≫ g
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]; exact pullback.condition.symm
  rw [mulHom, L.comp_mul_val' g _ _ hσ]
  have h1 : schemeHomOverComp (pullbackSymmetry g g).hom hσ (ptFst (f := g)) = ptSnd := by
    apply Subtype.ext; simp [schemeHomOverComp]
  have h2 : schemeHomOverComp (pullbackSymmetry g g).hom hσ (ptSnd (f := g)) = ptFst := by
    apply Subtype.ext; simp [schemeHomOverComp]
  rw [h1, h2, hc]
export _root_.GoodReductionJacobian.RelativeGroupLaw (symmetry_mulHom)

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nn_cond (n : ℕ) : g ≫ 𝟙 (Spec
  (CommRingCat.of k)) = L.schemeNsmul n ≫ g := by
  rw [Category.comp_id, L.schemeNsmul_over]
export _root_.GoodReductionJacobian.RelativeGroupLaw (nn_cond)


private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.nn (n : ℕ) : pullback g g ⟶
  pullback g g :=
  pullback.map g g g g (L.schemeNsmul n) (L.schemeNsmul n) (𝟙 _) (L.nn_cond n) (L.nn_cond n)
export _root_.GoodReductionJacobian.RelativeGroupLaw (nn)

@[scoped simp] theorem nn_fst (n : ℕ) : L.nn n ≫ pullback.fst g g = pullback.fst g g ≫
  L.schemeNsmul n :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem nn_snd (n : ℕ) : L.nn n ≫ pullback.snd g g = pullback.snd g g ≫
  L.schemeNsmul n :=
  pullback.lift_snd _ _ _

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.range_nn (n : ℕ) : Set.range (L.nn n)
  =
    pullback.fst g g ⁻¹' Set.range (L.schemeNsmul n) ∩ pullback.snd g g ⁻¹' Set.range
      (L.schemeNsmul n) :=
  Scheme.Pullback.range_map g g g g _ _ (𝟙 _) (L.nn_cond n) (L.nn_cond n)
export _root_.GoodReductionJacobian.RelativeGroupLaw (range_nn)


private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nn_translateInv (hc :
  L.IsCommutative) (n : ℕ) :
    L.nn n ≫ L.translateInv g idPoint = L.translateInv g idPoint ≫ L.nn n := by
  have hb : L.nn n ≫ qBase g = qBase g (f := g) := by
    change L.nn n ≫ pullback.fst g g ≫ g = pullback.fst g g ≫ g
    rw [← Category.assoc, nn_fst, Category.assoc, L.schemeNsmul_over]
  have hA : schemeHomOverComp (L.nn n) hb (qA g idPoint) = L.nsmul _ n (qA g (f := g) idPoint) := by
    apply Subtype.ext
    rw [L.nsmul_coe]; simp [schemeHomOverComp, idPoint]
  have hY : schemeHomOverComp (L.nn n) hb (qY g) = L.nsmul _ n (qY g (f := g)) := by
    apply Subtype.ext
    rw [L.nsmul_coe]; simp [schemeHomOverComp]
  apply pullback.hom_ext
  · rw [Category.assoc, translateInv_fst, Category.assoc, nn_fst, ← Category.assoc,
      translateInv_fst]
  · rw [Category.assoc, translateInv_snd, L.comp_mul_val' g _ _ hb, L.inv_natural _ _ _ hb, hA, hY,
      Category.assoc, nn_snd, ← Category.assoc, translateInv_snd, ← L.nsmul_coe, L.nsmul_mul hc,
        L.nsmul_inv hc]
export _root_.GoodReductionJacobian.RelativeGroupLaw (nn_translateInv)


theorem translate_id_snd : L.translate g idPoint ≫ pullback.snd g g = L.mulHom := by
  rw [translate_snd, mulHom]
  have : qA g (f := g) idPoint = ptFst := Subtype.ext (by simp [schemeHomOverComp, idPoint])
  rw [this]

private theorem
  _root_.GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul_of_flat_of_field'
    [LocallyOfFiniteType g] [IrreducibleSpace B] (hc : L.IsCommutative) (n : ℕ)
    [Flat (L.schemeNsmul n)] : Surjective (L.schemeNsmul n) := by
  classical
  set N := L.schemeNsmul n with hNdef
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian g
  have : LocallyOfFiniteType (N ≫ g) := by rw [hNdef, L.schemeNsmul_over]; infer_instance
  have : LocallyOfFiniteType N := locallyOfFiniteType_of_comp N g
  have : UniversallyOpen N := inferInstance
  let U : Set B := Set.range N
  have hUopen : IsOpen U := N.isOpenMap.isOpen_range
  have hUne : U.Nonempty := Set.range_nonempty _
  have he : ∀ b : B, L.unitSec (g b) ∈ U := fun b =>
    ⟨L.unitSec (g b), by rw [← Scheme.Hom.comp_apply, L.unitSec_schemeNsmul]⟩
  have hkey : ∀ w : ↑(pullback g g), pullback.fst g g w ∈ U → pullback.snd g g w ∉ U → L.mulHom w ∉
    U := by
    intro w h1 h2 hμ
    have hτ : L.translate g idPoint w ∈ Set.range (L.nn n) := by
      rw [L.range_nn]
      refine ⟨?_, ?_⟩
      · change pullback.fst g g (L.translate g idPoint w) ∈ U
        rw [← Scheme.Hom.comp_apply, translate_fst]; exact h1
      · change pullback.snd g g (L.translate g idPoint w) ∈ U
        rw [← Scheme.Hom.comp_apply, translate_id_snd]; exact hμ
    obtain ⟨w', hw'⟩ := hτ
    apply h2
    have hw : w = L.nn n (L.translateInv g idPoint w') := by
      have h1 : (L.translate g idPoint ≫ L.translateInv g idPoint) w = w := by
        rw [L.translate_translateInv]; rfl
      rw [Scheme.Hom.comp_apply, ← hw', ← Scheme.Hom.comp_apply, L.nn_translateInv hc,
        Scheme.Hom.comp_apply] at h1
      exact h1.symm
    refine ⟨pullback.snd g g (L.translateInv g idPoint w'), ?_⟩
    conv_rhs => rw [hw, ← Scheme.Hom.comp_apply, nn_snd, Scheme.Hom.comp_apply]
  have hkey' : ∀ w : ↑(pullback g g), pullback.fst g g w ∉ U → pullback.snd g g w ∈ U → L.mulHom w
    ∉ U := by
    intro w h1 h2
    have := hkey ((pullbackSymmetry g g).hom w)
      (by rwa [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst])
      (by rwa [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_snd])
    rwa [← Scheme.Hom.comp_apply, L.symmetry_mulHom hc] at this
  have htrans : ∀ z : B, z ∉ U → ∃ V : Set B, IsOpen V ∧ z ∈ V ∧ V ⊆ Uᶜ := by
    intro z hz
    let ι := B.fromSpecResidueField z
    let Q := pullback (ι ≫ g) g
    let m : Q ⟶ pullback g g := pullback.map (ι ≫ g) g g g ι (𝟙 B) (𝟙 _) (by simp) (by simp)
    have hm1 : m ≫ pullback.fst g g = pullback.fst (ι ≫ g) g ≫ ι := pullback.lift_fst _ _ _
    have hm2 : m ≫ pullback.snd g g = pullback.snd (ι ≫ g) g := by
      rw [pullback.lift_snd, Category.comp_id]
    have hmμ : m ≫ L.mulHom = L.translate (ι ≫ g) ⟨ι, rfl⟩ ≫ pullback.snd (ι ≫ g) g := by
      rw [translate_snd, mulHom, L.comp_mul_val' g m (qBase (ι ≫ g) (f := g))
        (by rw [← Category.assoc, hm1, Category.assoc])]
      congr 1
      all_goals (apply Subtype.ext; simp [schemeHomOverComp, hm1, hm2])
    have : UniversallyOpen (ι ≫ g) := inferInstance
    have hsnd : IsOpenMap (pullback.snd (ι ≫ g) g) := (pullback.snd (ι ≫ g) g).isOpenMap
    let τh := Scheme.homeoOfIso (L.translateIso (ι ≫ g) ⟨ι, rfl⟩)
    refine ⟨(m ≫ L.mulHom) '' ((pullback.snd (ι ≫ g) g) ⁻¹' U), ?_, ?_, ?_⟩
    · rw [hmμ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
      refine hsnd _ ?_
      have : (L.translate (ι ≫ g) ⟨ι, rfl⟩ : Q ⟶ Q) '' (pullback.snd (ι ≫ g) g ⁻¹' U) =
          τh '' (pullback.snd (ι ≫ g) g ⁻¹' U) := rfl
      rw [this]
      exact τh.isOpenMap _ (hUopen.preimage (pullback.snd (ι ≫ g) g).continuous)
    · let j : Spec (B.residueField z) ⟶ Q := pullback.lift (𝟙 _) (ι ≫ g ≫ L.unitSec)
        (by rw [Category.id_comp, Category.assoc, Category.assoc, L.unitSec_comp, Category.comp_id])
      have hjm : j ≫ m = ι ≫ L.pairUnit := by
        apply pullback.hom_ext
        · rw [Category.assoc, hm1, ← Category.assoc, pullback.lift_fst, Category.id_comp,
            Category.assoc,
            pairUnit_fst, Category.comp_id]
        · rw [Category.assoc, hm2, pullback.lift_snd, Category.assoc, pairUnit_snd]
      let pt : Spec (B.residueField z) := IsLocalRing.closedPoint _
      refine ⟨j pt, ?_, ?_⟩
      · change (j ≫ pullback.snd (ι ≫ g) g) pt ∈ U
        rw [pullback.lift_snd, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact he _
      · change ((j ≫ m) ≫ L.mulHom) pt = z
        rw [hjm, Category.assoc, pairUnit_mulHom, Category.comp_id]
        exact Scheme.fromSpecResidueField_apply z pt
    · rintro _ ⟨q, hq, rfl⟩ hU'
      refine hkey' (m q) ?_ ?_ (by rwa [Scheme.Hom.comp_apply] at hU')
      · rw [← Scheme.Hom.comp_apply, hm1, Scheme.Hom.comp_apply]
        have : ι (pullback.fst (ι ≫ g) g q) = z := by
          have := Scheme.range_fromSpecResidueField z
          exact (Set.range_subset_iff.mp (le_of_eq this) : ∀ _, _) _ |> Set.mem_singleton_iff.mp
        rw [this]; exact hz
      · rw [← Scheme.Hom.comp_apply, hm2]; exact hq
  have hUc : IsOpen Uᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨V, hV, hzV, hVU⟩ := htrans z hz
    exact ⟨V, hVU, hV, hzV⟩
  have hclopen : IsClopen U := ⟨⟨hUc⟩, hUopen⟩
  rcases isClopen_iff.mp hclopen with h | h
  · exact absurd h hUne.ne_empty
  · exact ⟨fun b => by have : b ∈ U := h ▸ Set.mem_univ b; exact this⟩
export _root_.GoodReductionJacobian.RelativeGroupLaw (surjective_schemeNsmul_of_flat_of_field')

end C4

end GoodReductionJacobian.RelativeGroupLaw

attribute [local simp] GoodReductionJacobian.RelativeGroupLaw.shear_fst
attribute [local simp] GoodReductionJacobian.RelativeGroupLaw.shear_snd
attribute [local simp] GoodReductionJacobian.RelativeGroupLaw.shearInv_fst
attribute [local simp] GoodReductionJacobian.RelativeGroupLaw.shearInv_snd
attribute [local simp] GoodReductionJacobian.RelativeGroupLaw.translate_fst
attribute [local simp] GoodReductionJacobian.RelativeGroupLaw.translate_snd
attribute [local simp] GoodReductionJacobian.RelativeGroupLaw.translateInv_fst
attribute [local simp] GoodReductionJacobian.RelativeGroupLaw.translateInv_snd
attribute [local simp] GoodReductionJacobian.RelativeGroupLaw.pairUnit_fst
attribute [local simp] GoodReductionJacobian.RelativeGroupLaw.pairUnit_snd
attribute [local simp] GoodReductionJacobian.RelativeGroupLaw.nn_fst
attribute [local simp] GoodReductionJacobian.RelativeGroupLaw.nn_snd



open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
  _root_.GoodReductionJacobian GoodReductionJacobian in
theorem _root_.GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul_of_flat_of_field
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [IrreducibleSpace A]
    (G : RelativeGroupLaw k f)
    (hc : G.IsCommutative)
    (n : ℕ) [Flat (G.schemeNsmul n)] :
    Surjective (G.schemeNsmul n) :=
  G.surjective_schemeNsmul_of_flat_of_field' hc n
end RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
