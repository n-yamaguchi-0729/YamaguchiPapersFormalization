/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Normalization.CompositumEmbedding
import EtaleFundamentalGroups.Normalization.Primes.FromLocalizationGoingUp
import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.BoundaryAway
import SchemeTheory.RingTheory.Ramification.Etale.SquareRamification
import EtaleFundamentalGroups.FiniteEtale.BaseChange.GenericTensorComponent
import EtaleFundamentalGroups.Kummer.IteratedRadical.BaseChange
import EtaleFundamentalGroups.Kummer.GenericTensor.Tower.Intermediate.NormalizationClosedPrime
import EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.StandardCompletion
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.Prefix.FullRootCombined
import EtaleFundamentalGroups.Kummer.NormalCrossings.SelectedBranch.OtherPrefixEtale
import EtaleFundamentalGroups.Kummer.NormalCrossings.SelectedBranch.RamificationIndexExact

/-!
# The selected normalization prime attached to the retained full component

The same full generic-tensor component used by the prefix/full-root purity
bridge has a normalization prime over the selected root.  Contracting that
prime along the literal right-coordinate embedding produces a prime of the
original selected-branch normalization.  Since the Galois branch-index
theorem holds for every such prime, this literal contraction has
ramification index exactly the selected exponent.

The theorem below makes all choices internally.  In particular, neither a
normalization prime, a component comparison, nor a ramification-index
identity is an input.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uA uK uL

/-- The fraction-field actions used below are both induced from the same
fraction field of the base.  Hence the canonical lift through the
intermediate fraction ring is compatible with them. -/
private theorem fractionFieldTower_isScalarTower_exactPrimeSource
    {R B D : Type uA} {K : Type uK}
    [CommRing R] [IsDomain R]
    [CommRing B] [IsDomain B] [Algebra R B]
    [CommRing D] [IsDomain D] [Algebra B D] [Algebra R D]
    [IsScalarTower R B D]
    [Field K] [algRK : Algebra R K] [IsFractionRing R K]
    [algKKB : Algebra K (FractionRing B)]
    [towerR_K_KB : IsScalarTower R K (FractionRing B)]
    [algKKD : Algebra K (FractionRing D)]
    [towerR_K_KD : IsScalarTower R K (FractionRing D)]
    [algKBKD : Algebra (FractionRing B) (FractionRing D)]
    [towerR_KB_KD : IsScalarTower R (FractionRing B) (FractionRing D)] :
    IsScalarTower K (FractionRing B) (FractionRing D) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  have hmaps :
      algebraMap K (FractionRing D) =
        (algebraMap (FractionRing B) (FractionRing D)).comp
          (algebraMap K (FractionRing B)) := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro z
    calc
      algebraMap K (FractionRing D) (algebraMap R K z) =
          algebraMap R (FractionRing D) z :=
        (IsScalarTower.algebraMap_apply R K (FractionRing D) z).symm
      _ = algebraMap (FractionRing B) (FractionRing D)
            (algebraMap R (FractionRing B) z) :=
        IsScalarTower.algebraMap_apply R (FractionRing B) (FractionRing D) z
      _ = algebraMap (FractionRing B) (FractionRing D)
            (algebraMap K (FractionRing B) (algebraMap R K z)) := by
        exact congrArg (algebraMap (FractionRing B) (FractionRing D))
          (IsScalarTower.algebraMap_apply R K (FractionRing B) z)
  exact DFunLike.congr_fun hmaps x

/-- Restrict an algebra equivalence over the base of a localization to an
equivalence over that localization. -/
private noncomputable def algEquivOverLocalizationBase_exactPrimeSource
    {R S U V : Type*}
    [CommRing R] [CommRing S] [CommRing U] [CommRing V]
    (M : Submonoid R)
    [Algebra R S] [IsLocalization M S]
    [Algebra R U] [Algebra R V]
    [Algebra S U] [Algebra S V]
    [IsScalarTower R S U] [IsScalarTower R S V]
    (e : U ≃ₐ[R] V) : U ≃ₐ[S] V :=
  { toRingEquiv := e.toRingEquiv
    commutes' := by
      intro z
      have hmaps :
          e.toRingHom.comp (algebraMap S U) = algebraMap S V := by
        apply IsLocalization.ringHom_ext M
        ext x
        change e (algebraMap S U (algebraMap R S x)) =
          algebraMap S V (algebraMap R S x)
        rw [← IsScalarTower.algebraMap_apply R S U,
          ← IsScalarTower.algebraMap_apply R S V]
        exact e.commutes x
      exact DFunLike.congr_fun hmaps z }

/-- Right-handed form of finite-etale generic-component base change.

The finite generic fibre occupies the left tensor coordinate and the normal
base-change fraction field occupies the right coordinate.  Tensor
commutativity transports the literal maximal ideal to the orientation of
`integralClosure_genericTensorFieldComponent_etale_of_finiteEtale_baseChange`;
the quotient equivalence then returns to the original specified component.
-/
private theorem
    integralClosure_genericTensorFieldComponent_etale_of_finiteEtale_baseChange_comm
    {A B T F E K : Type*}
    [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B]
    [CommRing T] [IsDomain T] [Algebra A T]
    [Module.Finite A T] [Algebra.Etale A T]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra T E] [IsFractionRing T E]
    [Algebra A E] [IsScalarTower A T E]
    [Algebra F E] [IsScalarTower A F E]
    [Field K] [Algebra B K] [IsFractionRing B K]
    [Algebra A K] [Algebra F K]
    [IsScalarTower A B K] [IsScalarTower A F K]
    (m : Ideal (E ⊗[F] K)) [m.IsMaximal] :
    let M := GenericTensorFieldComponent m
    let : Algebra K M := genericTensorFieldComponentRightAlgebra m
    let : Algebra B M :=
      ((algebraMap K M).comp (algebraMap B K)).toAlgebra
    Algebra.Etale B (integralClosure B M) := by
  classical
  intro M algKM algBM
  let : IsScalarTower B K M := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra K (K ⊗[F] E) := Algebra.TensorProduct.leftAlgebra
  let : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  let eComm : (K ⊗[F] E) ≃ₐ[K] (E ⊗[F] K) :=
    { toRingEquiv := (Algebra.TensorProduct.comm F K E).toRingEquiv
      commutes' := fun _ ↦ rfl }
  let mComm := m.comap eComm.toRingEquiv.toRingHom
  let : mComm.IsMaximal :=
    (inferInstance : m.IsMaximal).comap_bijective
      eComm.toRingEquiv.toRingHom eComm.bijective
  let MComm := GenericTensorFieldComponent mComm
  have hEtaleComm :
      Algebra.Etale B (integralClosure B MComm) :=
    integralClosure_genericTensorFieldComponent_etale_of_finiteEtale_baseChange
      (A := A) (B := B) (T := T) (F := F) (E := E) (K := K) mComm
  have hmMap : m = mComm.map eComm.toRingEquiv.toRingHom := by
    exact (Ideal.map_comap_of_surjective
      eComm.toRingEquiv.toRingHom eComm.surjective m).symm
  let eComponentK : MComm ≃ₐ[K] M :=
    Ideal.quotientEquivAlg mComm m eComm hmMap
  let eComponentB : MComm ≃ₐ[B] M := eComponentK.restrictScalars B
  exact Algebra.Etale.of_equiv eComponentB.mapIntegralClosure

/-- The selected branch prime is sometimes presented as the image of the
principal boundary prime rather than as the principal ideal generated after
localization.  Eliminating that equality before forming the second
localization keeps its dependent prime instance coherent. -/
private theorem
    heightTwoGaloisOtherRootPrefix_finiteEtale_at_mappedSelectedBranch
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (hCharZero : CharZero (A ⧸ Ideal.span ({t i} : Set A)))
    (sigma : Equiv.Perm (Fin d))
    (pR : Ideal (Localization.AtPrime P)) [pR.IsPrime]
    (hpR : pR = Ideal.span
      ({algebraMap A (Localization.AtPrime P) (t i)} :
        Set (Localization.AtPrime P))) :
    let e := heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let n := heightTwoConditionalOtherExponent t i r P e sigma
    let R := Localization.AtPrime P
    let aR : Fin d → R :=
      heightTwoConditionalOtherRadicand t i P sigma
    let V := Localization.AtPrime pR
    let aV : Fin d → V := fun k ↦ algebraMap R V (aR k)
    let E := iteratedRadical V d n aV
    Module.Finite V E ∧ Module.FaithfullyFlat V E ∧
      Algebra.Etale V E := by
  subst pR
  simpa only using
    (heightTwoGaloisOtherRootPrefix_finiteEtale_at_selectedBranch
      (K := K) (L := L) hNC i hi P hP htiP hCharZero sigma)

/-- The ramification index of a retained intermediate normalization prime is
the exact selected index.  All scalar actions on the localized tensor
component, the comparison of the two integral closures, and the contracted
normalization prime are constructed internally. -/
private theorem
    retainedIntermediateNormalizationPrime_ramificationIdx_eq
    {B V K KB L : Type*} {N : ℕ}
    [CommRing B] [IsDomain B]
    [CommRing V] [IsDomain V] [IsLocalRing V]
    [Field K] [Field KB] [Field L]
    [Algebra V K] [IsFractionRing V K]
    [Algebra B KB] [IsFractionRing B KB]
    (qB : Ideal B) [qB.IsPrime]
    [Algebra V (Localization.AtPrime qB)]
    [IsLocalHom (algebraMap V (Localization.AtPrime qB))]
    [Module.Finite V (Localization.AtPrime qB)]
    [Algebra.Etale V (Localization.AtPrime qB)]
    [Algebra K KB]
    [Algebra K L] [Algebra V L] [IsScalarTower V K L]
    [FiniteDimensional K L]
    (hCompatibility : ∀ z : V,
      algebraMap K KB (algebraMap V K z) =
        (@algebraMap (Localization.AtPrime qB) KB _ _
          (localizationAtPrimeToFractionFieldAlgebra (K := KB) qB))
            (algebraMap V (Localization.AtPrime qB) z))
    (m : Ideal (KB ⊗[K] L)) [m.IsMaximal]
    (hExact : ∀ Q : (IsLocalRing.maximalIdeal V).primesOver
      (integralClosure V L), Q.1.ramificationIdx V = N) :
    let M := GenericTensorFieldComponent m
    let : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    ∀ q : Ideal (integralClosure B M), q.IsPrime → q.LiesOver qB →
      q.ramificationIdx B = N := by
  classical
  intro M algBM q hqPrime hqOver
  let W := Localization.AtPrime qB
  let : SMul B M := algBM.toSMul
  let : IsScalarTower B KB M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower K KB M :=
    genericTensorFieldComponent_isScalarTower m
  let : Algebra W KB :=
    localizationAtPrimeToFractionFieldAlgebra (K := KB) qB
  let : IsFractionRing W KB :=
    localizationAtPrimeToFractionField_isFractionRing (K := KB) qB
  let : Algebra V KB :=
    ((algebraMap K KB).comp (algebraMap V K)).toAlgebra
  let : IsScalarTower V K KB := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower V W KB := by
    apply IsScalarTower.of_algebraMap_eq
    exact hCompatibility
  let : Algebra V M :=
    ((algebraMap K M).comp (algebraMap V K)).toAlgebra
  let : SMul V M := (inferInstance : Algebra V M).toSMul
  let : IsScalarTower V K M := IsScalarTower.of_algebraMap_eq' rfl
  let algWM : Algebra W M :=
    localizationAtPrimeToExtensionAlgebra (K := KB) (L := M) qB
  let : SMul W M := algWM.toSMul
  let : IsScalarTower W KB M :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := KB) (L := M) qB
  have hVWM : IsScalarTower V W M := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap K M (algebraMap V K z) =
      algebraMap KB M (algebraMap W KB (algebraMap V W z))
    rw [IsScalarTower.algebraMap_apply K KB M, hCompatibility]
  let algLM : Algebra L M := genericTensorFieldComponentRightAlgebra m
  let : SMul L M := algLM.toSMul
  let : IsScalarTower K L M :=
    genericTensorFieldComponent_right_isScalarTower m
  have hVLM : IsScalarTower V L M := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap K M (algebraMap V K z) =
      algebraMap L M (algebraMap V L z)
    rw [IsScalarTower.algebraMap_apply K L M,
      ← IsScalarTower.algebraMap_apply V K L]
  let C := integralClosure V L
  let S := integralClosure W M
  let : IsIntegrallyClosed C :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  let : IsFractionRing C L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L C
  let : IsScalarTower V C L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra C M :=
    ((algebraMap L M).comp (algebraMap C L)).toAlgebra
  let : SMul C M := (inferInstance : Algebra C M).toSMul
  let : IsScalarTower C L M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower V C M := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    calc
      algebraMap V M z = algebraMap K M (algebraMap V K z) :=
        IsScalarTower.algebraMap_apply V K M z
      _ = algebraMap L M (algebraMap K L (algebraMap V K z)) :=
        IsScalarTower.algebraMap_apply K L M _
      _ = algebraMap L M (algebraMap V L z) := by
        rw [← IsScalarTower.algebraMap_apply V K L]
      _ = algebraMap L M (algebraMap C L (algebraMap V C z)) := by
        rw [IsScalarTower.algebraMap_apply V C L]
      _ = algebraMap C M (algebraMap V C z) :=
        (IsScalarTower.algebraMap_apply C L M _).symm
  have hEtaleC : Algebra.Etale C (integralClosure C M) :=
    integralClosure_genericTensorFieldComponent_etale_of_finiteEtale_baseChange_comm
      (A := V) (B := C) (T := W) (F := K) (E := KB)
      (K := L) m
  let fLM : L →ₐ[V] M :=
    (genericTensorFieldComponentRight m).restrictScalars V
  let psi : C →ₐ[V] S :=
    EtaleFundamentalGroups.integralClosureToCompositumAlgHom
      (A := V) (B := W) (L := L) (Ω := M) fLM
  let : Algebra C S := psi.toAlgebra
  let : IsScalarTower V C S :=
    IsScalarTower.of_algebraMap_eq fun z ↦ (psi.commutes z).symm
  let : IsScalarTower C S M := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    symm
    change algebraMap S M (psi z) = algebraMap C M z
    calc
      algebraMap S M (psi z) = ((psi z : S) : M) := rfl
      _ = fLM (z : L) :=
        EtaleFundamentalGroups.integralClosureToCompositumAlgHom_coe
          (A := V) (B := W) (L := L) (Ω := M) fLM z
      _ = algebraMap L M (z : L) := rfl
      _ = algebraMap C M z :=
        (IsScalarTower.algebraMap_apply C L M z).symm
  let : Algebra.IsIntegral V C :=
    IsIntegralClosure.isIntegral_algebra V L
  let : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  let : IsIntegralClosure S C M :=
    { algebraMap_injective := Subtype.val_injective
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          have hxV : IsIntegral V x := isIntegral_trans (R := V) x hx
          have hxW : IsIntegral W x := hxV.tower_top
          exact
            (show IsIntegral W x ↔
                ∃ z : S, algebraMap S M z = x from
              IsIntegralClosure.isIntegral_iff).mp hxW
        · rintro ⟨z, rfl⟩
          have hxW : IsIntegral W (algebraMap S M z) :=
            (show IsIntegral W (algebraMap S M z) ↔
                ∃ w : S, algebraMap S M w = algebraMap S M z from
              IsIntegralClosure.isIntegral_iff).mpr ⟨z, rfl⟩
          have hxV : IsIntegral V (algebraMap S M z) :=
            isIntegral_trans (R := V) (algebraMap S M z) hxW
          exact hxV.tower_top }
  let : Algebra C (integralClosure C M) :=
    (integralClosure C M).algebra
  let : SMul C (integralClosure C M) :=
    (inferInstance : Algebra C (integralClosure C M)).toSMul
  let : IsScalarTower C (integralClosure C M) M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let eNorm : integralClosure C M ≃ₐ[C] S :=
    IsIntegralClosure.equiv C (integralClosure C M) M S
  let : Algebra.Etale C S := by
    exact Algebra.Etale.of_equiv eNorm
  let qLoc := localizedNormalizationPrime
    (K := KB) (L := M) qB q
  let : qLoc.IsPrime :=
    (localizedNormalizationPrime_isMaximal
      (K := KB) (L := M) qB q).isPrime
  let : qLoc.LiesOver (IsLocalRing.maximalIdeal W) :=
    localizedNormalizationPrime_liesOver
      (K := KB) (L := M) qB q
  let QIdeal := qLoc.comap psi.toRingHom
  let : QIdeal.IsPrime :=
    (inferInstance : qLoc.IsPrime).comap psi.toRingHom
  let : qLoc.LiesOver QIdeal := ⟨rfl⟩
  have hMaxWV : (IsLocalRing.maximalIdeal W).LiesOver
      (IsLocalRing.maximalIdeal V) := by
    apply (Ideal.liesOver_iff _ _).mpr
    exact (IsLocalRing.maximalIdeal_comap (algebraMap V W)).symm
  have hqLocOverV : qLoc.LiesOver (IsLocalRing.maximalIdeal V) :=
    Ideal.LiesOver.trans qLoc (IsLocalRing.maximalIdeal W)
      (IsLocalRing.maximalIdeal V)
  have hQOverV : QIdeal.LiesOver (IsLocalRing.maximalIdeal V) :=
    Ideal.LiesOver.tower_bot qLoc QIdeal
      (IsLocalRing.maximalIdeal V)
  let Q : (IsLocalRing.maximalIdeal V).primesOver C :=
    ⟨QIdeal, inferInstance, hQOverV⟩
  have hSquare : qLoc.ramificationIdx W = Q.1.ramificationIdx V :=
    EtaleFundamentalGroups.ramificationIdx_eq_of_etale_square
      (R := V) (B := C) (C := W) (S := S) Q.1 qLoc
  have hLocal : qLoc.ramificationIdx W = q.ramificationIdx B :=
    localizedNormalizationPrime_ramificationIdx
      (K := KB) (L := M) qB q
  exact hLocal.symm.trans (hSquare.trans (hExact Q))

/-- Canonical maps from prime localizations commute with the two literal
component embeddings whenever their fraction-field maps commute. -/
private theorem localizedComponentMaps_commute_exactPrimeSource
    {R D K KD L M : Type*}
    [CommRing R] [IsDomain R] [CommRing D] [IsDomain D]
    [Field K] [Field KD] [CommRing L] [CommRing M]
    [Algebra R D] [Algebra R K] [IsFractionRing R K]
    [Algebra D KD] [IsFractionRing D KD]
    [Algebra K KD] [Algebra K L]
    (pR : Ideal R) [pR.IsPrime]
    (qD : Ideal D) [qD.IsPrime] [qD.LiesOver pR]
    (f : KD →+* M) (g : L →+* M)
    (hBase : (algebraMap K KD).comp (algebraMap R K) =
      (algebraMap D KD).comp (algebraMap R D))
    (hComponent : f.comp (algebraMap K KD) = g.comp (algebraMap K L)) :
    let V := Localization.AtPrime pR
    let W := Localization.AtPrime qD
    let : Algebra V W := Localization.AtPrime.algebraOfLiesOver pR qD
    let : Algebra V K := localizationAtPrimeToFractionFieldAlgebra (K := K) pR
    let : Algebra W KD := localizationAtPrimeToFractionFieldAlgebra (K := KD) qD
    (f.comp (algebraMap W KD)).comp (algebraMap V W) =
      (g.comp (algebraMap K L)).comp (algebraMap V K) := by
  intro V W algVW algVK algWKD
  let : IsScalarTower R V K :=
    localizationAtPrimeToFractionField_isScalarTower (K := K) pR
  let : IsScalarTower D W KD :=
    localizationAtPrimeToFractionField_isScalarTower (K := KD) qD
  apply IsLocalization.ringHom_ext pR.primeCompl
  ext x
  simp only [RingHom.comp_apply]
  calc
    f (algebraMap W KD (algebraMap V W (algebraMap R V x))) =
        f (algebraMap D KD (algebraMap R D x)) := by
      rw [← IsScalarTower.algebraMap_apply R V W,
        IsScalarTower.algebraMap_apply R D W,
        ← IsScalarTower.algebraMap_apply D W KD]
    _ = f (algebraMap K KD (algebraMap R K x)) :=
      congrArg f (DFunLike.congr_fun hBase x).symm
    _ = g (algebraMap K L (algebraMap R K x)) :=
      DFunLike.congr_fun hComponent (algebraMap R K x)
    _ = g (algebraMap K L (algebraMap V K (algebraMap R V x))) := by
      rw [← IsScalarTower.algebraMap_apply R V K]

/-- Choose a post-root normalization prime and globalize it, retaining both
its height-one branch and a containing closed normalization prime. -/
private theorem postRootNormalizationPrimes_exactPrimeSource
    {D KD M : Type*}
    [CommRing D] [IsDomain D] [IsLocalRing D]
    [Field KD] [Field M]
    [Algebra D KD] [IsFractionRing D KD]
    [Algebra KD M] [Algebra D M] [IsScalarTower D KD M]
    [Module.Finite D (integralClosure D M)]
    (qD : Ideal D) [qD.IsPrime] :
    let W := Localization.AtPrime qD
    let : Algebra W KD := localizationAtPrimeToFractionFieldAlgebra (K := KD) qD
    let : Algebra W M := localizationAtPrimeToExtensionAlgebra (K := KD) (L := M) qD
    let Cpost := integralClosure W M
    let Cglobal := integralClosure D M
    ∃ qPost : (IsLocalRing.maximalIdeal W).primesOver Cpost,
      ∃ qGlobal p : Ideal Cglobal,
        qGlobal.IsPrime ∧ qGlobal.LiesOver qD ∧
          localizedNormalizationPrime (K := KD) (L := M) qD qGlobal = qPost.1 ∧
          qGlobal.ramificationIdx D = qPost.1.ramificationIdx W ∧
          qGlobal ≤ p ∧ p.IsMaximal ∧ p.LiesOver (IsLocalRing.maximalIdeal D) := by
  classical
  intro W algWKD algWM Cpost Cglobal
  let : IsFractionRing W KD :=
    localizationAtPrimeToFractionField_isFractionRing (K := KD) qD
  let : IsScalarTower W KD M :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower (K := KD) (L := M) qD
  let : FaithfulSMul W Cpost :=
    (faithfulSMul_iff_algebraMap_injective W Cpost).mpr fun x z hxz ↦ by
      apply IsFractionRing.injective W KD
      apply (algebraMap KD M).injective
      have hM := congrArg (fun c : Cpost ↦ (c : M)) hxz
      change algebraMap W M x = algebraMap W M z at hM
      simpa only [IsScalarTower.algebraMap_apply W KD M] using hM
  obtain ⟨qPostIdeal, hqPostMax, hqPostOver⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (R := W) (S := Cpost) (IsLocalRing.maximalIdeal W)
  let qPost : (IsLocalRing.maximalIdeal W).primesOver Cpost :=
    ⟨qPostIdeal, hqPostMax.isPrime, hqPostOver⟩
  let : qPost.1.IsPrime := qPost.2.1
  let : qPost.1.LiesOver (IsLocalRing.maximalIdeal W) := qPost.2.2
  let : Algebra.IsIntegral D Cglobal := Algebra.IsIntegral.of_finite D Cglobal
  have hqDMax : qD ≤ IsLocalRing.maximalIdeal D :=
    IsLocalRing.le_maximalIdeal_of_isPrime qD
  obtain ⟨qGlobal, p, hqGlobalPrime, hqGlobalOver,
      hqGlobalLocal, hqGlobalRam, hqGlobalLe,
      hpPrime, hpOver⟩ :=
    EtaleFundamentalGroups.exists_normalizationPrimes_over_largerPrime_of_localized
      (A := D) (K := KD) (L := M)
      qD (IsLocalRing.maximalIdeal D) hqDMax qPost.1 qPost.2.1 qPost.2.2
  have hpMax : p.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under
      (R := D) (S := Cglobal) p <| by
        rw [← hpOver.over]
        exact IsLocalRing.maximalIdeal.isMaximal D
  exact ⟨qPost, qGlobal, p, hqGlobalPrime, hqGlobalOver,
    hqGlobalLocal, hqGlobalRam, hqGlobalLe, hpMax, hpOver⟩

/-- Contract a retained post-root prime along a literal field embedding.
The original branch-index theorem supplies the index for every contracted
normalization prime; the contraction itself is constructed here. -/
private theorem selectedPrimeContraction_exactPrimeSource
    {V W L M : Type*} {N : ℕ}
    [CommRing V] [IsDomain V] [IsLocalRing V]
    [CommRing W] [IsDomain W] [IsLocalRing W]
    [Field L] [Field M]
    [algVW : Algebra V W] [IsLocalHom (algebraMap V W)]
    [algVL : Algebra V L] [algWM : Algebra W M]
    (gLM : L →+* M)
    (hLM : gLM.comp (algebraMap V L) =
      (algebraMap W M).comp (algebraMap V W))
    (qPost : (IsLocalRing.maximalIdeal W).primesOver (integralClosure W M))
    (hExact : ∀ Q : (IsLocalRing.maximalIdeal V).primesOver (integralClosure V L),
      Ideal.ramificationIdx (S := integralClosure V L) Q.1 V = N) :
    let Csel := integralClosure V L
    let Cpost := integralClosure W M
    let : Algebra V Cpost :=
      ((algebraMap W Cpost).comp (algebraMap V W)).toAlgebra
    ∃ φ : Csel →ₐ[V] Cpost,
      ∃ Q : (IsLocalRing.maximalIdeal V).primesOver Csel,
        qPost.1.comap φ.toRingHom = Q.1 ∧
          (∀ z : Csel, ((φ z : Cpost) : M) = gLM (z : L)) ∧
          Ideal.ramificationIdx (S := Csel) Q.1 V = N := by
  classical
  intro Csel Cpost algVCpost
  let : Algebra V M := ((algebraMap W M).comp (algebraMap V W)).toAlgebra
  let : IsScalarTower V W M := IsScalarTower.of_algebraMap_eq' rfl
  let fLM : L →ₐ[V] M :=
    { toRingHom := gLM
      commutes' := fun z ↦ DFunLike.congr_fun hLM z }
  let φ : Csel →ₐ[V] Cpost :=
    EtaleFundamentalGroups.integralClosureToCompositumAlgHom
      (A := V) (B := W) (L := L) (Ω := M) fLM
  let QIdeal := qPost.1.comap φ.toRingHom
  have hQPrime : QIdeal.IsPrime := qPost.2.1.comap φ.toRingHom
  have hMaxWV : (IsLocalRing.maximalIdeal W).LiesOver
      (IsLocalRing.maximalIdeal V) := by
    apply (Ideal.liesOver_iff _ _).mpr
    exact (IsLocalRing.maximalIdeal_comap (algebraMap V W)).symm
  let : SMul W Cpost := (inferInstance : Algebra W Cpost).toSMul
  let : SMul V Cpost := (inferInstance : Algebra V Cpost).toSMul
  let : IsScalarTower V W Cpost := IsScalarTower.of_algebraMap_eq' rfl
  let : qPost.1.IsPrime := qPost.2.1
  let : qPost.1.LiesOver (IsLocalRing.maximalIdeal W) := qPost.2.2
  let : qPost.1.LiesOver (IsLocalRing.maximalIdeal V) :=
    Ideal.LiesOver.trans qPost.1 (IsLocalRing.maximalIdeal W) (IsLocalRing.maximalIdeal V)
  let algCC : Algebra Csel Cpost := φ.toAlgebra
  let : SMul Csel Cpost := algCC.toSMul
  let : IsScalarTower V Csel Cpost :=
    IsScalarTower.of_algebraMap_eq fun z ↦ (φ.commutes z).symm
  have hQOverV : QIdeal.LiesOver (IsLocalRing.maximalIdeal V) := by
    let : qPost.1.LiesOver QIdeal := ⟨rfl⟩
    exact Ideal.LiesOver.tower_bot qPost.1 QIdeal (IsLocalRing.maximalIdeal V)
  let Q : (IsLocalRing.maximalIdeal V).primesOver Csel := ⟨QIdeal, hQPrime, hQOverV⟩
  refine ⟨φ, Q, rfl, ?_, hExact Q⟩
  intro z
  exact EtaleFundamentalGroups.integralClosureToCompositumAlgHom_coe
    (A := V) (B := W) (L := L) (Ω := M) fLM z
/-- Compute the exact prefix-normalization index before introducing the
post-root localization actions.  The finite-etale prefix and its unique
selected prime are constructed from the geometric Galois cover. -/
private theorem prefixNormalizationRamification_exactPrimeSource
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Module.Finite A (integralClosure A L)]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (hCharZero : CharZero (A ⧸ Ideal.span ({t i} : Set A)))
    (σ : Equiv.Perm (Fin d))
    (hgeometryB :
      let e := heightTwoOtherBranchGaloisRamificationIndex (K := K) (L := L) t hNC i
      let R := Localization.AtPrime P
      let n := heightTwoConditionalOtherExponent t i r P e σ
      let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
      let B := iteratedRadical R d n a
      let yB := algebraMap R B (algebraMap A R (t i))
      IsRegularLocalRing B ∧ IsDomain B ∧
        ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞) ∧ Prime yB ∧
          IsDomain (B ⧸ Ideal.span ({yB} : Set B)) ∧
          IsRegularLocalRing (B ⧸ Ideal.span ({yB} : Set B))) :
    let e := heightTwoOtherBranchGaloisRamificationIndex (K := K) (L := L) t hNC i
    let N := heightTwoSelectedBranchGaloisRamificationIndex (K := K) (L := L) t hNC i
    let R := Localization.AtPrime P
    let n := heightTwoConditionalOtherExponent t i r P e σ
    let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
    let B := iteratedRadical R d n a
    let y := algebraMap A R (t i)
    let yB := algebraMap R B y
    let : IsDomain B := hgeometryB.2.1
    let : IsRegularLocalRing B := hgeometryB.1
    let hn := heightTwoConditionalOtherExponent_pos_of_pos t i r P e
      (heightTwoOtherBranchGaloisRamificationIndex_pos (K := K) (L := L) t hNC i) σ
    let : Module.FaithfullyFlat R B := faithfullyFlat_iteratedRadical n a hn
    let : FaithfulSMul R B := Module.FaithfullyFlat.faithfulSMul
    let : Algebra R K := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    let : IsFractionRing R K := localizationAtPrimeToFractionField_isFractionRing (K := K) P
    let KB := FractionRing B
    let : FaithfulSMul R KB := FaithfulSMul.trans R B KB
    let : Algebra K KB := chosenFractionFieldToFaithfulFieldAlgebra (R := R) (K := K) (F := KB)
    ∀ (m : Ideal (KB ⊗[K] L)) (hm : m.IsMaximal),
      let : m.IsMaximal := hm
      let M₀ := GenericTensorFieldComponent m
      let : Algebra B M₀ := genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      let : SMul B M₀ := (genericTensorFieldComponentLeftScalarAlgebra (R := B) m).toSMul
      let pR := (Ideal.span ({t i} : Set A)).map (algebraMap A R)
      let qB := Ideal.span ({yB} : Set B)
      let : pR.IsPrime := by
        let : (Ideal.span ({t i} : Set A)).IsPrime :=
          Ideal.isPrime_span_singleton_of_prime (hNC.2.2.2.1 i hi)
        exact Ideal.isPrime_map_of_isLocalizationAtPrime P
          (P.span_singleton_le_iff_mem.mpr htiP)
      let : qB.IsPrime := Ideal.isPrime_span_singleton_of_prime hgeometryB.2.2.2.1
      let : qB.LiesOver pR := by
        constructor
        simpa only [pR, qB, yB, y, Ideal.map_span, Ideal.map_map,
          Set.image_singleton, RingHom.comp_apply] using
          (Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) pR).symm
      ∀ qPrefix : Ideal (integralClosure B M₀), qPrefix.IsPrime →
        qPrefix.LiesOver qB → qPrefix.ramificationIdx B = N := by
  classical
  intro e N R n a B y yB domainB regularB hn flatRB faithfulRB algRK fracRK KB faithfulRKB algKKB
    m hm maximalM M₀ algBM₀ smulBM₀ pR qB hpR hqB hqBpR
  let V := Localization.AtPrime pR
  let : IsScalarTower R K KB :=
    chosenFractionFieldToFaithfulField_isScalarTower (R := R) (K := K) (F := KB)
  let : IsScalarTower R B KB := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra V K := localizationAtPrimeToFractionFieldAlgebra (K := K) pR
  let : IsFractionRing V K := localizationAtPrimeToFractionField_isFractionRing (K := K) pR
  let : Algebra V L := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) pR
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower (K := K) (L := L) pR
  intro qPrefix hqPrefixPrime hqPrefixOver
  have hpRSpan :
      pR = Ideal.span ({algebraMap A R (t i)} : Set R) := by
    simp only [pR, Ideal.map_span, Set.image_singleton]
  let Wpre := Localization.AtPrime qB
  let : Algebra V Wpre :=
    Localization.AtPrime.algebraOfLiesOver pR qB
  let : IsLocalHom (algebraMap V Wpre) := inferInstance
  let : Module.Finite R B := finite_iteratedRadical n a hn
  let : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  have hpRMap : pR.map (algebraMap R B) = qB := by
    simp only [pR, qB, yB, y, Ideal.map_span, Set.image_singleton]
  have hqBUnique : pR.primesOver B = {qB} := by
    ext J
    constructor
    · rintro ⟨hJPrime, hJOver⟩
      have hqBJ : qB ≤ J := by
        rw [← hpRMap, Ideal.map_le_iff_le_comap, hJOver.over]
      have hJB : J ≤ qB := by
        by_contra hnot
        have hlt : qB < J := by
          apply lt_of_le_of_ne hqBJ
          intro hEq
          apply hnot
          rw [← hEq]
        have hcomap :=
          Ideal.IsIntegral.under_lt_under (R := R) (A := B) hlt
        have hqBComap :
            Ideal.comap (algebraMap R B) qB = pR :=
          (inferInstance : qB.LiesOver pR).over.symm
        have hJComap :
            Ideal.comap (algebraMap R B) J = pR :=
          hJOver.over.symm
        simp only [hqBComap, hJComap] at hcomap
        exact (lt_irrefl pR) hcomap
      exact Set.mem_singleton_iff.mpr (le_antisymm hJB hqBJ)
    · intro hJ
      rw [Set.mem_singleton_iff] at hJ
      subst J
      exact ⟨inferInstance, inferInstance⟩
  let : IsLocalization
      (Algebra.algebraMapSubmonoid B pR.primeCompl) Wpre :=
    EtaleFundamentalGroups.isLocalization_localizationAtPrime_of_primesOver_eq_singleton
      hqBUnique
  let Tloc := Localization
    (Algebra.algebraMapSubmonoid B pR.primeCompl)
  let : Algebra V Tloc := localizationAlgebra pR.primeCompl B
  let : IsScalarTower R V Tloc :=
    isScalarTower_localizationAlgebra pR.primeCompl B
  let eB : Tloc ≃ₐ[B] Wpre :=
    IsLocalization.algEquiv
      (Algebra.algebraMapSubmonoid B pR.primeCompl) Tloc Wpre
  let eV : Tloc ≃ₐ[V] Wpre :=
    { toRingEquiv := eB.toRingEquiv
      commutes' := fun z ↦ by
        have hmaps :
            eB.toRingHom.comp (algebraMap V Tloc) =
              algebraMap V Wpre := by
          apply IsLocalization.ringHom_ext pR.primeCompl
          ext x
          simp only [RingHom.comp_apply]
          rw [← IsScalarTower.algebraMap_apply R V Tloc,
            ← IsScalarTower.algebraMap_apply R V Wpre,
            IsScalarTower.algebraMap_apply R B Tloc,
            IsScalarTower.algebraMap_apply R B Wpre]
          exact eB.commutes (algebraMap R B x)
        exact RingHom.congr_fun hmaps z }
  let aV : Fin d → V := fun k ↦ algebraMap R V (a k)
  let Epre := iteratedRadical V d n aV
  have hPrefixFiniteEtale :
      Module.Finite V Epre ∧ Module.FaithfullyFlat V Epre ∧
        Algebra.Etale V Epre := by
    simpa only [e, n, R, a, V, aV, Epre] using
      (heightTwoGaloisOtherRootPrefix_finiteEtale_at_mappedSelectedBranch
        (K := K) (L := L) hNC i hi P hP htiP
        hCharZero σ pR hpRSpan)
  let : Module.Finite V Epre := hPrefixFiniteEtale.1
  let : Algebra.Etale V Epre := hPrefixFiniteEtale.2.2
  let eBase : (V ⊗[R] B) ≃ₐ[V] Epre :=
    iteratedRadicalBaseChangeAlgEquiv n a
  let eTensorLoc : (V ⊗[R] B) ≃ₐ[V] Tloc :=
    Localization.tensorRightAlgEquiv pR.primeCompl B
  let ePre : Epre ≃ₐ[V] Wpre :=
    eBase.symm.trans (eTensorLoc.trans eV)
  let : Module.Finite V Wpre :=
    Module.Finite.equiv ePre.toLinearEquiv
  let : Algebra.Etale V Wpre := Algebra.Etale.of_equiv ePre
  let : Algebra Wpre KB :=
    localizationAtPrimeToFractionFieldAlgebra (K := KB) qB
  let : IsScalarTower B Wpre KB :=
    localizationAtPrimeToFractionField_isScalarTower (K := KB) qB
  let : IsFractionRing Wpre KB :=
    localizationAtPrimeToFractionField_isFractionRing (K := KB) qB
  let : Algebra V KB :=
    ((algebraMap Wpre KB).comp (algebraMap V Wpre)).toAlgebra
  let : IsScalarTower V Wpre KB :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R V K :=
    localizationAtPrimeToFractionField_isScalarTower (K := K) pR
  have hVKKb : IsScalarTower V K KB := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext pR.primeCompl
    ext x
    change algebraMap Wpre KB (algebraMap V Wpre (algebraMap R V x)) =
      algebraMap K KB (algebraMap V K (algebraMap R V x))
    rw [← IsScalarTower.algebraMap_apply R V Wpre,
      IsScalarTower.algebraMap_apply R B Wpre,
      ← IsScalarTower.algebraMap_apply B Wpre KB,
      ← IsScalarTower.algebraMap_apply R B KB,
      ← IsScalarTower.algebraMap_apply R V K,
      ← IsScalarTower.algebraMap_apply R K KB]
  apply retainedIntermediateNormalizationPrime_ramificationIdx_eq
    (B := B) (V := V) (K := K) (KB := KB) (L := L)
    (N := N) qB (m := m)
  · intro z
    rw [← IsScalarTower.algebraMap_apply V K KB,
      ← IsScalarTower.algebraMap_apply V Wpre KB]
  · intro Qauto
    simpa only [N, R, pR, V,
      heightTwoSelectedBranchGaloisRamificationIndex] using
      (
  localNormalizationPrime_ramificationIdx_eq_splitStrictNormalCrossingsGaloisIndex_at_largerPrime
        (K := K) (L := L) hNC i hi P htiP Qauto)
  · exact hqPrefixPrime
  · exact hqPrefixOver

private theorem
    galoisFullRootCover_selectedComponent_exactPrimeSource_constructed
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Module.Finite A (integralClosure A L)]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (hCharZero : ∀ j, j.1 < r →
      CharZero (A ⧸ Ideal.span ({t j} : Set A)))
    (hAway : (Localization.awayMap
      (algebraMap A (integralClosure A L)) f).Etale) :
    let e := heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let N := heightTwoSelectedBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    ∃ σ : Equiv.Perm (Fin d),
      let R := Localization.AtPrime P
      let n := heightTwoConditionalOtherExponent t i r P e σ
      let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
      let B := iteratedRadical R d n a
      let y : R := algebraMap A R (t i)
      let yB : B := algebraMap R B y
      let F : B[X] := X ^ N - C yB
      let D := AdjoinRoot F
      ∃ hgeometryB : IsRegularLocalRing B ∧ IsDomain B ∧
          ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞) ∧ Prime yB ∧
          IsDomain (B ⧸ Ideal.span ({yB} : Set B)) ∧
          IsRegularLocalRing (B ⧸ Ideal.span ({yB} : Set B)),
        ∃ hgeometryD : IsRegularLocalRing D ∧ IsDomain D ∧
            ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞) ∧
            Prime (AdjoinRoot.root F),
          let : IsRegularLocalRing B := hgeometryB.1
          let : IsDomain B := hgeometryB.2.1
          let : IsIntegrallyClosed B :=
            SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
              hgeometryB.2.2.1
          let : IsRegularLocalRing D := hgeometryD.1
          let : IsDomain D := hgeometryD.2.1
          let : IsIntegrallyClosed D :=
            SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
              hgeometryD.2.2.1
          let hn : ∀ k, 0 < n k :=
            heightTwoConditionalOtherExponent_pos_of_pos t i r P e
              (heightTwoOtherBranchGaloisRamificationIndex_pos
                (K := K) (L := L) t hNC i) σ
          let hN : 0 < N :=
            heightTwoSelectedBranchGaloisRamificationIndex_pos
              (K := K) (L := L) t hNC i
          let : Module.Finite B D := by
            simpa only [D, F] using
              (monic_X_pow_sub_C yB hN.ne').finite_adjoinRoot
          let : Algebra.IsIntegral B D := Algebra.IsIntegral.of_finite B D
          let : Module.FaithfullyFlat R B :=
            faithfullyFlat_iteratedRadical n a hn
          let : FaithfulSMul R B := Module.FaithfullyFlat.faithfulSMul
          let : Module.FaithfullyFlat B D :=
            faithfullyFlat_adjoinRoot_X_pow_sub_C hN yB
          let : FaithfulSMul B D := Module.FaithfullyFlat.faithfulSMul
          let : FaithfulSMul R D := FaithfulSMul.trans R B D
          let : Algebra R K :=
            localizationAtPrimeToFractionFieldAlgebra (K := K) P
          let : IsFractionRing R K :=
            localizationAtPrimeToFractionField_isFractionRing (K := K) P
          let KB := FractionRing B
          let KD := FractionRing D
          let : FaithfulSMul R KB := FaithfulSMul.trans R B KB
          let : FaithfulSMul R KD := FaithfulSMul.trans R D KD
          let : FaithfulSMul B KD := FaithfulSMul.trans B D KD
          let : Algebra K KB :=
            chosenFractionFieldToFaithfulFieldAlgebra
              (R := R) (K := K) (F := KB)
          let : Algebra K KD :=
            galoisFullRootCoverFractionFieldAlgebra n a hn N hN y
          let : Algebra KB KD := FractionRing.liftAlgebra B KD
          ∃ hTower : IsScalarTower K KB KD,
            let : IsScalarTower K KB KD := hTower
            ∃ hFin : FiniteDimensional KB KD,
              let : FiniteDimensional KB KD := hFin
              let m := genericTensorMaximalIdeal
                (K := K) (K' := KD) (L := L)
              let : m.IsMaximal := genericTensorMaximalIdeal_isMaximal
              let n₀ := genericTensorTowerIntermediateIdeal
                (K := K) (F := KB) (F' := KD) (L := L) m
              let : n₀.IsMaximal :=
                genericTensorTowerIntermediateIdeal_isMaximal
                  (K := K) (F := KB) (F' := KD) (L := L) m
              let M₀ := GenericTensorFieldComponent n₀
              let : Algebra B M₀ :=
                genericTensorFieldComponentLeftScalarAlgebra (R := B) n₀
              let : SMul B M₀ :=
                (genericTensorFieldComponentLeftScalarAlgebra
                  (R := B) n₀).toSMul
              let : IsScalarTower B KB M₀ :=
                IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
              let M := GenericTensorFieldComponent m
              let : Algebra D M :=
                genericTensorFieldComponentLeftScalarAlgebra (R := D) m
              let : SMul D M :=
                (genericTensorFieldComponentLeftScalarAlgebra
                  (R := D) m).toSMul
              let : IsScalarTower D KD M :=
                IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
              let pR := (Ideal.span ({t i} : Set A)).map
                (algebraMap A R)
              let qB := Ideal.span ({yB} : Set B)
              let qD := Ideal.span ({AdjoinRoot.root F} : Set D)
              let : pR.IsPrime := by
                let : (Ideal.span ({t i} : Set A)).IsPrime :=
                  Ideal.isPrime_span_singleton_of_prime
                    (hNC.2.2.2.1 i hi)
                exact Ideal.isPrime_map_of_isLocalizationAtPrime P
                  (P.span_singleton_le_iff_mem.mpr htiP)
              let : qB.IsPrime :=
                Ideal.isPrime_span_singleton_of_prime hgeometryB.2.2.2.1
              let : qD.IsPrime :=
                Ideal.isPrime_span_singleton_of_prime hgeometryD.2.2.2
              let : qB.LiesOver pR := by
                constructor
                simpa only [pR, qB, yB, y, Ideal.map_span,
                  Ideal.map_map, Set.image_singleton,
                  RingHom.comp_apply] using
                  (Ideal.comap_map_eq_self_of_faithfullyFlat
                    (B := B) pR).symm
              let : qD.LiesOver qB :=
                span_root_liesOver_span_radicand hN hgeometryB.2.2.2.1
              let : qD.LiesOver pR := Ideal.LiesOver.trans qD qB pR
              let V := Localization.AtPrime pR
              let W := Localization.AtPrime qD
              let : Algebra V W :=
                Localization.AtPrime.algebraOfLiesOver pR qD
              let : IsLocalHom (algebraMap V W) := inferInstance
              let : Algebra V K :=
                localizationAtPrimeToFractionFieldAlgebra (K := K) pR
              let : Algebra V L :=
                localizationAtPrimeToExtensionAlgebra
                  (K := K) (L := L) pR
              let : Algebra W KD :=
                localizationAtPrimeToFractionFieldAlgebra (K := KD) qD
              let : Algebra W M :=
                localizationAtPrimeToExtensionAlgebra
                  (K := KD) (L := M) qD
              let : Algebra L M := genericTensorFieldComponentRightAlgebra m
              let : Algebra V M :=
                ((algebraMap W M).comp (algebraMap V W)).toAlgebra
              let Csel := integralClosure V L
              let Cpost := integralClosure W M
              let Cglobal := integralClosure D M
              let : Algebra B Cglobal :=
                ((algebraMap D Cglobal).comp (algebraMap B D)).toAlgebra
              let : Algebra V Cpost :=
                ((algebraMap W Cpost).comp (algebraMap V W)).toAlgebra
              ∃ qPost : (IsLocalRing.maximalIdeal W).primesOver Cpost,
                ∃ qGlobal p : Ideal Cglobal,
                  qGlobal.IsPrime ∧ qGlobal.LiesOver qD ∧
                    localizedNormalizationPrime
                        (K := KD) (L := M) qD qGlobal = qPost.1 ∧
                    qGlobal.ramificationIdx D =
                      qPost.1.ramificationIdx W ∧
                    qGlobal.ramificationIdx B = N ∧
                    qGlobal ≤ p ∧ p.IsMaximal ∧
                    p.LiesOver (IsLocalRing.maximalIdeal D) ∧
                    let qPrefix :=
                      genericTensorTowerIntermediateNormalizationPrime
                        (A := B) (B := D) (K := K) (F := KB)
                        (F' := KD) (L := L) m qGlobal
                    let qClosed :=
                      genericTensorTowerIntermediateNormalizationPrime
                        (A := B) (B := D) (K := K) (F := KB)
                        (F' := KD) (L := L) m p
                    qGlobal.comap
                        (genericTensorTowerIntermediateNormalizationAlgHom
                          (A := B) (B := D) (K := K) (F := KB)
                          (F' := KD) (L := L) m).toRingHom = qPrefix ∧
                      qPrefix.IsPrime ∧ qPrefix.LiesOver qB ∧
                      qPrefix.ramificationIdx B = N ∧
                      qPrefix ≤ qClosed ∧ qClosed.IsMaximal ∧
                      qClosed.LiesOver (IsLocalRing.maximalIdeal B) ∧
                      ∃ φ : Csel →ₐ[V] Cpost,
                        ∃ Q : (IsLocalRing.maximalIdeal V).primesOver Csel,
                          qPost.1.comap φ.toRingHom = Q.1 ∧
                            (∀ z : Csel,
                              (((φ z : Cpost) : M)) =
                                algebraMap L M (z : L)) ∧
                            Ideal.ramificationIdx (S := Csel) Q.1 V = N ∧
                            (Localization.awayMap
                              (algebraMap B (integralClosure B M₀)) yB).Etale ∧
                            Module.Finite D (integralClosure D M) ∧
                              Algebra.Etale D (integralClosure D M) := by
  classical
  intro e N
  obtain ⟨σ, hgeometryB, hgeometryD, _hTowerCombined,
      _hFinCombined, hcomponentForAll⟩ :=
    splitStrictNormalCrossings_heightTwo_galoisPrefix_selectedAway_fullRoot_fixedComponent_etale
      (A := A) (K := K) (L := L) (d := d) (r := r)
      (f := f) (t := t) hNC i hi P hP htiP hCharZero hAway
  refine ⟨σ, ?_⟩
  intro R n a B y yB F D
  refine ⟨hgeometryB, hgeometryD, ?_⟩
  intro regB domainB closedB regD domainD closedD hn hN
    finiteBD integralBD ffRB faithfulRB ffBD faithfulBD faithfulRD
    algRK fracRK KB KD faithfulRKB faithfulRKD faithfulBKD algKKB algKKD algKBKD
  let : IsScalarTower A R K :=
    localizationAtPrimeToFractionField_isScalarTower (K := K) P
  let : IsScalarTower R K KB :=
    chosenFractionFieldToFaithfulField_isScalarTower
      (R := R) (K := K) (F := KB)
  let : IsScalarTower R K KD :=
    galoisFullRootCoverFractionField_isScalarTower n a hn N hN y
  let : IsScalarTower R B KB := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B D KD := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R D KD := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R B KD := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B KB KD :=
    FractionRing.isScalarTower_liftAlgebra B KD
  refine ⟨_hTowerCombined, ?_⟩
  intro towerKKBKD
  refine ⟨_hFinCombined, ?_⟩
  intro finiteKBKD m hm n₀ hn₀ M₀ algBM₀ smulBM₀ towerBKBM₀
    M algDM smulDM towerDKDM
  have hcomponent :
      (Localization.awayMap
          (algebraMap B (integralClosure B M₀)) yB).Etale ∧
        Module.Finite D (integralClosure D M) ∧
          Algebra.Etale D (integralClosure D M) :=
    hcomponentForAll m inferInstance
  intro pR qB qD hpR hqB hqD hqBpR hqDqB hqDpR V W
    algVW localVW algVK algVL algWKD algWM algLM algVM
  have hPrefixRamification :
      ∀ qPrefix : Ideal (integralClosure B M₀), qPrefix.IsPrime →
        qPrefix.LiesOver qB → qPrefix.ramificationIdx B = N :=
    prefixNormalizationRamification_exactPrimeSource
      (K := K) (L := L) hNC i hi P hP htiP (hCharZero i hi) σ hgeometryB
      n₀ inferInstance
  intro Csel Cpost Cglobal algBCglobal algVCpost
  let : IsScalarTower B D Cglobal := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite D Cglobal := hcomponent.2.1
  obtain ⟨qPost, qGlobal, p, hqGlobalPrime, hqGlobalOver,
      hqGlobalLocal, hqGlobalRam, hqGlobalLe, hpMax, hpOver⟩ :=
    postRootNormalizationPrimes_exactPrimeSource (D := D) (KD := KD) (M := M) qD
  have hqDRam : qD.ramificationIdx B = N := by
    let : IsRegularRing B :=
      EtaleFundamentalGroups.isRegularRing_of_isRegularLocalRing_dimension_two
        hgeometryB.2.2.1
    let U := Localization.AtPrime qB
    let : Algebra U W :=
      Localization.AtPrime.algebraOfLiesOver qB qD
    let : IsDomain W := by
      simpa only [W, qD, D, F] using
        (adjoinRootLocalizationAtRootPrime_isDomain
          (R := B) hN hgeometryB.2.2.2.1)
    let hWDVR : IsDiscreteValuationRing W := by
      simpa only [W, qD, D, F] using
        (adjoinRootLocalizationAtRootPrime_isDiscreteValuationRing
          (R := B) hN hgeometryB.2.2.2.1)
    have hqBMapW : qB.map (algebraMap B W) =
        IsLocalRing.maximalIdeal W ^ N := by
      calc
        qB.map (algebraMap B W) =
            (qB.map (algebraMap B U)).map (algebraMap U W) := by
          rw [Ideal.map_map, IsScalarTower.algebraMap_eq B U W]
        _ = (IsLocalRing.maximalIdeal U).map (algebraMap U W) := by
          rw [Localization.AtPrime.map_eq_maximalIdeal]
        _ = IsLocalRing.maximalIdeal W ^ N := by
          simpa only [U, W, qB, qD, D, F] using
            (adjoinRootLocalizationAtRootPrime_maximalIdeal_map_eq_pow
              (R := B) hN hgeometryB.2.2.2.1)
    rw [Ideal.ramificationIdx_eq qB qD, hqBMapW,
      hWDVR.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]
  let : Algebra.Etale D Cglobal := hcomponent.2.2
  have hqGlobalRamDOne : qGlobal.ramificationIdx D = 1 :=
    Ideal.ramificationIdx_eq_one qGlobal D
  have hqGlobalRamB : qGlobal.ramificationIdx B = N := by
    calc
      qGlobal.ramificationIdx B =
          qD.ramificationIdx B * qGlobal.ramificationIdx D :=
        Ideal.ramificationIdx_tower qD qGlobal
      _ = N := by rw [hqDRam, hqGlobalRamDOne, mul_one]
  refine ⟨qPost, qGlobal, p, hqGlobalPrime, hqGlobalOver,
    hqGlobalLocal, hqGlobalRam, hqGlobalRamB, hqGlobalLe, hpMax, hpOver, ?_⟩
  intro qPrefix qClosed
  have hqPrefixPrime : qPrefix.IsPrime :=
    genericTensorTowerIntermediateNormalizationPrime_isPrime
      (A := B) (B := D) (K := K) (F := KB) (F' := KD) (L := L)
      m qGlobal
  have hqClosedMax : qClosed.IsMaximal :=
    genericTensorTowerIntermediateNormalizationPrime_isMaximal
      (A := B) (B := D) (K := K) (F := KB) (F' := KD) (L := L)
      m p
  have hqClosedOver : qClosed.LiesOver (IsLocalRing.maximalIdeal B) :=
    genericTensorTowerIntermediateNormalizationPrime_liesOver_maximalIdeal
      (A := B) (B := D) (K := K) (F := KB) (F' := KD) (L := L)
      m p
  let g := genericTensorTowerIntermediateNormalizationAlgHom
    (A := B) (B := D) (K := K) (F := KB) (F' := KD) (L := L) m
  have hqGlobalComap : qGlobal.comap g.toRingHom = qPrefix :=
    genericTensorTowerIntermediateNormalizationAlgHom_comap_eq_prime
      (A := B) (B := D) (K := K) (F := KB) (F' := KD) (L := L)
      m qGlobal
  have hqGlobalOverB : qGlobal.LiesOver qB :=
    Ideal.LiesOver.trans qGlobal qD qB
  have hqPrefixOver : qPrefix.LiesOver qB := by
    have hmap :
        g.toRingHom.comp (algebraMap B (integralClosure B M₀)) =
          algebraMap B Cglobal := by
      apply RingHom.ext
      intro b
      exact g.commutes b
    constructor
    rw [Ideal.under_def, ← hqGlobalComap, Ideal.comap_comap, hmap]
    exact hqGlobalOverB.over
  have hqPrefixLe : qPrefix ≤ qClosed := by
    change qGlobal.comap g.toRingHom ≤ p.comap g.toRingHom
    exact Ideal.comap_mono hqGlobalLe
  have hBaseRing :
      (algebraMap K KD).comp (algebraMap R K) =
        (algebraMap D KD).comp (algebraMap R D) := by
    ext z
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R K KD,
      IsScalarTower.algebraMap_apply R D KD]
  have hTensorRing :
      (genericTensorFieldComponentLeft m).toRingHom.comp (algebraMap K KD) =
        (genericTensorFieldComponentRight m).toRingHom.comp (algebraMap K L) := by
    ext z
    exact ((genericTensorFieldComponentLeft m).commutes z).trans
      ((genericTensorFieldComponentRight m).commutes z).symm
  have hLocalRing := localizedComponentMaps_commute_exactPrimeSource
    (R := R) (D := D) (K := K) (KD := KD) (L := L) (M := M)
    pR qD (genericTensorFieldComponentLeft m).toRingHom
    (genericTensorFieldComponentRight m).toRingHom hBaseRing hTensorRing
  obtain ⟨φ, Q, hQComap, hQCoe, hExact⟩ :=
    selectedPrimeContraction_exactPrimeSource (N := N)
      (V := V) (W := W) (L := L) (M := M)
      (algVW := Localization.AtPrime.algebraOfLiesOver pR qD)
      (algVL := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) pR)
      (algWM := localizationAtPrimeToExtensionAlgebra (K := KD) (L := M) qD)
      (genericTensorFieldComponentRight m).toRingHom
      (RingHom.ext fun z ↦ (DFunLike.congr_fun hLocalRing z).symm)
      qPost (fun Qauto ↦ by
        simpa only [N, R, pR, V, Csel,
          heightTwoSelectedBranchGaloisRamificationIndex] using
          (
  localNormalizationPrime_ramificationIdx_eq_splitStrictNormalCrossingsGaloisIndex_at_largerPrime
            (K := K) (L := L) hNC i hi P htiP Qauto))
  refine ⟨hqGlobalComap, hqPrefixPrime, hqPrefixOver, ?_, hqPrefixLe,
    hqClosedMax, hqClosedOver,
    φ, Q, hQComap, ?_, hExact, hcomponent.1,
    hcomponent.2.1, hcomponent.2.2⟩
  · exact hPrefixRamification qPrefix hqPrefixPrime hqPrefixOver
  intro z
  exact hQCoe z

/-- The canonical full component retained by the combined prefix/full-root
theorem supplies, by literal contraction of a post-root normalization prime,
an original selected-branch normalization prime of exact Galois index.

The output also globalizes the selected post-root branch and follows it to
a closed normalization prime.  Thus the later completion can retain this
literal branch instead of selecting an unrelated closed factor.  The
height-one branch and that closed prime are then contracted along the same
canonical intermediate normalization map, with the resulting containment
retained explicitly.  The canonical intermediate tensor ideal and the two
purity inputs still belong to exactly the same final component. -/
theorem
    splitStrictNormalCrossings_heightTwo_galoisFullRootCover_selectedComponent_exactPrimeSource
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Module.Finite A (integralClosure A L)]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (hCharZero : ∀ j, j.1 < r →
      CharZero (A ⧸ Ideal.span ({t j} : Set A)))
    (hAway : (Localization.awayMap
      (algebraMap A (integralClosure A L)) f).Etale) :
    let e := heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let N := heightTwoSelectedBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    ∃ σ : Equiv.Perm (Fin d),
      let R := Localization.AtPrime P
      let n := heightTwoConditionalOtherExponent t i r P e σ
      let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
      let B := iteratedRadical R d n a
      let y : R := algebraMap A R (t i)
      let yB : B := algebraMap R B y
      let F : B[X] := X ^ N - C yB
      let D := AdjoinRoot F
      ∃ hgeometryB : IsRegularLocalRing B ∧ IsDomain B ∧
          ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞) ∧ Prime yB ∧
          IsDomain (B ⧸ Ideal.span ({yB} : Set B)) ∧
          IsRegularLocalRing (B ⧸ Ideal.span ({yB} : Set B)),
        ∃ hgeometryD : IsRegularLocalRing D ∧ IsDomain D ∧
            ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞) ∧
            Prime (AdjoinRoot.root F),
          let : IsRegularLocalRing B := hgeometryB.1
          let : IsDomain B := hgeometryB.2.1
          let : IsIntegrallyClosed B :=
            SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
              hgeometryB.2.2.1
          let : IsRegularLocalRing D := hgeometryD.1
          let : IsDomain D := hgeometryD.2.1
          let : IsIntegrallyClosed D :=
            SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
              hgeometryD.2.2.1
          let hn : ∀ k, 0 < n k :=
            heightTwoConditionalOtherExponent_pos_of_pos t i r P e
              (heightTwoOtherBranchGaloisRamificationIndex_pos
                (K := K) (L := L) t hNC i) σ
          let hN : 0 < N :=
            heightTwoSelectedBranchGaloisRamificationIndex_pos
              (K := K) (L := L) t hNC i
          let : Module.Finite B D := by
            simpa only [D, F] using
              (monic_X_pow_sub_C yB hN.ne').finite_adjoinRoot
          let : Algebra.IsIntegral B D := Algebra.IsIntegral.of_finite B D
          let : Module.FaithfullyFlat R B :=
            faithfullyFlat_iteratedRadical n a hn
          let : FaithfulSMul R B := Module.FaithfullyFlat.faithfulSMul
          let : Module.FaithfullyFlat B D :=
            faithfullyFlat_adjoinRoot_X_pow_sub_C hN yB
          let : FaithfulSMul B D := Module.FaithfullyFlat.faithfulSMul
          let : FaithfulSMul R D := FaithfulSMul.trans R B D
          let : Algebra R K :=
            localizationAtPrimeToFractionFieldAlgebra (K := K) P
          let : IsFractionRing R K :=
            localizationAtPrimeToFractionField_isFractionRing (K := K) P
          let KB := FractionRing B
          let KD := FractionRing D
          let : FaithfulSMul R KB := FaithfulSMul.trans R B KB
          let : FaithfulSMul R KD := FaithfulSMul.trans R D KD
          let : FaithfulSMul B KD := FaithfulSMul.trans B D KD
          let : Algebra K KB :=
            chosenFractionFieldToFaithfulFieldAlgebra
              (R := R) (K := K) (F := KB)
          let : Algebra K KD :=
            galoisFullRootCoverFractionFieldAlgebra n a hn N hN y
          let : Algebra KB KD := FractionRing.liftAlgebra B KD
          ∃ hTower : IsScalarTower K KB KD,
            let : IsScalarTower K KB KD := hTower
            ∃ hFin : FiniteDimensional KB KD,
              let : FiniteDimensional KB KD := hFin
              let m := genericTensorMaximalIdeal
                (K := K) (K' := KD) (L := L)
              let : m.IsMaximal := genericTensorMaximalIdeal_isMaximal
              let n₀ := genericTensorTowerIntermediateIdeal
                (K := K) (F := KB) (F' := KD) (L := L) m
              let : n₀.IsMaximal :=
                genericTensorTowerIntermediateIdeal_isMaximal
                  (K := K) (F := KB) (F' := KD) (L := L) m
              let M₀ := GenericTensorFieldComponent n₀
              let : Algebra B M₀ :=
                genericTensorFieldComponentLeftScalarAlgebra (R := B) n₀
              let : SMul B M₀ :=
                (genericTensorFieldComponentLeftScalarAlgebra
                  (R := B) n₀).toSMul
              let : IsScalarTower B KB M₀ :=
                IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
              let M := GenericTensorFieldComponent m
              let : Algebra D M :=
                genericTensorFieldComponentLeftScalarAlgebra (R := D) m
              let : Algebra B M :=
                genericTensorFieldComponentLeftScalarAlgebra (R := B) m
              let : SMul D M :=
                (genericTensorFieldComponentLeftScalarAlgebra
                  (R := D) m).toSMul
              let : SMul B M :=
                (genericTensorFieldComponentLeftScalarAlgebra
                  (R := B) m).toSMul
              let : IsScalarTower B D M :=
                IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
              let : IsScalarTower D KD M :=
                IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
              let pR := (Ideal.span ({t i} : Set A)).map
                (algebraMap A R)
              let qB := Ideal.span ({yB} : Set B)
              let qD := Ideal.span ({AdjoinRoot.root F} : Set D)
              let : pR.IsPrime := by
                let : (Ideal.span ({t i} : Set A)).IsPrime :=
                  Ideal.isPrime_span_singleton_of_prime
                    (hNC.2.2.2.1 i hi)
                exact Ideal.isPrime_map_of_isLocalizationAtPrime P
                  (P.span_singleton_le_iff_mem.mpr htiP)
              let : qB.IsPrime :=
                Ideal.isPrime_span_singleton_of_prime hgeometryB.2.2.2.1
              let : qD.IsPrime :=
                Ideal.isPrime_span_singleton_of_prime hgeometryD.2.2.2
              let : qB.LiesOver pR := by
                constructor
                simpa only [pR, qB, yB, y, Ideal.map_span,
                  Ideal.map_map, Set.image_singleton,
                  RingHom.comp_apply] using
                  (Ideal.comap_map_eq_self_of_faithfullyFlat
                    (B := B) pR).symm
              let : qD.LiesOver qB :=
                span_root_liesOver_span_radicand hN hgeometryB.2.2.2.1
              let : qD.LiesOver pR := Ideal.LiesOver.trans qD qB pR
              let V := Localization.AtPrime pR
              let W := Localization.AtPrime qD
              let : Algebra V W :=
                Localization.AtPrime.algebraOfLiesOver pR qD
              let : IsLocalHom (algebraMap V W) := inferInstance
              let : Algebra V K :=
                localizationAtPrimeToFractionFieldAlgebra (K := K) pR
              let : Algebra V L :=
                localizationAtPrimeToExtensionAlgebra
                  (K := K) (L := L) pR
              let : Algebra W KD :=
                localizationAtPrimeToFractionFieldAlgebra (K := KD) qD
              let : Algebra W M :=
                localizationAtPrimeToExtensionAlgebra
                  (K := KD) (L := M) qD
              let : Algebra L M := genericTensorFieldComponentRightAlgebra m
              let : Algebra V M :=
                ((algebraMap W M).comp (algebraMap V W)).toAlgebra
              let Csel := integralClosure V L
              let Cpost := integralClosure W M
              let Cglobal := integralClosure D M
              let : Algebra B Cglobal :=
                ((algebraMap D Cglobal).comp (algebraMap B D)).toAlgebra
              let : Algebra V Cpost :=
                ((algebraMap W Cpost).comp (algebraMap V W)).toAlgebra
              ∃ qPost : (IsLocalRing.maximalIdeal W).primesOver Cpost,
                ∃ qGlobal p : Ideal Cglobal,
                  qGlobal.IsPrime ∧ qGlobal.LiesOver qD ∧
                    localizedNormalizationPrime
                        (K := KD) (L := M) qD qGlobal = qPost.1 ∧
                    qGlobal.ramificationIdx D =
                      qPost.1.ramificationIdx W ∧
                    qGlobal.ramificationIdx B = N ∧
                    qGlobal ≤ p ∧ p.IsMaximal ∧
                    p.LiesOver (IsLocalRing.maximalIdeal D) ∧
                    let qPrefix :=
                      genericTensorTowerIntermediateNormalizationPrime
                        (A := B) (B := D) (K := K) (F := KB)
                        (F' := KD) (L := L) m qGlobal
                    let qClosed :=
                      genericTensorTowerIntermediateNormalizationPrime
                        (A := B) (B := D) (K := K) (F := KB)
                        (F' := KD) (L := L) m p
                    qGlobal.comap
                        (genericTensorTowerIntermediateNormalizationAlgHom
                          (A := B) (B := D) (K := K) (F := KB)
                          (F' := KD) (L := L) m).toRingHom = qPrefix ∧
                      qPrefix.IsPrime ∧ qPrefix.LiesOver qB ∧
                      qPrefix.ramificationIdx B = N ∧
                      qPrefix ≤ qClosed ∧ qClosed.IsMaximal ∧
                      qClosed.LiesOver (IsLocalRing.maximalIdeal B) ∧
                      ∃ φ : Csel →ₐ[V] Cpost,
                        ∃ Q : (IsLocalRing.maximalIdeal V).primesOver Csel,
                          qPost.1.comap φ.toRingHom = Q.1 ∧
                            (∀ z : Csel,
                              (((φ z : Cpost) : M)) =
                                algebraMap L M (z : L)) ∧
                            Ideal.ramificationIdx (S := Csel) Q.1 V = N ∧
                            (Localization.awayMap
                              (algebraMap B (integralClosure B M₀)) yB).Etale ∧
                            Module.Finite D (integralClosure D M) ∧
                              Algebra.Etale D (integralClosure D M) := by
  exact galoisFullRootCover_selectedComponent_exactPrimeSource_constructed
    (K := K) (L := L) hNC i hi P hP htiP hCharZero hAway

end EtaleFundamentalGroups.Kummer

end
