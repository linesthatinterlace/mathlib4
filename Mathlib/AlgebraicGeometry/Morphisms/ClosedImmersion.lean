/-
Copyright (c) 2023 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Christian Merten, Jonas van der Schaaf
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!

# Closed immersions of schemes

A morphism of schemes `f : X ⟶ Y` is a closed immersion if the underlying map of topological spaces
is a closed immersion and the induced morphisms of stalks are all surjective.

## Main definitions

* `IsClosedImmersion` : The property of scheme morphisms stating `f : X ⟶ Y` is a closed immersion.

## TODO

* Show closed immersions are precisely the proper monomorphisms
* Define closed immersions of locally ringed spaces, where we also assume that the kernel of `O_X →
  f_*O_Y` is locally generated by sections as an `O_X`-module, and relate it to this file. See
  https://stacks.math.columbia.edu/tag/01HJ.

-/

universe v u

open CategoryTheory Opposite TopologicalSpace Topology

namespace AlgebraicGeometry

/-- A morphism of schemes `X ⟶ Y` is a closed immersion if the underlying
topological map is a closed embedding and the induced stalk maps are surjective. -/
@[mk_iff]
class IsClosedImmersion {X Y : Scheme} (f : X ⟶ Y) : Prop extends SurjectiveOnStalks f where
  base_closed : IsClosedEmbedding f.base

lemma Scheme.Hom.isClosedEmbedding {X Y : Scheme} (f : X.Hom Y)
    [IsClosedImmersion f] : IsClosedEmbedding f.base :=
  IsClosedImmersion.base_closed

namespace IsClosedImmersion

lemma eq_inf : @IsClosedImmersion = (topologically IsClosedEmbedding) ⊓
    @SurjectiveOnStalks := by
  ext X Y f
  rw [isClosedImmersion_iff, and_comm]
  rfl

lemma iff_isPreimmersion {X Y : Scheme} {f : X ⟶ Y} :
    IsClosedImmersion f ↔ IsPreimmersion f ∧ IsClosed (Set.range f.base) := by
  rw [isClosedImmersion_iff, isPreimmersion_iff, and_assoc, isClosedEmbedding_iff]

lemma of_isPreimmersion {X Y : Scheme} (f : X ⟶ Y) [IsPreimmersion f]
    (hf : IsClosed (Set.range f.base)) : IsClosedImmersion f :=
  iff_isPreimmersion.mpr ⟨‹_›, hf⟩

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] : IsPreimmersion f :=
  (iff_isPreimmersion.mp ‹_›).1

/-- Isomorphisms are closed immersions. -/
instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsClosedImmersion f where
  base_closed := Homeomorph.isClosedEmbedding <| TopCat.homeoOfIso (asIso f.base)
  surj_on_stalks := fun _ ↦ (ConcreteCategory.bijective_of_isIso _).2

instance (priority := low) {X Y : Scheme.{u}} [IsEmpty X] (f : X ⟶ Y) : IsClosedImmersion f :=
  .of_isPreimmersion _ (by rw [Set.range_eq_empty]; exact isClosed_empty)

instance : MorphismProperty.IsMultiplicative @IsClosedImmersion where
  id_mem _ := inferInstance
  comp_mem _ _ hf hg := ⟨hg.base_closed.comp hf.base_closed⟩

/-- Composition of closed immersions is a closed immersion. -/
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsClosedImmersion f]
    [IsClosedImmersion g] : IsClosedImmersion (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

/-- Composition with an isomorphism preserves closed immersions. -/
instance respectsIso : MorphismProperty.RespectsIso @IsClosedImmersion := by
  apply MorphismProperty.RespectsIso.mk <;> intro X Y Z e f hf <;> infer_instance

instance {X : Scheme} (I : X.IdealSheafData) : IsClosedImmersion I.subschemeι :=
  .of_isPreimmersion _ (I.range_subschemeι ▸ I.support.isClosed)

/-- Given two commutative rings `R S : CommRingCat` and a surjective morphism
`f : R ⟶ S`, the induced scheme morphism `specObj S ⟶ specObj R` is a
closed immersion. -/
theorem spec_of_surjective {R S : CommRingCat} (f : R ⟶ S) (h : Function.Surjective f) :
    IsClosedImmersion (Spec.map f) where
  base_closed := PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ h
  surj_on_stalks x := by
    haveI : (RingHom.toMorphismProperty (fun f ↦ Function.Surjective f)).RespectsIso := by
      rw [← RingHom.toMorphismProperty_respectsIso_iff]
      exact RingHom.surjective_respectsIso
    apply (MorphismProperty.arrow_mk_iso_iff
      (RingHom.toMorphismProperty (fun f ↦ Function.Surjective f))
      (Scheme.arrowStalkMapSpecIso f x)).mpr
    exact RingHom.surjective_localRingHom_of_surjective f.hom h x.asIdeal

/-- For any ideal `I` in a commutative ring `R`, the quotient map `specObj R ⟶ specObj (R ⧸ I)`
is a closed immersion. -/
instance spec_of_quotient_mk {R : CommRingCat.{u}} (I : Ideal R) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Any morphism between affine schemes that is surjective on global sections is a
closed immersion. -/
lemma of_surjective_of_isAffine {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (h : Function.Surjective (f.appTop)) : IsClosedImmersion f := by
  rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (arrowIsoSpecΓOfIsAffine f)]
  apply spec_of_surjective
  exact h

/--
If `f ≫ g` and `g` are closed immersions, then `f` is a closed immersion.
Also see `IsClosedImmersion.of_comp` for the general version
where `g` is only required to be separated.
-/
theorem of_comp_isClosedImmersion {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsClosedImmersion g]
    [IsClosedImmersion (f ≫ g)] : IsClosedImmersion f where
  base_closed := by
    have h := (f ≫ g).isClosedEmbedding
    simp only [Scheme.comp_coeBase, TopCat.coe_comp] at h
    refine .of_continuous_injective_isClosedMap (Scheme.Hom.continuous f) h.injective.of_comp ?_
    intro Z hZ
    rw [IsClosedEmbedding.isClosed_iff_image_isClosed g.isClosedEmbedding,
      ← Set.image_comp]
    exact h.isClosedMap _ hZ
  surj_on_stalks x := by
    have h := (f ≫ g).stalkMap_surjective x
    simp_rw [Scheme.stalkMap_comp] at h
    exact Function.Surjective.of_comp h

instance Spec_map_residue {X : Scheme.{u}} (x) : IsClosedImmersion (Spec.map (X.residue x)) :=
  IsClosedImmersion.spec_of_surjective (X.residue x)
    Ideal.Quotient.mk_surjective

instance (priority := low) {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] : IsAffineHom f :=
  isAffineHom_of_isInducing _ f.isClosedEmbedding.isInducing f.isClosedEmbedding.isClosed_range

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    IsIso f.toImage := by
  have := @of_comp_isClosedImmersion _ _ _ f.toImage f.imageι inferInstance
    (by rw [Scheme.Hom.toImage_imageι]; infer_instance)
  have : IsHomeomorph f.toImage.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨f.toImage.isEmbedding, by
      rw [← Set.range_eq_univ, ← f.toImage.isClosedEmbedding.isClosed_range.closure_eq]
      exact f.toImage.denseRange.closure_eq⟩
  refine isomorphisms_eq_stalkwise.ge _ ⟨?_, ?_⟩
  · exact inferInstanceAs (IsIso (TopCat.isoOfHomeo this.homeomorph).hom)
  · intro x
    refine ⟨?_, f.toImage.stalkMap_surjective x⟩
    change Function.Injective (CommRingCat.Hom.hom (((TopCat.Presheaf.stalkFunctor CommRingCat
      (f.toImage.base x)).map f.toImage.c) ≫ X.presheaf.stalkPushforward _ _ x))
    simp only [TopCat.Presheaf.stalkFunctor_obj, CommRingCat.hom_comp, RingHom.coe_comp]
    refine .comp ?_ (f.stalkFunctor_toImage_injective _)
    have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing CommRingCat
      (f := f.toImage.base) f.toImage.isEmbedding.isInducing X.presheaf x
    exact ((ConcreteCategory.isIso_iff_bijective _).mp this).1

/-- The category of closed subschemes is contravariantly equivalent
to the lattice of ideal sheaves. -/
noncomputable
def overEquivIdealSheafData (X : Scheme.{u}) :
    (MorphismProperty.Over @IsClosedImmersion ⊤ X)ᵒᵖ ≌ X.IdealSheafData where
  functor := (MorphismProperty.Over.forget _ _ _).op ⋙ X.kerFunctor
  inverse :=
  { obj I := .op <| .mk _ I.subschemeι inferInstance
    map {I J} h := (MorphismProperty.Over.homMk (Scheme.IdealSheafData.inclusion h.le)).op
    map_comp f g := Quiver.Hom.unop_inj (by ext1; simp) }
  unitIso := NatIso.ofComponents (fun Y ↦
    letI : IsClosedImmersion Y.unop.hom := Y.unop.prop
    ((MorphismProperty.Over.isoMk (asIso Y.unop.hom.toImage).symm).op)) fun {X Y} f ↦ by
      apply Quiver.Hom.unop_inj
      ext1
      dsimp
      rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq,
        ← cancel_mono (Scheme.IdealSheafData.subschemeι _)]
      simp
  counitIso := NatIso.ofComponents (fun I ↦ eqToIso (by simp))

lemma isIso_iff_ker_eq_bot {X Y : Scheme.{u}} {f : X ⟶ Y} [IsClosedImmersion f] :
    IsIso f ↔ f.ker = ⊥ := by
  refine ⟨fun _ ↦ f.ker_eq_bot_of_isIso, fun H ↦ ?_⟩
  have : IsIso f.imageι := by simpa [Scheme.Hom.imageι, Scheme.Hom.image] using H ▸ inferInstance
  exact f.toImage_imageι ▸ inferInstance

/-- The universal property of closed immersions:
For a closed immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose kernel
contains the kernel of `X` in `Z`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
noncomputable
def lift {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion f] (H : f.ker ≤ g.ker) : Y ⟶ X :=
  g.toImage ≫ Scheme.IdealSheafData.inclusion H ≫ inv f.toImage

@[reassoc (attr := simp)]
lemma lift_fac {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion f] (H : f.ker ≤ g.ker) : lift f g H ≫ f = g := by
  nth_rw 2 [← f.toImage_imageι]
  simp [lift, - Scheme.Hom.toImage_imageι, g.toImage_imageι]

end IsClosedImmersion

section Affine

variable {X Y : Scheme.{u}} [IsAffine Y] {f : X ⟶ Y}

open IsClosedImmersion LocallyRingedSpace

/-- If `f : X ⟶ Y` is a morphism of schemes with quasi-compact source and affine target,
`f` induces an injection on global sections, then `f` is dominant. -/
lemma isDominant_of_of_appTop_injective [CompactSpace X]
    (hfinj : Function.Injective (f.appTop)) :
    IsDominant f := by
  have : QuasiCompact f := HasAffineProperty.iff_of_isAffine.mpr ‹_›
  have : f.ker = ⊥ := Scheme.IdealSheafData.ext_of_isAffine
    (by simpa [f.ker_apply ⟨⊤, isAffineOpen_top Y⟩, ← RingHom.injective_iff_ker_eq_bot])
  exact ⟨by simpa only [Scheme.Hom.support_ker, Scheme.IdealSheafData.support_bot,
    Closeds.coe_top, ← dense_iff_closure_eq] using (congr((↑($this).support : Set Y)) :)⟩

@[deprecated (since := "2025-05-10")]
alias surjective_of_isClosed_range_of_injective := isDominant_of_of_appTop_injective

instance [CompactSpace X] : IsDominant X.toSpecΓ :=
  isDominant_of_of_appTop_injective (by
    simpa only [Scheme.toSpecΓ_appTop] using
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(X, ⊤)).hom).1)

/-- If `f : X ⟶ Y` is open, injective, `X` is quasi-compact and `Y` is affine, then `f` is stalkwise
injective if it is injective on global sections. -/
lemma stalkMap_injective_of_isOpenMap_of_injective [CompactSpace X]
    (hfopen : IsOpenMap f.base) (hfinj₁ : Function.Injective f.base)
    (hfinj₂ : Function.Injective (f.appTop)) (x : X) :
    Function.Injective (f.stalkMap x) := by
  let φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤) := f.appTop
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  have (i : 𝒰.J) : IsAffine (𝒰.obj i) := Scheme.isAffine_affineCover X _
  let res (i : 𝒰.J) : Γ(X, ⊤) ⟶ Γ(𝒰.obj i, ⊤) := (𝒰.map i).appTop
  refine stalkMap_injective_of_isAffine _ _ (fun (g : Γ(Y, ⊤)) h ↦ ?_)
  rw [TopCat.Presheaf.Γgerm, Scheme.stalkMap_germ_apply] at h
  obtain ⟨U, w, (hx : x ∈ U), hg⟩ :=
    X.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero ⊤ (φ g) ⟨x, trivial⟩ h
  obtain ⟨_, ⟨s, rfl⟩, hyv, bsle⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen Y)
    (show f.base x ∈ ⟨f.base '' U.carrier, hfopen U.carrier U.is_open'⟩ from ⟨x, by simpa⟩)
  let W (i : 𝒰.J) : TopologicalSpace.Opens (𝒰.obj i) := (𝒰.obj i).basicOpen ((res i) (φ s))
  have hwle (i : 𝒰.J) : W i ≤ (𝒰.map i)⁻¹ᵁ U := by
    change (𝒰.obj i).basicOpen ((𝒰.map i ≫ f).appTop s) ≤ _
    rw [← Scheme.preimage_basicOpen_top, Scheme.comp_coeBase, Opens.map_comp_obj]
    refine Scheme.Hom.preimage_le_preimage_of_le _
      (le_trans (f.preimage_le_preimage_of_le bsle) (le_of_eq ?_))
    simp [Set.preimage_image_eq _ hfinj₁]
  have h0 (i : 𝒰.J) : (𝒰.map i).appLE _ (W i) (by simp) (φ g) = 0 := by
    rw [← Scheme.Hom.appLE_map _ _ (homOfLE <| hwle i).op, ← Scheme.Hom.map_appLE _ le_rfl w.op]
    simp only [CommRingCat.comp_apply]
    rw [hg]
    simp only [map_zero]
  have h1 (i : 𝒰.J) : ∃ n, (res i) (φ (s ^ n * g)) = 0 := by
    obtain ⟨n, hn⟩ := exists_of_res_zero_of_qcqs_of_top (s := ((res i) (φ s))) (h0 i)
    exact ⟨n, by rwa [map_mul, map_mul, map_pow, map_pow]⟩
  have h2 : ∃ n, ∀ i, (res i) (φ (s ^ n * g)) = 0 := by
    choose fn hfn using h1
    refine ⟨Finset.sup Finset.univ fn, fun i ↦ ?_⟩
    rw [map_mul, map_pow, map_mul, map_pow]
    simp only [map_mul, map_pow, map_mul, map_pow] at hfn
    apply pow_mul_eq_zero_of_le (Finset.le_sup (Finset.mem_univ i)) (hfn i)
  obtain ⟨n, hn⟩ := h2
  apply germ_eq_zero_of_pow_mul_eq_zero (U := ⊤) ⟨f.base x, trivial⟩ hyv
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero] at hfinj₂
  exact hfinj₂ _ (Scheme.zero_of_zero_cover _ _ hn)

namespace IsClosedImmersion

/-- If `f` is a closed immersion with affine target such that the induced map on global
sections is injective, `f` is an isomorphism. -/
theorem isIso_of_injective_of_isAffine [IsClosedImmersion f]
    (hf : Function.Injective (f.appTop)) : IsIso f :=
  isIso_iff_ker_eq_bot.mpr (Scheme.IdealSheafData.ext_of_isAffine
    (by simpa [f.ker_apply ⟨⊤, isAffineOpen_top Y⟩, ← RingHom.injective_iff_ker_eq_bot]))

variable (f)

/-- If `f` is a closed immersion with affine target, the source is affine and
the induced map on global sections is surjective. -/
theorem isAffine_surjective_of_isAffine [IsClosedImmersion f] :
    IsAffine X ∧ Function.Surjective (f.appTop) := by
  refine ⟨isAffine_of_isAffineHom f, ?_⟩
  simp only [← f.toImage_imageι, Scheme.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
    Scheme.Hom.image, Scheme.Hom.imageι]
  rw [Scheme.Hom.appTop, Scheme.Hom.appTop, f.ker.subschemeι_app ⟨⊤, isAffineOpen_top Y⟩,
    CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).2.comp
    ((ConcreteCategory.bijective_of_isIso _).2.comp Ideal.Quotient.mk_surjective)

lemma Spec_iff {R : CommRingCat} {f : X ⟶ Spec R} :
    IsClosedImmersion f ↔ ∃ I : Ideal R, ∃ e : X ≅ Spec(R ⧸ I),
      f = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  constructor
  · intro H
    obtain ⟨h₁, h₂⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine f
    let φ := (Scheme.ΓSpecIso R).inv ≫ f.appTop
    refine ⟨RingHom.ker φ.1, Scheme.isoSpec _ ≪≫ Scheme.Spec.mapIso
        (.op (RingEquiv.ofBijective φ.1.kerLift ?_).toCommRingCatIso), ?_⟩
    · exact ⟨φ.1.kerLift_injective, Ideal.Quotient.lift_surjective_of_surjective _ _
        (h₂.comp (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.surjective)⟩
    · simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
        Quiver.Hom.unop_op, Category.assoc, ← Spec.map_comp]
      change f = X.isoSpec.hom ≫ Spec.map φ
      simp only [Scheme.isoSpec, asIso_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
        ← SpecMap_ΓSpecIso_hom, φ]
      simp only [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  · rintro ⟨I, e, rfl⟩
    infer_instance

end IsClosedImmersion

end Affine

/-- Being a closed immersion is local at the target. -/
instance IsClosedImmersion.isLocalAtTarget : IsLocalAtTarget @IsClosedImmersion :=
  eq_inf ▸ inferInstance

/-- On morphisms with affine target, being a closed immersion is precisely having affine source
and being surjective on global sections. -/
instance IsClosedImmersion.hasAffineProperty : HasAffineProperty @IsClosedImmersion
    (fun X _ f ↦ IsAffine X ∧ Function.Surjective (f.appTop)) := by
  convert HasAffineProperty.of_isLocalAtTarget @IsClosedImmersion
  refine ⟨fun ⟨h₁, h₂⟩ ↦ of_surjective_of_isAffine _ h₂, by apply isAffine_surjective_of_isAffine⟩

/-- Being a closed immersion is stable under base change. -/
instance IsClosedImmersion.isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsClosedImmersion := by
  apply HasAffineProperty.isStableUnderBaseChange
  haveI := HasAffineProperty.isLocal_affineProperty @IsClosedImmersion
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g ⟨ha, hsurj⟩
  exact ⟨inferInstance, RingHom.surjective_isStableUnderBaseChange.pullback_fst_appTop _
    RingHom.surjective_respectsIso f _ hsurj⟩

instance {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion g] :
    IsClosedImmersion (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ ‹_›

instance {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion f] :
    IsClosedImmersion (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ ‹_›

/-- Closed immersions are locally of finite type. -/
instance (priority := 900) {X Y : Scheme.{u}} (f : X ⟶ Y) [h : IsClosedImmersion f] :
    LocallyOfFiniteType f := by
  wlog hY : IsAffine Y
  · rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFiniteType) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H : IsClosedImmersion (f ∣_ U) := IsLocalAtTarget.restrict h U
    exact this _ U.2
  obtain ⟨_, hf⟩ := h.isAffine_surjective_of_isAffine
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
  exact RingHom.FiniteType.of_surjective (Scheme.Hom.app f ⊤).hom hf

/-- A surjective closed immersion is an isomorphism when the target is reduced. -/
lemma isIso_of_isClosedImmersion_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [Surjective f] [IsReduced Y] :
    IsIso f := by
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot, ← Scheme.IdealSheafData.support_eq_top_iff,
    ← SetLike.coe_injective.eq_iff, Scheme.Hom.support_ker]
  simp

lemma isClosed_singleton_iff_isClosedImmersion {X : Scheme} {x : X} :
    IsClosed ({x} : Set X) ↔ IsClosedImmersion (X.fromSpecResidueField x) := by
  rw [← Scheme.range_fromSpecResidueField]
  exact ⟨fun H ↦ .of_isPreimmersion _ H,
    fun _ ↦ (X.fromSpecResidueField x).isClosedEmbedding.isClosed_range⟩

section Section

nonrec theorem isClosedImmersion_of_comp_eq_id {X Y : Scheme.{u}} [Subsingleton Y]
    (f : X ⟶ Y) (g : Y ⟶ X) (hg : g ≫ f = 𝟙 Y) :
    IsClosedImmersion g := by
  wlog hX : ∃ R, X = Spec R
  · rw [IsLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) X.affineCover]
    intro i
    by_cases hxU : Set.range g.base ⊆ (X.affineCover.map i).opensRange
    · rw [Scheme.Cover.pullbackHom,
        ← (IsOpenImmersion.isPullback_lift_id _ _ hxU).flip.isoPullback_inv_snd,
        MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion]
      refine this (X.affineCover.map i ≫ f) _ ?_ ⟨_, rfl⟩
      rw [IsOpenImmersion.lift_fac_assoc, hg]
    · have : IsEmpty ((X.affineCover.pullbackCover g).obj i) := by
        apply Scheme.isEmpty_pullback
        rw [← Set.subset_compl_iff_disjoint_left]
        rintro _ hx ⟨x, rfl⟩
        apply hxU
        rintro _ ⟨y, rfl⟩
        exact Subsingleton.elim x y ▸ hx
      infer_instance
  obtain ⟨R, rfl⟩ := hX
  wlog hY : ∃ S, Y = Spec S
  · have inst := (Scheme.isoSpec Y).inv.homeomorph.injective.subsingleton
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (Scheme.isoSpec Y).inv]
    exact this R (f ≫ (Scheme.isoSpec Y).hom) ((Scheme.isoSpec Y).inv ≫ g)
      (by simp [reassoc_of% hg]) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hY
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp, ← Spec.map_id, Spec.map_injective.eq_iff] at hg
  apply IsClosedImmersion.spec_of_surjective
  apply Function.LeftInverse.surjective (g := φ)
  exact fun x ↦ congr($hg.1 x)

instance {X Y : Scheme.{u}} [Subsingleton X] (f : Retract X Y) : IsClosedImmersion f.i :=
  isClosedImmersion_of_comp_eq_id _ _ f.retract

instance (priority := low) {X Y : Scheme.{u}} [Subsingleton Y] [X.Over Y] (f : Y ⟶ X) [f.IsOver Y] :
    IsClosedImmersion f :=
  isClosedImmersion_of_comp_eq_id (X ↘ Y) f (by simp)

end Section

end AlgebraicGeometry
