import MiyaokaMori.Prelude
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Extending a morphism across a point with valuation-ring local ring

Stacks Project, Tag 0BX7 (Morphisms, lemma-extend-across): if `X` is Noetherian, `x` lies in the closure
of `U` with `O_{X,x}` a valuation ring, and `Y` is proper over `S`, then an `S`-morphism `U → Y` extends
to a larger open containing `x` (cf. Debarre, *Introduction to Mori theory*, 5.17: the local valuative
criterion extends a rational map across a codimension-one point).

Route: Stacks 0BX7 verbatim, all ingredients from Mathlib:
germ-injectivity of locally Noetherian schemes (0BX3, `Scheme.exists_germ_injective`), the
valuative criterion for proper morphisms (0BX5, `IsProper.eq_valuativeCriterion`), spreading out
(0BX6, `spread_out_of_isGermInjective'`), the separated/dominant extension lemma
(`ext_of_isDominant_of_isSeparated`, the 01KM equalizer argument) and gluing along an open cover
(`Scheme.OpenCover.glueMorphisms`, here specialised to two opens in `Scheme.exists_glue_of_sup`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- If `V₀` is an affine open containing `x` on which the germ map `Γ(X, V₀) → 𝒪_{X,x}` is
injective, and `𝒪_{X,x}` is a domain, then the image `η` of the generic point `⊥` of
`Spec 𝒪_{X,x}` in `X` specializes to every point of `V₀`: `Γ(X, V₀)` is a domain (it embeds in
one), so `V₀ = Spec Γ(X, V₀)` is irreducible with generic point `⊥`, and `⊥ ↦ ⊥` under
`Spec 𝒪_{X,x} → Spec Γ(X, V₀)` because the germ map is injective. -/
theorem Scheme.fromSpecStalk_bot_specializes_of_mem
    {X : Scheme.{u}} {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) {x : X} (hxV₀ : x ∈ V₀)
    [IsDomain (X.presheaf.stalk x)]
    (hinj : Function.Injective (X.presheaf.germ V₀ x hxV₀))
    {y : X} (hy : y ∈ V₀) :
    X.fromSpecStalk x (⊥ : PrimeSpectrum (X.presheaf.stalk x)) ⤳ y := by
  have : IsDomain Γ(X, V₀) := hinj.isDomain (X.presheaf.germ V₀ x hxV₀).hom
  obtain ⟨q, rfl⟩ : y ∈ Set.range hV₀.fromSpec := by rwa [hV₀.range_fromSpec]
  have h1 : X.fromSpecStalk x (⊥ : PrimeSpectrum (X.presheaf.stalk x)) =
      hV₀.fromSpec (⊥ : PrimeSpectrum Γ(X, V₀)) := by
    rw [← hV₀.fromSpecStalk_eq_fromSpecStalk hxV₀, IsAffineOpen.fromSpecStalk]
    show hV₀.fromSpec (PrimeSpectrum.comap (X.presheaf.germ V₀ x hxV₀).hom ⊥) =
      hV₀.fromSpec (⊥ : PrimeSpectrum Γ(X, V₀))
    congr 1
    refine PrimeSpectrum.ext ?_
    exact Ideal.comap_bot_of_injective _ hinj
  rw [h1]
  exact ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le).map hV₀.fromSpec.continuous

/-- The two-piece open cover of `U ⊔ V` by `U` (index `true`) and `V` (index `false`). -/
def Scheme.Opens.supCover {X : Scheme.{u}} (U V : X.Opens) : (U ⊔ V).toScheme.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b => (bif b then U else V).toScheme)
    (fun b => X.homOfLE (show (bif b then U else V) ≤ U ⊔ V by
      cases b
      · exact le_sup_right
      · exact le_sup_left))
    (by
      rintro ⟨z, hz⟩
      rcases (Opens.mem_sup.mp hz) with hzU | hzV
      · exact ⟨true, ⟨z, hzU⟩, Scheme.homOfLE_apply' _ _ _⟩
      · exact ⟨false, ⟨z, hzV⟩, Scheme.homOfLE_apply' _ _ _⟩)

/-- Two morphisms out of `U ⊔ V` agreeing on `U` and on `V` are equal. -/
theorem Scheme.hom_ext_of_sup {X Y : Scheme.{u}} (U V : X.Opens)
    (φ ψ : (U ⊔ V).toScheme ⟶ Y)
    (hU : X.homOfLE le_sup_left ≫ φ = X.homOfLE le_sup_left ≫ ψ)
    (hV : X.homOfLE le_sup_right ≫ φ = X.homOfLE le_sup_right ≫ ψ) : φ = ψ := by
  refine (Scheme.Opens.supCover U V).hom_ext φ ψ fun b => ?_
  cases b
  · exact hV
  · exact hU

/-- Gluing two morphisms defined on opens `U`, `V` that agree on `U ⊓ V` to a morphism on
`U ⊔ V` (the two-piece case of `Scheme.OpenCover.glueMorphisms`). -/
theorem Scheme.exists_glue_of_sup {X Y : Scheme.{u}} (U V : X.Opens)
    (f : U.toScheme ⟶ Y) (g : V.toScheme ⟶ Y)
    (h : X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ f = X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ g) :
    ∃ φ : (U ⊔ V).toScheme ⟶ Y,
      X.homOfLE le_sup_left ≫ φ = f ∧ X.homOfLE le_sup_right ≫ φ = g := by
  -- the symmetric compatibility, on `V ⊓ U`
  have h' : X.homOfLE (inf_le_left : V ⊓ U ≤ V) ≫ g =
      X.homOfLE (inf_le_right : V ⊓ U ≤ U) ≫ f := by
    have := congrArg (fun ψ => X.homOfLE (le_of_eq (inf_comm V U)) ≫ ψ) h
    simpa only [Scheme.homOfLE_homOfLE_assoc] using this.symm
  have hO : ∀ b : Bool, (bif b then U else V) ≤ U ⊔ V := by
    intro b; cases b
    · exact le_sup_right
    · exact le_sup_left
  let gl : ∀ b : Bool, (bif b then U else V).toScheme ⟶ Y := fun b =>
    Bool.casesOn (motive := fun b => (bif b then U else V).toScheme ⟶ Y) b g f
  have hcompat : ∀ i j : Bool, pullback.fst (X.homOfLE (hO i)) (X.homOfLE (hO j)) ≫ gl i =
      pullback.snd (X.homOfLE (hO i)) (X.homOfLE (hO j)) ≫ gl j := by
    intro i j
    rw [← cancel_epi (isPullback_opens_inf_le (hO i) (hO j)).isoPullback.hom]
    simp only [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    cases i <;> cases j
    · rfl
    · exact h'
    · exact h
    · rfl
  refine ⟨(Scheme.Opens.supCover U V).glueMorphisms gl hcompat, ?_, ?_⟩
  · exact (Scheme.Opens.supCover U V).ι_glueMorphisms gl hcompat true
  · exact (Scheme.Opens.supCover U V).ι_glueMorphisms gl hcompat false

/-- **Stacks 0BX7** (extending a morphism across a point whose local ring is a valuation ring).
Let `X` be Noetherian over `S`, `Y` proper over `S`, `U ⊆ X` open, `f : U ⟶ Y` an `S`-morphism,
and `x ∈ closure U` with `𝒪_{X,x}` a valuation ring. Then `f` extends to an `S`-morphism on an
open `U' ⊇ U` containing `x`.

Proof. Choose an affine open `V₀ ∋ x` with `Γ(X, V₀) ↪ 𝒪_{X,x}` (`X` is locally Noetherian, hence
germ-injective). `Γ(X, V₀)` is then a domain, so `V₀` is irreducible with generic point
`η := ` image of `⊥` under `Spec 𝒪_{X,x} → X`; since `x ∈ closure U`, `U ∩ V₀ ≠ ∅`, so `η ∈ U`.
Let `K = Frac 𝒪_{X,x}`; the point `Spec K → Spec 𝒪_{X,x} → X` is `η ∈ U`, so composing with `f`
gives a valuative square for `Y → S`, and the valuative criterion (Stacks 0BX5) yields a lift
`t : Spec 𝒪_{X,x} → Y` over `S` with `t|_{Spec K} = f ∘ (Spec K → U)`. Spreading out (Stacks 0BX6,
`Y → S` locally of finite type) gives an open `V ∋ x` and an `S`-morphism `g : V → Y` with
`t = (Spec 𝒪_{X,x} → V) ≫ g`. Shrink `V` to `V₁ := V ⊓ V₀`. On `W := U ⊓ V₁` (reduced, as an open of
`V₀ = Spec` of a domain) `f` and `g` agree after composing with the dominant `Spec K → W`
(`η` is dense in `W ⊆ V₀`), hence agree, `Y → S` being separated. Glue `f` and `g|_{V₁}` along
`U ⊔ V₁`; the glued map is over `S` because both pieces are. -/
theorem exists_extend_across_valuationRing_point
    {S X Y : AlgebraicGeometry.Scheme.{u}} [X.Over S] [Y.Over S]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsProper (Y ↘ S)]
    (U : X.Opens) (f : U.toScheme ⟶ Y) (hf : f ≫ (Y ↘ S) = U.ι ≫ (X ↘ S))
    (x : X) (hx : x ∈ closure (U : Set X)) [IsDomain (X.presheaf.stalk x)]
    (hval : ValuationRing (X.presheaf.stalk x)) :
    ∃ (U' : X.Opens) (hUU' : U ≤ U') (f' : U'.toScheme ⟶ Y),
      x ∈ U' ∧ f' ≫ (Y ↘ S) = U'.ι ≫ (X ↘ S) ∧ X.homOfLE hUU' ≫ f' = f := by
  classical
  -- Step 1: a germ-injective affine neighbourhood `V₀` of `x` (Stacks 0BX3, Mathlib).
  obtain ⟨V₀, hxV₀, hV₀, hinj⟩ := X.exists_germ_injective x
  -- Step 2: the generic point `η` of `V₀`; it lies in `U` and in every open nbhd of `x`.
  set η : X := X.fromSpecStalk x (⊥ : PrimeSpectrum (X.presheaf.stalk x)) with hη_def
  have hη : ∀ y ∈ V₀, η ⤳ y := fun y hy =>
    Scheme.fromSpecStalk_bot_specializes_of_mem hV₀ hxV₀ hinj hy
  have hηU : η ∈ U := by
    obtain ⟨y, hyV₀, hyU⟩ := mem_closure_iff.mp hx V₀ V₀.isOpen hxV₀
    exact (hη y hyV₀).mem_open U.isOpen hyU
  have hηV₀ : η ∈ V₀ := (hη x hxV₀).mem_open V₀.isOpen hxV₀
  -- the fraction field `K` of the valuation ring `𝒪_{X,x}` and the map `Spec K → X`
  let K := FractionRing (X.presheaf.stalk x)
  let φ : Spec (CommRingCat.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K)) ≫ X.fromSpecStalk x
  have hφ : ∀ p, φ p = η := by
    intro p
    have hp : p = (⊥ : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    subst hp
    show X.fromSpecStalk x (PrimeSpectrum.comap (algebraMap (X.presheaf.stalk x) K) ⊥) = η
    rw [hη_def]
    congr 1
    refine PrimeSpectrum.ext ?_
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (X.presheaf.stalk x) K)
  have hφrange : ∀ W : X.Opens, η ∈ W → Set.range φ ⊆ Set.range W.ι := by
    rintro W hηW _ ⟨p, rfl⟩
    rw [hφ p, Scheme.Opens.range_ι]
    exact hηW
  let ιU : Spec (CommRingCat.of K) ⟶ U.toScheme := IsOpenImmersion.lift U.ι φ (hφrange U hηU)
  have hιU : ιU ≫ U.ι = φ := IsOpenImmersion.lift_fac _ _ _
  -- Step 3: the valuative criterion (Stacks 0BX5, Mathlib) gives `t : Spec 𝒪_{X,x} ⟶ Y`.
  have hex : ValuativeCriterion.Existence (Y ↘ S) := by
    have h : IsProper (Y ↘ S) := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let sq : ValuativeCommSq (Y ↘ S) :=
    { R := X.presheaf.stalk x
      domain := inferInstanceAs (IsDomain (X.presheaf.stalk x))
      valuationRing := hval
      K := K
      field := inferInstanceAs (Field K)
      algebra := inferInstanceAs (Algebra (X.presheaf.stalk x) K)
      isFractionRing := inferInstanceAs (IsFractionRing (X.presheaf.stalk x) K)
      i₁ := ιU ≫ f
      i₂ := X.fromSpecStalk x ≫ (X ↘ S)
      commSq := ⟨by rw [Category.assoc, hf, ← Category.assoc, hιU]; rfl⟩ }
  obtain ⟨⟨t, ht₁, ht₂⟩⟩ := (hex sq).exists_lift
  change Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K)) ≫ t = ιU ≫ f at ht₁
  change t ≫ (Y ↘ S) = X.fromSpecStalk x ≫ (X ↘ S) at ht₂
  -- Step 4: spread out `t` to an `S`-morphism `g : V ⟶ Y` on an open `V ∋ x` (Stacks 0BX6).
  obtain ⟨V, hxV, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' (X ↘ S) (Y ↘ S) t ht₂
  -- shrink `V` into `V₀` so that everything happens inside the integral affine `V₀`
  let V₁ : X.Opens := V ⊓ V₀
  have hxV₁ : x ∈ V₁ := ⟨hxV, hxV₀⟩
  let g₁ : V₁.toScheme ⟶ Y := X.homOfLE (inf_le_left : V₁ ≤ V) ≫ g
  have hg₁S : g₁ ≫ (Y ↘ S) = V₁.ι ≫ (X ↘ S) := by
    simp only [g₁, Category.assoc, hg₂, Scheme.homOfLE_ι_assoc]
  -- Step 5: `f` and `g₁` agree on `W := U ⊓ V₁` (reduced, with `η` dense; `Y` separated over `S`).
  let W : X.Opens := U ⊓ V₁
  have hWV₀ : W ≤ V₀ := inf_le_right.trans inf_le_right
  have hηW : η ∈ W := ⟨hηU, (hη x hxV₀).mem_open V.isOpen hxV, hηV₀⟩
  let ιW : Spec (CommRingCat.of K) ⟶ W.toScheme := IsOpenImmersion.lift W.ι φ (hφrange W hηW)
  have hιW : ιW ≫ W.ι = φ := IsOpenImmersion.lift_fac _ _ _
  have : IsReduced V₀.toScheme := by
    have : IsDomain Γ(X, V₀) := hinj.isDomain (X.presheaf.germ V₀ x hxV₀).hom
    exact isReduced_of_isOpenImmersion hV₀.isoSpec.hom
  have : IsReduced W.toScheme := isReduced_of_isOpenImmersion (X.homOfLE hWV₀)
  have : IsDominant ιW := by
    refine ⟨dense_iff_inter_open.mpr fun O hO ⟨w, hw⟩ => ⟨ιW default, ?_, ⟨default, rfl⟩⟩⟩
    have h1 : W.ι (ιW default) = η := by rw [← Scheme.Hom.comp_apply, hιW, hφ]
    have h2 : η ⤳ W.ι w :=
      hη _ (hWV₀ (by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨w, rfl⟩))
    rw [← h1] at h2
    exact (W.ι.isOpenEmbedding.isInducing.specializes_iff.mp h2).mem_open hO hw
  have hfg : X.homOfLE (inf_le_left : W ≤ U) ≫ f = X.homOfLE (inf_le_right : W ≤ V₁) ≫ g₁ := by
    refine ext_of_isDominant_of_isSeparated (Y ↘ S) ?_ ιW ?_
    · simp only [g₁, Category.assoc, hf, hg₂, Scheme.homOfLE_ι_assoc]
    · have e1 : ιW ≫ X.homOfLE (inf_le_left : W ≤ U) = ιU := by
        rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, hιW, hιU]
      have e2 : ιW ≫ X.homOfLE (inf_le_right : W ≤ V₁) ≫ X.homOfLE (inf_le_left : V₁ ≤ V) =
          Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K)) ≫
            V.fromSpecStalkOfMem x hxV := by
        rw [← cancel_mono V.ι]
        simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
        rw [hιW]
      have e1' : ιW ≫ X.homOfLE (inf_le_left : W ≤ U) ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K)) ≫ t := by
        rw [← Category.assoc, e1, ht₁]
      have e2' : ιW ≫ X.homOfLE (inf_le_right : W ≤ V₁) ≫ g₁ =
          Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K)) ≫ t := by
        simp only [g₁]
        rw [reassoc_of% e2, ← hg₁]
      exact e1'.trans e2'.symm
  -- Step 6: glue `f` and `g₁` along `U ⊔ V₁`; the result is an `S`-morphism piece by piece.
  obtain ⟨f', hf'U, hf'V₁⟩ := Scheme.exists_glue_of_sup U V₁ f g₁ hfg
  refine ⟨U ⊔ V₁, le_sup_left, f', Opens.mem_sup.mpr (Or.inr hxV₁), ?_, hf'U⟩
  apply Scheme.hom_ext_of_sup U V₁
  · rw [← Category.assoc, hf'U, hf, Scheme.homOfLE_ι_assoc]
  · rw [← Category.assoc, hf'V₁, hg₁S, Scheme.homOfLE_ι_assoc]

end AlgebraicGeometry

end
