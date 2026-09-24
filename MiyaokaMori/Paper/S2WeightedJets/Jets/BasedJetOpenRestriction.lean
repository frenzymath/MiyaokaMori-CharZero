import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetOpenRestriction_ConstantTermSurjective
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetFunctor
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableBy
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme

/-! # Restriction of based jets to open sets

Based jets only see a neighborhood of the section (the relative, based version of Ein–Mustață Lemma 2.3): if
`U ⊆ C` and `V ⊆ Z` are open with `s(U) ⊆ V ⊆ p⁻¹(U)`, then the part of `J_r^s(Z/C)` over `U` is isomorphic to
`J_r^{s|_U}(V/U)` (§2 of the paper, the local coordinates on the based jet space).

Proof (Yoneda):
1. Let `J = J_r^s(Z/C)` and `P := (π⁻¹U → U) ∈ Over U` (`relativeJetScheme.restrictObj`). For `W ∈ Over U`,
   `Hom_U(W, P) ≃ Hom_C(W, J)`: from right to left, lift along the open immersion `π⁻¹U ↪ J` (the image lies over
   `U`, `restrictHomOfBase`); from left to right, compose (`restrictHomToBase`).
2. `Hom_C(W, J) ≃ {based jets of Z/C over W}` (`relativeJetScheme.representableBy`).
3. `{based jets of Z/C over W} ≃ {based jets of V/U over W}`: the image of a jet `φ : W ×_k D_r → Z` lies in `V`,
   because the constant-term section `ι₀ : W → W ×_k D_r` is surjective on underlying spaces
   (`jetConstantTerm_surjective`) and the image of `ι₀ ≫ φ = W → U → C → Z` lies in `s(U) ⊆ V`; so `φ` factors
   uniquely through `V ↪ Z` (`restrictJetOfBase`), and conversely compose with `V ↪ Z` (`restrictJetToBase`).
   Compatibility is checked with `cancel_mono`.
4. The composite of the three steps is natural in `W` (`restrictRepresentableBy.homEquiv_comp`), so `P` represents
   the based jet functor of `V/U`, as does `J_r^{s|_U}(V/U)`; `RepresentableBy.uniqueUpToIso` gives an
   isomorphism in `Over U`, whose `.left` is the isomorphism of schemes, and `Over.w` gives the compatibility with
   the morphisms to `U` (`relativeJetScheme.restrict_open_exists_over`, the strengthened form needed downstream by
   `relativeJetScheme_restrict_open_over`).
Technical point: the two `k`-structures `⟨W.hom ≫ (U.ι ≫ σ)⟩` and `⟨(W.hom ≫ U.ι) ≫ σ⟩` on `W.left` for
`W ∈ Over U` are definitionally equal (associativity of composition of schemes is `rfl`), so the objects of the two
jet functors can be interchanged directly; `relativeJetScheme.opensOver` is a local instance of this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The restricted section is a morphism over the restricted base.  This is
   the Over-compatibility needed before comparing the two jet functors. -/
theorem relativeJetScheme.restrict_section_over {k : Type u} [Field k]
    {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Z : CategoryTheory.Over C) (s : C ⟶ Z.left)
    (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C)
    (U : C.Opens) (V : Z.left.Opens) (hsV : U ≤ s ⁻¹ᵁ V)
    (hVU : V ≤ Z.hom ⁻¹ᵁ U) :
    s.resLE V U hsV ≫ Z.hom.resLE U V hVU =
      CategoryTheory.CategoryStruct.id U.toScheme := by
  apply (CategoryTheory.cancel_mono U.ι).mp
  rw [CategoryTheory.Category.assoc, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι,
    ← CategoryTheory.Category.assoc, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι,
    CategoryTheory.Category.assoc, hs, CategoryTheory.Category.id_comp,
    CategoryTheory.Category.comp_id]

/- The generic preimage lemma can be instantiated on the restricted base.
   Keeping this instance explicit avoids repeatedly reconstructing the
   `Over.mk` and its section-over proof in local-coordinate arguments. -/
theorem relativeJetScheme.restrict_section_preimage_le_top {k : Type u} [Field k]
    {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Z : CategoryTheory.Over C) (s : C ⟶ Z.left)
    (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C)
    (U : C.Opens) (V : Z.left.Opens) (hsV : U ≤ s ⁻¹ᵁ V)
    (hVU : V ≤ Z.hom ⁻¹ᵁ U) :
    (⊤ : U.toScheme.Opens) ≤
      (s.resLE V U hsV) ⁻¹ᵁ
        ((Z.hom.resLE U V hVU) ⁻¹ᵁ (⊤ : U.toScheme.Opens)) := by
  simpa using
    (relativeJetScheme.section_preimage_le
      (CategoryTheory.Over.mk (Z.hom.resLE U V hVU))
      (s.resLE V U hsV)
      (relativeJetScheme.restrict_section_over (k := k) (C := C) Z s hs U V hsV hVU)
      (⊤ : U.toScheme.Opens))

/- The restriction square remains compatible after composing with the open
   immersion `U.ι`; this is often the form needed by `Scheme.Hom.appLE`.
   It is deliberately stated separately from `restrict_section_over`, whose
   codomain is the identity on `U.toScheme`. -/
theorem relativeJetScheme.restrict_section_over_comp_ι {k : Type u} [Field k]
    {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Z : CategoryTheory.Over C) (s : C ⟶ Z.left)
    (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C)
    (U : C.Opens) (V : Z.left.Opens) (hsV : U ≤ s ⁻¹ᵁ V)
    (hVU : V ≤ Z.hom ⁻¹ᵁ U) :
    s.resLE V U hsV ≫ Z.hom.resLE U V hVU ≫ U.ι = U.ι := by
  rw [← CategoryTheory.Category.assoc,
    relativeJetScheme.restrict_section_over (k := k) (C := C) Z s hs U V hsV hVU,
    CategoryTheory.Category.id_comp]

/- Augmentation compatibility for the restricted over-object, at the top
   open of `U`.  This is the concrete ring-level bridge used when comparing
   the global and restricted chart constructions. -/
theorem relativeJetScheme.restrict_augmentation_comp {k : Type u} [Field k]
    {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Z : CategoryTheory.Over C) (s : C ⟶ Z.left)
    (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C)
    (U : C.Opens) (V : Z.left.Opens) (hsV : U ≤ s ⁻¹ᵁ V)
    (hVU : V ≤ Z.hom ⁻¹ᵁ U) :
    let ZU : CategoryTheory.Over U.toScheme :=
      CategoryTheory.Over.mk (Z.hom.resLE U V hVU)
    (ZU.hom.app (⊤ : U.toScheme.Opens)) ≫
        (s.resLE V U hsV).appLE (ZU.hom ⁻¹ᵁ (⊤ : U.toScheme.Opens))
          (⊤ : U.toScheme.Opens)
          (relativeJetScheme.restrict_section_preimage_le_top
            (k := k) (C := C) Z s hs U V hsV hVU) =
      CategoryTheory.CategoryStruct.id Γ(U.toScheme, (⊤ : U.toScheme.Opens)) := by
  let ZU : CategoryTheory.Over U.toScheme :=
    CategoryTheory.Over.mk (Z.hom.resLE U V hVU)
  change ZU.hom.app (⊤ : U.toScheme.Opens) ≫
      (s.resLE V U hsV).appLE (ZU.hom ⁻¹ᵁ (⊤ : U.toScheme.Opens))
        (⊤ : U.toScheme.Opens) _ = _
  exact relativeJetScheme.augmentation_comp ZU (s.resLE V U hsV)
    (relativeJetScheme.restrict_section_over (k := k) (C := C) Z s hs U V hsV hVU)
    (⊤ : U.toScheme.Opens)


section RestrictGeneric

variable (k : Type u) [Field k] {C : AlgebraicGeometry.Scheme.{u}}
  (Z : CategoryTheory.Over C) (s : C ⟶ Z.left) (r : ℕ)
  (U : C.Opens) (V : Z.left.Opens) (hsV : U ≤ s ⁻¹ᵁ V) (hVU : V ≤ Z.hom ⁻¹ᵁ U)

include hsV in
/-- A based jet of `Z/C` on a `k`-scheme `T` mapping to `U` lands in `V`: every point of
`T ×_k D_r` is in the image of the constant-term section (`jetConstantTerm_surjective`),
whose composite with the jet is `T → U → C → Z`, i.e. `s` of a point of `U`, which lies in
`V` by `hsV`. -/
theorem relativeJetScheme.restrictJet_range (T : AlgebraicGeometry.Scheme.{u})
    [T.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (φ : jetThickening (k := k) r T ⟶ Z.left) (t : T ⟶ U.toScheme)
    (h2 : jetConstantTerm (k := k) r T ≫ φ = t ≫ U.ι ≫ s) :
    Set.range φ ⊆ Set.range V.ι := by
  rw [AlgebraicGeometry.Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  obtain ⟨w, rfl⟩ := jetConstantTerm_surjective (k := k) r T x
  have hU : U.ι (t w) ∈ Set.range U.ι := Set.mem_range_self _
  rw [AlgebraicGeometry.Scheme.Opens.range_ι] at hU
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, h2, AlgebraicGeometry.Scheme.Hom.comp_apply,
    AlgebraicGeometry.Scheme.Hom.comp_apply]
  exact hsV hU

theorem relativeJetScheme.restrictJet_lift_over (T : AlgebraicGeometry.Scheme.{u})
    [T.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (φ : jetThickening (k := k) r T ⟶ Z.left) (t : T ⟶ U.toScheme)
    (h1 : φ ≫ Z.hom = jetThickeningProj (k := k) r T ≫ t ≫ U.ι)
    (hr : Set.range φ ⊆ Set.range V.ι) :
    AlgebraicGeometry.IsOpenImmersion.lift V.ι φ hr ≫ Z.hom.resLE U V hVU =
      jetThickeningProj (k := k) r T ≫ t := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    AlgebraicGeometry.IsOpenImmersion.lift_fac, h1, Category.assoc]

theorem relativeJetScheme.restrictJet_lift_constantTerm (T : AlgebraicGeometry.Scheme.{u})
    [T.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (φ : jetThickening (k := k) r T ⟶ Z.left) (t : T ⟶ U.toScheme)
    (h2 : jetConstantTerm (k := k) r T ≫ φ = t ≫ U.ι ≫ s)
    (hr : Set.range φ ⊆ Set.range V.ι) :
    jetConstantTerm (k := k) r T ≫ AlgebraicGeometry.IsOpenImmersion.lift V.ι φ hr =
      t ≫ s.resLE V U hsV := by
  apply (cancel_mono V.ι).mp
  rw [Category.assoc, AlgebraicGeometry.IsOpenImmersion.lift_fac, h2, Category.assoc,
    AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]

theorem relativeJetScheme.restrictJet_comp_ι_over (T : AlgebraicGeometry.Scheme.{u})
    [T.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (ψ : jetThickening (k := k) r T ⟶ V.toScheme) (t : T ⟶ U.toScheme)
    (h1 : ψ ≫ Z.hom.resLE U V hVU = jetThickeningProj (k := k) r T ≫ t) :
    (ψ ≫ V.ι) ≫ Z.hom = jetThickeningProj (k := k) r T ≫ t ≫ U.ι := by
  rw [Category.assoc, ← AlgebraicGeometry.Scheme.Hom.resLE_comp_ι (f := Z.hom) (U := U)
    (V := V) (e := hVU), ← Category.assoc, h1, Category.assoc]

theorem relativeJetScheme.restrictJet_comp_ι_constantTerm (T : AlgebraicGeometry.Scheme.{u})
    [T.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (ψ : jetThickening (k := k) r T ⟶ V.toScheme) (t : T ⟶ U.toScheme)
    (h2 : jetConstantTerm (k := k) r T ≫ ψ = t ≫ s.resLE V U hsV) :
    jetConstantTerm (k := k) r T ≫ ψ ≫ V.ι = t ≫ U.ι ≫ s := by
  rw [← Category.assoc, h2, Category.assoc, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]

end RestrictGeneric

section Restrict

variable (k : Type u) [Field k] {C : AlgebraicGeometry.Scheme.{u}}
  [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
  (Z : CategoryTheory.Over C) (s : C ⟶ Z.left)
  (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
  (U : C.Opens) (V : Z.left.Opens) (hsV : U ≤ s ⁻¹ᵁ V) (hVU : V ≤ Z.hom ⁻¹ᵁ U)

/-- `U` as a `k`-scheme through `C` (the instance fixed in the statement of
`relativeJetScheme_restrict_open`); a local instance in this file only. -/
@[instance_reducible] def relativeJetScheme.opensOver (U : C.Opens) :
    U.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨U.ι ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩

attribute [local instance] relativeJetScheme.opensOver

/-- A `U`-scheme viewed as a `C`-scheme. -/
abbrev relativeJetScheme.restrictToBase (W : Over U.toScheme) : Over C :=
  Over.mk (W.hom ≫ U.ι)

/-- Functoriality of `restrictToBase`. -/
def relativeJetScheme.restrictToBaseMap {W' W : Over U.toScheme} (f : W' ⟶ W) :
    relativeJetScheme.restrictToBase U W' ⟶ relativeJetScheme.restrictToBase U W :=
  Over.homMk f.left (Over.w_assoc f U.ι)

/-- Restricting a based jet of `Z/C` on a `U`-scheme to a based jet of `V/U`. -/
def relativeJetScheme.restrictJetOfBase (W : Over U.toScheme)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (op (relativeJetScheme.restrictToBase U W))) :
    (relativeJetFunctor (k := k) (Over.mk (Z.hom.resLE U V hVU)) (s.resLE V U hsV)
      (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU) r).obj (op W) :=
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (U.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  Subtype.mk (AlgebraicGeometry.IsOpenImmersion.lift V.ι φ.1
      (relativeJetScheme.restrictJet_range k Z s r U V hsV W.left φ.1 W.hom φ.2.2))
    ⟨relativeJetScheme.restrictJet_lift_over k Z r U V hVU W.left φ.1 W.hom φ.2.1 _,
      relativeJetScheme.restrictJet_lift_constantTerm k Z s r U V hsV W.left φ.1 W.hom φ.2.2 _⟩

theorem relativeJetScheme.restrictJetOfBase_val_comp_ι (W : Over U.toScheme)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (op (relativeJetScheme.restrictToBase U W))) :
    (relativeJetScheme.restrictJetOfBase k Z s hs r U V hsV hVU W φ).1 ≫ V.ι = φ.1 := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (U.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  exact AlgebraicGeometry.IsOpenImmersion.lift_fac V.ι φ.1
    (relativeJetScheme.restrictJet_range k Z s r U V hsV W.left φ.1 W.hom φ.2.2)

/-- A based jet of `V/U` composed with `V ↪ Z` is a based jet of `Z/C`. -/
def relativeJetScheme.restrictJetToBase (W : Over U.toScheme)
    (ψ : (relativeJetFunctor (k := k) (Over.mk (Z.hom.resLE U V hVU)) (s.resLE V U hsV)
      (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU) r).obj (op W)) :
    (relativeJetFunctor (k := k) Z s hs r).obj (op (relativeJetScheme.restrictToBase U W)) :=
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (U.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  Subtype.mk (ψ.1 ≫ V.ι)
    ⟨relativeJetScheme.restrictJet_comp_ι_over k Z r U V hVU W.left ψ.1 W.hom ψ.2.1,
      relativeJetScheme.restrictJet_comp_ι_constantTerm k Z s r U V hsV W.left ψ.1 W.hom ψ.2.2⟩

theorem relativeJetScheme.restrictJetToBase_val (W : Over U.toScheme)
    (ψ : (relativeJetFunctor (k := k) (Over.mk (Z.hom.resLE U V hVU)) (s.resLE V U hsV)
      (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU) r).obj (op W)) :
    (relativeJetScheme.restrictJetToBase k Z s hs r U V hsV hVU W ψ).1 = ψ.1 ≫ V.ι := rfl

theorem relativeJetScheme.restrictJetToBase_restrictJetOfBase (W : Over U.toScheme)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (op (relativeJetScheme.restrictToBase U W))) :
    relativeJetScheme.restrictJetToBase k Z s hs r U V hsV hVU W
      (relativeJetScheme.restrictJetOfBase k Z s hs r U V hsV hVU W φ) = φ := by
  apply Subtype.ext
  rw [relativeJetScheme.restrictJetToBase_val]
  exact relativeJetScheme.restrictJetOfBase_val_comp_ι k Z s hs r U V hsV hVU W φ

theorem relativeJetScheme.restrictJetOfBase_restrictJetToBase (W : Over U.toScheme)
    (ψ : (relativeJetFunctor (k := k) (Over.mk (Z.hom.resLE U V hVU)) (s.resLE V U hsV)
      (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU) r).obj (op W)) :
    relativeJetScheme.restrictJetOfBase k Z s hs r U V hsV hVU W
      (relativeJetScheme.restrictJetToBase k Z s hs r U V hsV hVU W ψ) = ψ := by
  apply Subtype.ext
  symm
  apply AlgebraicGeometry.IsOpenImmersion.lift_uniq
  rfl

variable [AlgebraicGeometry.IsAffineHom Z.hom]

/-- The open piece `π⁻¹U → U` of `J_r^s(Z/C) → C`, as a `U`-scheme. -/
abbrev relativeJetScheme.restrictObj : Over U.toScheme :=
  Over.mk ((relativeJetScheme (k := k) Z s hs r).hom ∣_ U)

/-- A `U`-morphism into `π⁻¹U` is a `C`-morphism into `J`. -/
def relativeJetScheme.restrictHomToBase {W : Over U.toScheme}
    (g : W ⟶ relativeJetScheme.restrictObj k Z s hs r U) :
    relativeJetScheme.restrictToBase U W ⟶ relativeJetScheme (k := k) Z s hs r :=
  Over.homMk (g.left ≫ ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U).ι) (by
    have hg : g.left ≫ ((relativeJetScheme (k := k) Z s hs r).hom ∣_ U) = W.hom := Over.w g
    show (g.left ≫ ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U).ι) ≫
      (relativeJetScheme (k := k) Z s hs r).hom = W.hom ≫ U.ι
    rw [Category.assoc, ← AlgebraicGeometry.morphismRestrict_ι, ← Category.assoc, hg])

theorem relativeJetScheme.restrictHomToBase_left {W : Over U.toScheme}
    (g : W ⟶ relativeJetScheme.restrictObj k Z s hs r U) :
    (relativeJetScheme.restrictHomToBase k Z s hs r U g).left =
      g.left ≫ ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U).ι := rfl

theorem relativeJetScheme.restrictHom_range {W : Over U.toScheme}
    (f : relativeJetScheme.restrictToBase U W ⟶ relativeJetScheme (k := k) Z s hs r) :
    Set.range f.left ⊆ Set.range ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U).ι := by
  rw [AlgebraicGeometry.Scheme.Opens.range_ι]
  rintro _ ⟨w, rfl⟩
  have hf : f.left ≫ (relativeJetScheme (k := k) Z s hs r).hom = W.hom ≫ U.ι := Over.w f
  show (relativeJetScheme (k := k) Z s hs r).hom (f.left w) ∈ U
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, hf, AlgebraicGeometry.Scheme.Hom.comp_apply]
  have hU : U.ι (W.hom w) ∈ Set.range U.ι := Set.mem_range_self _
  rwa [AlgebraicGeometry.Scheme.Opens.range_ι] at hU

/-- A `C`-morphism from a `U`-scheme into `J` lands in `π⁻¹U`. -/
def relativeJetScheme.restrictHomOfBase {W : Over U.toScheme}
    (f : relativeJetScheme.restrictToBase U W ⟶ relativeJetScheme (k := k) Z s hs r) :
    W ⟶ relativeJetScheme.restrictObj k Z s hs r U :=
  Over.homMk (AlgebraicGeometry.IsOpenImmersion.lift _ f.left
      (relativeJetScheme.restrictHom_range k Z s hs r U f)) (by
    have hf : f.left ≫ (relativeJetScheme (k := k) Z s hs r).hom = W.hom ≫ U.ι := Over.w f
    apply (cancel_mono U.ι).mp
    show (AlgebraicGeometry.IsOpenImmersion.lift _ f.left
        (relativeJetScheme.restrictHom_range k Z s hs r U f) ≫
        ((relativeJetScheme (k := k) Z s hs r).hom ∣_ U)) ≫ U.ι = W.hom ≫ U.ι
    rw [Category.assoc, AlgebraicGeometry.morphismRestrict_ι, ← Category.assoc,
      AlgebraicGeometry.IsOpenImmersion.lift_fac, hf])

theorem relativeJetScheme.restrictHomOfBase_left {W : Over U.toScheme}
    (f : relativeJetScheme.restrictToBase U W ⟶ relativeJetScheme (k := k) Z s hs r) :
    (relativeJetScheme.restrictHomOfBase k Z s hs r U f).left =
      AlgebraicGeometry.IsOpenImmersion.lift _ f.left
        (relativeJetScheme.restrictHom_range k Z s hs r U f) := rfl

theorem relativeJetScheme.restrictHomToBase_restrictHomOfBase {W : Over U.toScheme}
    (f : relativeJetScheme.restrictToBase U W ⟶ relativeJetScheme (k := k) Z s hs r) :
    relativeJetScheme.restrictHomToBase k Z s hs r U
      (relativeJetScheme.restrictHomOfBase k Z s hs r U f) = f := by
  apply Over.OverMorphism.ext
  rw [relativeJetScheme.restrictHomToBase_left, relativeJetScheme.restrictHomOfBase_left,
    AlgebraicGeometry.IsOpenImmersion.lift_fac]

theorem relativeJetScheme.restrictHomToBase_comp {W' W : Over U.toScheme} (f : W' ⟶ W)
    (g : W ⟶ relativeJetScheme.restrictObj k Z s hs r U) :
    relativeJetScheme.restrictHomToBase k Z s hs r U (f ≫ g) =
      relativeJetScheme.restrictToBaseMap U f ≫
        relativeJetScheme.restrictHomToBase k Z s hs r U g := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, relativeJetScheme.restrictHomToBase_left,
    relativeJetScheme.restrictHomToBase_left, Over.comp_left, Category.assoc]
  rfl

/-- The bijection `Hom_U(W, π⁻¹U) ≃ {based jets of V/U on W}`: a `U`-morphism into `π⁻¹U`
is a `C`-morphism into `J`, i.e. (by `relativeJetScheme.representableBy`) a based jet of
`Z/C` on `W`, which lands in `V` (`restrictJetOfBase`); conversely compose with `V ↪ Z`. -/
def relativeJetScheme.restrictHomEquiv (W : Over U.toScheme) :
    (W ⟶ relativeJetScheme.restrictObj k Z s hs r U) ≃
      (relativeJetFunctor (k := k) (Over.mk (Z.hom.resLE U V hVU)) (s.resLE V U hsV)
        (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU) r).obj (op W) where
  toFun g := relativeJetScheme.restrictJetOfBase k Z s hs r U V hsV hVU W
    ((relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv
      (relativeJetScheme.restrictHomToBase k Z s hs r U g))
  invFun ψ := relativeJetScheme.restrictHomOfBase k Z s hs r U
    ((relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv.symm
      (relativeJetScheme.restrictJetToBase k Z s hs r U V hsV hVU W ψ))
  left_inv g := by
    apply Over.OverMorphism.ext
    rw [relativeJetScheme.restrictHomOfBase_left]
    symm
    apply AlgebraicGeometry.IsOpenImmersion.lift_uniq
    rw [relativeJetScheme.restrictJetToBase_restrictJetOfBase, Equiv.symm_apply_apply,
      relativeJetScheme.restrictHomToBase_left]
  right_inv ψ := by
    apply Subtype.ext
    symm
    apply AlgebraicGeometry.IsOpenImmersion.lift_uniq
    rw [relativeJetScheme.restrictHomToBase_restrictHomOfBase, Equiv.apply_symm_apply,
      relativeJetScheme.restrictJetToBase_val]

theorem relativeJetScheme.restrictHomEquiv_apply (W : Over U.toScheme)
    (g : W ⟶ relativeJetScheme.restrictObj k Z s hs r U) :
    relativeJetScheme.restrictHomEquiv k Z s hs r U V hsV hVU W g =
      relativeJetScheme.restrictJetOfBase k Z s hs r U V hsV hVU W
        ((relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv
          (relativeJetScheme.restrictHomToBase k Z s hs r U g)) := rfl

/-- `π⁻¹U → U` represents the based-jet functor of `V → U` with base point `s|_U`
(the Yoneda step of EM08 Lemma 2.3 in its relative, based form). -/
def relativeJetScheme.restrictRepresentableBy :
    (relativeJetFunctor (k := k) (Over.mk (Z.hom.resLE U V hVU)) (s.resLE V U hsV)
      (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU) r).RepresentableBy
      (relativeJetScheme.restrictObj k Z s hs r U) where
  homEquiv {W} := relativeJetScheme.restrictHomEquiv k Z s hs r U V hsV hVU W
  homEquiv_comp {W' W} f g := by
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (U.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : W'.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W'.hom ≫ (U.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    haveI : f.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨Over.w_assoc f _⟩
    apply Subtype.ext
    symm
    apply AlgebraicGeometry.IsOpenImmersion.lift_uniq
    have hmap : ((relativeJetFunctor (k := k) (Over.mk (Z.hom.resLE U V hVU)) (s.resLE V U hsV)
        (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU) r).map f.op
          (relativeJetScheme.restrictHomEquiv k Z s hs r U V hsV hVU W g)).1 ≫ V.ι =
        jetThickeningMap (k := k) r f.left ≫
          ((relativeJetScheme.restrictHomEquiv k Z s hs r U V hsV hVU W g).1 ≫ V.ι) := rfl
    rw [hmap, relativeJetScheme.restrictHomEquiv_apply,
      relativeJetScheme.restrictJetOfBase_val_comp_ι,
      relativeJetScheme.restrictHomToBase_comp,
      (relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv_comp]
    rfl

variable [AlgebraicGeometry.IsAffineHom (Over.mk (Z.hom.resLE U V hVU)).hom]

/-- The iso `π⁻¹U ≅ J_r^{s|_U}(V/U)` together with its compatibility with the maps to `U`:
both sides represent the based-jet functor of `V/U` (`restrictRepresentableBy` and
`relativeJetScheme.representableBy`), so they are isomorphic over `U` by Yoneda. -/
theorem relativeJetScheme.restrict_open_exists_over :
    ∃ e : ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U).toScheme ≅
        (relativeJetScheme (k := k) (Over.mk (Z.hom.resLE U V hVU)) (s.resLE V U hsV)
          (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU) r).left,
      e.hom ≫ (relativeJetScheme (k := k) (Over.mk (Z.hom.resLE U V hVU)) (s.resLE V U hsV)
          (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU) r).hom =
        (relativeJetScheme (k := k) Z s hs r).hom ∣_ U :=
  let i := (relativeJetScheme.restrictRepresentableBy k Z s hs r U V hsV hVU).uniqueUpToIso
    (relativeJetScheme.representableBy (k := k) (Over.mk (Z.hom.resLE U V hVU)) (s.resLE V U hsV)
      (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU) r)
  ⟨(Over.forget _).mapIso i, Over.w i.hom⟩

end Restrict

theorem relativeJetScheme_restrict_open {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (U : C.Opens) (V : Z.left.Opens) (hsV : U ≤ s ⁻¹ᵁ V) (hVU : V ≤ Z.hom ⁻¹ᵁ U)
    [AlgebraicGeometry.IsAffineHom (Z.hom.resLE U V hVU)] :
    letI : (U : AlgebraicGeometry.Scheme.{u}).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨U.ι ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    haveI : AlgebraicGeometry.IsAffineHom (CategoryTheory.Over.mk (Z.hom.resLE U V hVU)).hom :=
      inferInstanceAs (AlgebraicGeometry.IsAffineHom (Z.hom.resLE U V hVU))
    Nonempty (((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U).toScheme ≅
      (relativeJetScheme (k := k) (CategoryTheory.Over.mk (Z.hom.resLE U V hVU)) (s.resLE V U hsV)
        (relativeJetScheme.restrict_section_over (k := k) (C := C) Z s hs U V hsV hVU) r).left) := by
  haveI : AlgebraicGeometry.IsAffineHom (CategoryTheory.Over.mk (Z.hom.resLE U V hVU)).hom :=
    inferInstanceAs (AlgebraicGeometry.IsAffineHom (Z.hom.resLE U V hVU))
  obtain ⟨e, -⟩ := relativeJetScheme.restrict_open_exists_over k Z s hs r U V hsV hVU
  exact ⟨e⟩

end
