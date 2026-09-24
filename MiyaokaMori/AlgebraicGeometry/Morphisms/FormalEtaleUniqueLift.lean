import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.FormallyEtaleMorphism

/-! # Unique lifting along nilpotent thickenings for formally étale morphisms

A formally étale morphism admits unique lifts along closed immersions with nilpotent kernel: with the
constant term fixed at `s`, every truncated coordinate tuple `Spec k[t]/(t^{k+1}) → A^{n+1}` lifts
uniquely along the étale map to `Z` (the local coordinates on the based jet space, §2.2 of the
paper; Stacks Project, Tags 04FD / 04F1).

## Route

Instead of an induction on the nilpotency order through the intermediate thickenings `I^j` (Stacks
04FD at each step), we give a direct proof, because Mathlib already contains the two
ring-level ingredients for arbitrary nilpotent kernels:

* **Uniqueness** is Mathlib's `AlgebraicGeometry.FormallyUnramified.hom_ext` (Stacks 04F1): a formally
  unramified morphism admits at most one lift along a closed immersion with nilpotent kernel ideal sheaf.
  Our class `AlgebraicGeometry.FormallyEtale` (affine-locally formally étale ring maps) implies Mathlib's
  `AlgebraicGeometry.FormallyUnramified` (`FormallyEtale.formallyUnramified`, a theorem, not an instance).
* **Existence** is glued from affine pieces: for every `y : T'` pick affine `U ⊆ W` with `b y ∈ U`,
  affine `V ⊆ g⁻¹U` with `a x ∈ V` (`ι x = y`; `ι` is surjective since its kernel is nilpotent),
  and an affine `O ∋ y` with `O ⊆ b⁻¹U` and `ι⁻¹O ⊆ a⁻¹V` (the latter is open because `ι` is a
  closed embedding). On `O` the lifting problem is the ring problem
  `Γ(Z,V) → Γ(T, ι⁻¹O) = Γ(T',O)/I(O)` with `I(O)^m = 0`, solved by
  `Algebra.FormallySmooth.liftOfSurjective` (`Γ(W,U) → Γ(Z,V)` is formally étale, hence formally
  smooth). The local lifts agree on overlaps by uniqueness (applied to the base change of `ι` to the
  overlap, whose kernel is again nilpotent by `Scheme.ker_ideal_of_isPullback_of_isOpenImmersion`),
  so they glue (`Scheme.Cover.glueMorphisms`).

Stacks 04FD is the special case `m = 2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- Our affine-local `FormallyEtale` implies Mathlib's affine-local `FormallyUnramified`
(ring level: `Algebra.FormallyEtale → Algebra.FormallyUnramified`). Deliberately a theorem, not an
instance, so that it does not change instance search downstream. -/
theorem FormallyEtale.formallyUnramified {Z W : Scheme.{u}} (g : Z ⟶ W) [FormallyEtale g] :
    FormallyUnramified g := by
  refine ⟨fun {U} hU {V} hV e => ?_⟩
  have h := FormallyEtale.formallyEtale_appLE g hU hV e
  unfold RingHom.FormallyEtale at h
  unfold RingHom.FormallyUnramified
  let := (g.appLE U V e).hom.toAlgebra
  exact inferInstance

/-- Uniform per-affine nilpotency `I(U)^m = 0` of the kernel ideal sheaf is nilpotency
`I^m = 0` in the semiring `IdealSheafData`. -/
theorem Scheme.Hom.isNilpotent_ker_of_forall_pow_eq_bot {T T' : Scheme.{u}} (ι : T ⟶ T') (m : ℕ)
    (hnil : ∀ U : T'.affineOpens, ι.ker.ideal U ^ m = ⊥) : IsNilpotent ι.ker :=
  ⟨m, Scheme.IdealSheafData.ext (funext fun U => hnil U)⟩

/-- A closed immersion with nilpotent kernel ideal sheaf is surjective on points. -/
theorem Scheme.Hom.surjective_of_isNilpotent_ker {T T' : Scheme.{u}} (ι : T ⟶ T')
    [IsClosedImmersion ι] (hi : IsNilpotent ι.ker) : Surjective ι := by
  have : IsDominant ι := by
    obtain ⟨n, hn⟩ := hi
    rw [isDominant_iff, denseRange_iff_closure_range, ← ι.support_ker,
      ← ι.ker.support_pow (n + 1) (by simp), pow_succ, hn]
    simp
  exact surjective_of_isDominant_of_isClosed_range ι ι.isClosedEmbedding.isClosed_range

/-- The base change of a closed immersion with nilpotent kernel along an open immersion again has
nilpotent kernel (`Scheme.ker_ideal_of_isPullback_of_isOpenImmersion`). -/
theorem Scheme.Hom.isNilpotent_ker_pullback_snd {T T' P : Scheme.{u}} (ι : T ⟶ T')
    [IsClosedImmersion ι] (hi : IsNilpotent ι.ker) (p : P ⟶ T') [IsOpenImmersion p] :
    IsNilpotent (pullback.snd ι p).ker := by
  obtain ⟨n, hn⟩ := hi
  refine ⟨n, Scheme.IdealSheafData.ext (funext fun W => ?_)⟩
  have h := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion ι (pullback.snd ι p)
    (pullback.fst ι p) p (IsPullback.of_hasPullback ι p).flip W
  have hW : ι.ker.ideal ⟨p ''ᵁ W, W.2.image_of_isOpenImmersion _⟩ ^ n = ⊥ :=
    congr(($hn).ideal ⟨p ''ᵁ W, W.2.image_of_isOpenImmersion _⟩)
  change (pullback.snd ι p).ker.ideal W ^ n = ⊥
  rw [h]
  refine le_bot_iff.mp ((Ideal.le_comap_pow _ n).trans ?_)
  rw [hW, Ideal.comap_bot_of_injective _ (ConcreteCategory.bijective_of_isIso _).1]

/-- `appLE` only depends on the morphism, not on the proof of the inclusion. -/
private theorem Scheme.Hom.appLE_congr_hom {X Y : Scheme.{u}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (U : Y.Opens)
    (V : X.Opens) (e₁ : V ≤ f₁ ⁻¹ᵁ U) (e₂ : V ≤ f₂ ⁻¹ᵁ U) :
    f₁.appLE U V e₁ = f₂.appLE U V e₂ := by
  subst h; rfl

/-- A lift `c : O ⟶ Z` on an open `O ⊆ T'` satisfying `(ι ∣_ O) ≫ c = (ι⁻¹O).ι ≫ a` satisfies the
same identity against every test square, via the pullback property of `ι ∣_ O`. -/
theorem lift_on_open_universal {Z T T' : Scheme.{u}} (ι : T ⟶ T') (a : T ⟶ Z) (O : T'.Opens)
    (c : O.toScheme ⟶ Z) (hc : (ι ∣_ O) ≫ c = (ι ⁻¹ᵁ O).ι ≫ a) {Q : Scheme.{u}} (q : Q ⟶ T)
    (q' : Q ⟶ O.toScheme) (h : q' ≫ O.ι = q ≫ ι) : q' ≫ c = q ≫ a := by
  have H := isPullback_morphismRestrict ι O
  rw [← H.lift_fst q' q h, Category.assoc, hc, ← Category.assoc, H.lift_snd]

/-- Local existence: around every point of `T'` there is an affine open `O` and a lift on `O`. -/
theorem FormallyEtale.exists_affine_lift {Z W : Scheme.{u}} (g : Z ⟶ W) [FormallyEtale g]
    {T T' : Scheme.{u}} (ι : T ⟶ T') [IsClosedImmersion ι] (m : ℕ)
    (hnil : ∀ U : T'.affineOpens, ι.ker.ideal U ^ m = ⊥)
    (a : T ⟶ Z) (b : T' ⟶ W) (hab : a ≫ g = ι ≫ b) (y : T') :
    ∃ O : T'.affineOpens, y ∈ O.1 ∧ ∃ c : O.1.toScheme ⟶ Z,
      (ι ∣_ O.1) ≫ c = (ι ⁻¹ᵁ O.1).ι ≫ a ∧ c ≫ g = O.1.ι ≫ b := by
  have : Surjective ι :=
    ι.surjective_of_isNilpotent_ker (ι.isNilpotent_ker_of_forall_pow_eq_bot m hnil)
  obtain ⟨x, rfl⟩ := ι.surjective y
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (b (ι x))) isOpen_univ
  have hax : g (a x) ∈ U := by
    have h1 : (a ≫ g) x = (ι ≫ b) x := by rw [hab]
    simp only [Scheme.Hom.comp_apply] at h1
    rw [h1]; exact hxU
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ g ⁻¹ᵁ U⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open hax (g ⁻¹ᵁ U).isOpen
  -- the open set of `T'` whose preimage under the homeomorphism `ι` is `a⁻¹V`
  let S : T'.Opens := ⟨(ι.base '' ((a ⁻¹ᵁ V : Set T)ᶜ))ᶜ,
    (ι.isClosedEmbedding.isClosedMap _ (a ⁻¹ᵁ V).isOpen.isClosed_compl).isOpen_compl⟩
  have hxS : ι x ∈ S := fun ⟨x', hx', hx'x⟩ =>
    hx' (by rw [ι.isClosedEmbedding.injective hx'x]; exact hxV)
  obtain ⟨_, ⟨O, hO, rfl⟩, hxO, hOle : O ≤ b ⁻¹ᵁ U ⊓ S⟩ :=
    T'.isBasis_affineOpens.exists_subset_of_mem_open (⟨hxU, hxS⟩ : ι x ∈ b ⁻¹ᵁ U ⊓ S)
      (b ⁻¹ᵁ U ⊓ S).isOpen
  have hOU : O ≤ b ⁻¹ᵁ U := hOle.trans inf_le_left
  have hO'V : ι ⁻¹ᵁ O ≤ a ⁻¹ᵁ V := fun x' hx' => by
    by_contra hcon
    exact (hOle hx').2 ⟨x', hcon, rfl⟩
  have hO' : IsAffineOpen (ι ⁻¹ᵁ O) := hO.preimage ι
  refine ⟨⟨O, hO⟩, hxO, ?_⟩
  -- the ring-level lifting problem
  have hfe := FormallyEtale.formallyEtale_appLE g hU hV hVU
  algebraize [(g.appLE U V hVU).hom, (b.appLE U O hOU).hom, (b.appLE U O hOU ≫ ι.app O).hom]
  have key : g.appLE U V hVU ≫ a.appLE V (ι ⁻¹ᵁ O) hO'V = b.appLE U O hOU ≫ ι.app O := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_congr_hom hab _ _ _ _
  let fA : Γ(Z, V) →ₐ[Γ(W, U)] Γ(T, ι ⁻¹ᵁ O) :=
    { (a.appLE V (ι ⁻¹ᵁ O) hO'V).hom with
      commutes' := fun r => congr(($key).hom r) }
  let gB : Γ(T', O) →ₐ[Γ(W, U)] Γ(T, ι ⁻¹ᵁ O) :=
    { (ι.app O).hom with commutes' := fun r => rfl }
  have hs : Function.Surjective gB := ι.app_surjective O hO
  have hn : IsNilpotent (RingHom.ker (gB : Γ(T', O) →+* Γ(T, ι ⁻¹ᵁ O))) := by
    refine ⟨m, ?_⟩
    have hk : RingHom.ker (gB : Γ(T', O) →+* Γ(T, ι ⁻¹ᵁ O)) = ι.ker.ideal ⟨O, hO⟩ :=
      (ι.ker_apply ⟨O, hO⟩).symm
    rw [hk]; exact hnil ⟨O, hO⟩
  let φ := Algebra.FormallySmooth.liftOfSurjective fA gB hs hn
  have hφ₁ : g.appLE U V hVU ≫ CommRingCat.ofHom φ.toRingHom = b.appLE U O hOU := by
    ext r; exact φ.commutes r
  have hφ₂ : CommRingCat.ofHom φ.toRingHom ≫ ι.app O = a.appLE V (ι ⁻¹ᵁ O) hO'V := by
    ext r; exact Algebra.FormallySmooth.liftOfSurjective_apply fA gB hs hn r
  -- the local lift
  refine ⟨hO.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · have hK : (ι ∣_ O) ≫ hO.isoSpec.hom = hO'.isoSpec.hom ≫ Spec.map (ι.app O) := by
      have : IsOpenImmersion hO.fromSpec := hO.isOpenImmersion_fromSpec
      have : Mono hO.fromSpec := inferInstance
      rw [← cancel_mono hO.fromSpec, Category.assoc, Category.assoc, hO.isoSpec_hom_fromSpec,
        morphismRestrict_ι, ← Scheme.Hom.appLE_eq_app, hO.SpecMap_appLE_fromSpec ι hO' le_rfl,
        ← Category.assoc, hO'.isoSpec_hom_fromSpec]
    rw [← Category.assoc, hK, Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp,
      hφ₂, hV.SpecMap_appLE_fromSpec a hO' hO'V, ← Category.assoc, hO'.isoSpec_hom_fromSpec]
  · rw [Category.assoc, Category.assoc, hU.SpecMap_appLE_fromSpec g hV hVU |>.symm,
      ← Category.assoc (Spec.map _), ← Spec.map_comp, hφ₁, hU.SpecMap_appLE_fromSpec b hO hOU,
      ← Category.assoc, hO.isoSpec_hom_fromSpec]

end AlgebraicGeometry

open AlgebraicGeometry in
theorem formallyEtale_lift_nilpotent {Z W : AlgebraicGeometry.Scheme.{u}} (g : Z ⟶ W)
    [AlgebraicGeometry.FormallyEtale g] {T T' : AlgebraicGeometry.Scheme.{u}}
    (ι : T ⟶ T') [AlgebraicGeometry.IsClosedImmersion ι]
    /- The ideal sheaf of `ι` is uniformly nilpotent on affine opens: `I(U)^m = 0` (stated affine-open
    by affine-open, since `IdealSheafData` has no multiplication). -/
    (m : ℕ) (hnil : ∀ U : T'.affineOpens, ι.ker.ideal U ^ m = ⊥)
    (a : T ⟶ Z) (b : T' ⟶ W) (hab : a ≫ g = ι ≫ b) :
    ∃! c : T' ⟶ Z, ι ≫ c = a ∧ c ≫ g = b := by
  have hnil' : IsNilpotent ι.ker := ι.isNilpotent_ker_of_forall_pow_eq_bot m hnil
  have := FormallyEtale.formallyUnramified g
  choose O hyO c hc₁ hc₂ using FormallyEtale.exists_affine_lift g ι m hnil a b hab
  let 𝒰 : T'.OpenCover :=
    { I₀ := T'
      X i := (O i).1.toScheme
      f i := (O i).1.ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ⟨x, by simpa using hyO x⟩, inferInstance⟩ }
  have hcompat : ∀ i j, pullback.fst ((O i).1.ι) ((O j).1.ι) ≫ c i =
      pullback.snd ((O i).1.ι) ((O j).1.ι) ≫ c j := by
    intro i j
    let p : pullback ((O i).1.ι) ((O j).1.ι) ⟶ T' := pullback.fst ((O i).1.ι) ((O j).1.ι) ≫ (O i).1.ι
    have : IsClosedImmersion (pullback.snd ι p) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) (IsPullback.of_hasPullback ι p) ‹_›
    refine FormallyUnramified.hom_ext (pullback.snd ι p) (ι.isNilpotent_ker_pullback_snd hnil' p)
      g ?_ ?_
    · rw [← Category.assoc, lift_on_open_universal ι a _ (c i) (hc₁ i) (pullback.fst ι p) _
        (by rw [Category.assoc]; exact pullback.condition.symm),
        ← Category.assoc, lift_on_open_universal ι a _ (c j) (hc₁ j) (pullback.fst ι p) _
        (by rw [Category.assoc, ← pullback.condition]; exact pullback.condition.symm)]
    · rw [Category.assoc, hc₂ i, Category.assoc, hc₂ j, ← Category.assoc, ← Category.assoc,
        pullback.condition]
  let cg : T' ⟶ Z := 𝒰.glueMorphisms c hcompat
  have G1 : cg ≫ g = b := 𝒰.hom_ext _ _ fun i => by
    rw [← Category.assoc]
    change (𝒰.f i ≫ 𝒰.glueMorphisms c hcompat) ≫ g = (O i).1.ι ≫ b
    rw [𝒰.ι_glueMorphisms]; exact hc₂ i
  have G2 : ι ≫ cg = a := by
    refine Scheme.hom_ext_of_forall _ _ fun x => ⟨ι ⁻¹ᵁ (O (ι x)).1, hyO (ι x), ?_⟩
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    change (ι ∣_ (O (ι x)).1) ≫ 𝒰.f (ι x) ≫ 𝒰.glueMorphisms c hcompat = _
    rw [𝒰.ι_glueMorphisms]; exact hc₁ (ι x)
  refine ⟨cg, ⟨G2, G1⟩, fun c' hc' => ?_⟩
  exact FormallyUnramified.hom_ext ι hnil' g (hc'.1.trans G2.symm) (hc'.2.trans G1.symm)

end
