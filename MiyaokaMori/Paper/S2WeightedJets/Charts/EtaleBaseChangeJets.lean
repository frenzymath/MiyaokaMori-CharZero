import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.FormalEtaleUniqueLift
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetConstantTermNilpotent
import MiyaokaMori.Paper.S2WeightedJets.Jets.UnbasedRelativeJetScheme
import MiyaokaMori.Paper.S1Intro.Stacks02hm

/-! # Étale base change for jet schemes

Étale base change of jet schemes (Ein–Mustaţă, *Jet schemes and singularities*, Lemma 2.9): for an
étale morphism `g : Z → W` over `S`, `J_r(Z/S) ≅ Z ×_W J_r(W/S)` (relative jet schemes without a
fixed constant term; the version based at a section is deduced from this one in
`JetLocalCoordinates`). Used in §2.2 of the paper for the chart (2.5).

Route (the one-line proof of Lemma 2.9, relative to `S`):
1. pure category theory: `isPullback_of_existsUnique_lift` reduces `IsPullback` to the existence
   and uniqueness of a lift for every test scheme `T`;
2. compatibility of `jetScheme.map` with `jetScheme.homEquiv` (`jetScheme.homEquiv_map`, from the
   naturality `jetScheme.homEquiv_comp` used twice) and the commutative square `jetScheme.map_proj`
   (from `jetScheme.homEquiv_proj` used twice);
3. the lifting problem `jetScheme_etale_base_change_existsUnique`: translate `b : T → J_r(W/S)` into
   `β : T ×_k D_r → W`, apply `formallyEtale_lift_nilpotent` (`g` étale, hence formally étale,
   `formallyEtale_of_etale`; `ι₀` is a closed immersion with nilpotent ideal,
   `jetConstantTerm_isClosedImmersion_nilpotent`) to obtain a unique `γ : T ×_k D_r → Z`, and
   translate back to a `T`-point via the inverse of `jetScheme.homEquiv`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- `letI`/`haveI` are intentional: the `k`-structure instances are inlined into the terms so that they
-- coincide syntactically with the instance terms in the type of `jetScheme.homEquiv`, and `rw` matches.
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Pure category theory: a commutative square `fst ≫ f = snd ≫ g` is a pullback as soon as for every
    test object `T` and compatible `(a, b)` there is a unique `c` with `c ≫ fst = a` and
    `c ≫ snd = b` (`PullbackCone.IsLimit.mk` + `IsPullback.of_isLimit'`; the lift is extracted
    with `Exists.choose`, since `IsPullback` is a `Prop`). -/

theorem isPullback_of_existsUnique_lift {C : Type u'} [CategoryTheory.Category.{v'} C]
    {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (w : fst ≫ f = snd ≫ g)
    (h : ∀ {T : C} (a : T ⟶ X) (b : T ⟶ Y), a ≫ f = b ≫ g →
      ∃! c : T ⟶ P, c ≫ fst = a ∧ c ≫ snd = b) :
    CategoryTheory.IsPullback fst snd f g :=
  CategoryTheory.IsPullback.of_isLimit' ⟨w⟩
    (CategoryTheory.Limits.PullbackCone.IsLimit.mk w
      (fun s => (h s.fst s.snd s.condition).exists.choose)
      (fun s => (h s.fst s.snd s.condition).exists.choose_spec.1)
      (fun s => (h s.fst s.snd s.condition).exists.choose_spec.2)
      (fun s _m hm₁ hm₂ =>
        (h s.fst s.snd s.condition).unique ⟨hm₁, hm₂⟩
          (h s.fst s.snd s.condition).exists.choose_spec))

section JetSchemeMap

variable {k : Type u} [Field k] {S Z W : AlgebraicGeometry.Scheme.{u}}
  [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
  {pZ : Z ⟶ S} {pW : W ⟶ S} [AlgebraicGeometry.IsAffineHom pZ] [AlgebraicGeometry.IsAffineHom pW]
  (r : ℕ) (g : Z ⟶ W) (hg : g ≫ pW = pZ)

/-- `J_r(g)` lies over the structure morphism of `J_r(Z/S)`: `J_r(g) ≫ π^W ≫ pW = π^Z ≫ pZ`
    (the second component of the subtype in the definition of `jetScheme.map`). -/

theorem jetScheme.map_over :
    jetScheme.map (k := k) r g hg ≫ jetScheme.proj (k := k) r pW ≫ pW =
      jetScheme.proj (k := k) r pZ ≫ pZ := by
  let t := jetScheme.proj (k := k) r pZ ≫ pZ
  let u := jetScheme.homEquiv (k := k) r pZ (jetScheme (k := k) r pZ) t
    ⟨CategoryTheory.CategoryStruct.id _, CategoryTheory.Category.id_comp _⟩
  exact ((jetScheme.homEquiv (k := k) r pW (jetScheme (k := k) r pZ) t).symm
    ⟨u.1 ≫ g, (CategoryTheory.Category.assoc _ _ _).trans ((congrArg (u.1 ≫ ·) hg).trans u.2)⟩).2

/-- Under `jetScheme.homEquiv`, `J_r(g)` corresponds to the universal jet of `Z` composed with `g`
    (the defining equation of `jetScheme.map` + `Equiv.apply_symm_apply`). -/

theorem jetScheme.homEquiv_map_apply :
    (jetScheme.homEquiv (k := k) r pW (jetScheme (k := k) r pZ) (jetScheme.proj (k := k) r pZ ≫ pZ)
        ⟨jetScheme.map (k := k) r g hg, jetScheme.map_over (k := k) r g hg⟩).1 =
      (jetScheme.homEquiv (k := k) r pZ (jetScheme (k := k) r pZ) (jetScheme.proj (k := k) r pZ ≫ pZ)
        ⟨CategoryTheory.CategoryStruct.id _, CategoryTheory.Category.id_comp _⟩).1 ≫ g := by
  let t := jetScheme.proj (k := k) r pZ ≫ pZ
  let u := jetScheme.homEquiv (k := k) r pZ (jetScheme (k := k) r pZ) t
    ⟨CategoryTheory.CategoryStruct.id _, CategoryTheory.Category.id_comp _⟩
  have e : (⟨jetScheme.map (k := k) r g hg, jetScheme.map_over (k := k) r g hg⟩ :
      { a : jetScheme (k := k) r pZ ⟶ jetScheme (k := k) r pW //
        a ≫ jetScheme.proj (k := k) r pW ≫ pW = t }) =
      (jetScheme.homEquiv (k := k) r pW (jetScheme (k := k) r pZ) t).symm
        ⟨u.1 ≫ g, (CategoryTheory.Category.assoc _ _ _).trans ((congrArg (u.1 ≫ ·) hg).trans u.2)⟩ :=
    Subtype.ext rfl
  rw [e, Equiv.apply_symm_apply]

/-- The square commutes: `J_r(g) ≫ π^W = π^Z ≫ g` (`jetScheme.homEquiv_proj` twice +
    `jetScheme.homEquiv_map_apply`). -/

theorem jetScheme.map_proj :
    jetScheme.map (k := k) r g hg ≫ jetScheme.proj (k := k) r pW =
      jetScheme.proj (k := k) r pZ ≫ g := by
  have h1 := jetScheme.homEquiv_proj (k := k) r pW (jetScheme (k := k) r pZ)
    (jetScheme.proj (k := k) r pZ ≫ pZ)
    ⟨jetScheme.map (k := k) r g hg, jetScheme.map_over (k := k) r g hg⟩
  have h2 := jetScheme.homEquiv_proj (k := k) r pZ (jetScheme (k := k) r pZ)
    (jetScheme.proj (k := k) r pZ ≫ pZ)
    ⟨CategoryTheory.CategoryStruct.id _, CategoryTheory.Category.id_comp _⟩
  rw [h1, jetScheme.homEquiv_map_apply, ← CategoryTheory.Category.assoc, ← h2,
    CategoryTheory.Category.id_comp]

/-- `J_r(g)` is compatible with the functor-of-points description: for a `T`-point `a` over `t`, the
    jet corresponding to `a ≫ J_r(g)` is the jet corresponding to `a`, composed with `g`.
    Proof: `jetScheme.homEquiv_comp` (naturality) for `pW` and for `pZ`, with `f := a` viewed as a
    morphism `Over.mk t ⟶ Over.mk (π^Z ≫ pZ)` in `Over S`, then `jetScheme.homEquiv_map_apply`. -/

theorem jetScheme.homEquiv_map (T : AlgebraicGeometry.Scheme.{u}) (t : T ⟶ S)
    (a : T ⟶ jetScheme (k := k) r pZ) (ha : a ≫ jetScheme.proj (k := k) r pZ ≫ pZ = t) :
    letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (jetScheme.homEquiv (k := k) r pW T t
        ⟨a ≫ jetScheme.map (k := k) r g hg, by
          rw [CategoryTheory.Category.assoc, jetScheme.map_over]; exact ha⟩).1 =
      (jetScheme.homEquiv (k := k) r pZ T t ⟨a, ha⟩).1 ≫ g := by
  letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : (jetScheme (k := k) r pZ).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(jetScheme.proj (k := k) r pZ ≫ pZ) ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : a.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk t)
      (V := CategoryTheory.Over.mk (jetScheme.proj (k := k) r pZ ≫ pZ)) a ha) _⟩
  have h1 : (jetScheme.homEquiv (k := k) r pW T t
        ⟨a ≫ jetScheme.map (k := k) r g hg, by
          rw [CategoryTheory.Category.assoc, jetScheme.map_over]; exact ha⟩).1 =
      jetThickeningMap (k := k) r a ≫
        (jetScheme.homEquiv (k := k) r pW (jetScheme (k := k) r pZ) (jetScheme.proj (k := k) r pZ ≫ pZ)
          ⟨jetScheme.map (k := k) r g hg, jetScheme.map_over (k := k) r g hg⟩).1 :=
    jetScheme.homEquiv_comp (k := k) r pW (T := CategoryTheory.Over.mk (jetScheme.proj (k := k) r pZ ≫ pZ))
      (T' := CategoryTheory.Over.mk t)
      (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk t)
        (V := CategoryTheory.Over.mk (jetScheme.proj (k := k) r pZ ≫ pZ)) a ha)
      ⟨jetScheme.map (k := k) r g hg, jetScheme.map_over (k := k) r g hg⟩
  have h2 : (jetScheme.homEquiv (k := k) r pZ T t
        ⟨a ≫ CategoryTheory.CategoryStruct.id _, by
          rw [CategoryTheory.Category.comp_id]; exact ha⟩).1 =
      jetThickeningMap (k := k) r a ≫
        (jetScheme.homEquiv (k := k) r pZ (jetScheme (k := k) r pZ) (jetScheme.proj (k := k) r pZ ≫ pZ)
          ⟨CategoryTheory.CategoryStruct.id _, CategoryTheory.Category.id_comp _⟩).1 :=
    jetScheme.homEquiv_comp (k := k) r pZ (T := CategoryTheory.Over.mk (jetScheme.proj (k := k) r pZ ≫ pZ))
      (T' := CategoryTheory.Over.mk t)
      (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk t)
        (V := CategoryTheory.Over.mk (jetScheme.proj (k := k) r pZ ≫ pZ)) a ha)
      ⟨CategoryTheory.CategoryStruct.id _, CategoryTheory.Category.id_comp _⟩
  have e : (⟨a ≫ CategoryTheory.CategoryStruct.id _, by
        rw [CategoryTheory.Category.comp_id]; exact ha⟩ :
      { a : T ⟶ jetScheme (k := k) r pZ // a ≫ jetScheme.proj (k := k) r pZ ≫ pZ = t }) = ⟨a, ha⟩ :=
    Subtype.ext (CategoryTheory.Category.comp_id a)
  rw [h1, jetScheme.homEquiv_map_apply, ← CategoryTheory.Category.assoc, ← h2, e]

end JetSchemeMap

/-- The lifting problem (the core of Ein–Mustaţă, Lemma 2.9): given `a : T → Z` and
    `b : T → J_r(W/S)` with `b ≫ π^W = a ≫ g`, there is a unique `c : T → J_r(Z/S)` with
    `c ≫ J_r(g) = b` and `c ≫ π^Z = a`.
    Proof: under `jetScheme.homEquiv`, `b` corresponds to `β : T ×_k D_r → W` with constant term
    `ι₀ ≫ β = b ≫ π^W = a ≫ g` (`jetScheme.homEquiv_proj`); `g` is étale, hence formally étale
    (`formallyEtale_of_etale`), and `ι₀` is a closed immersion with nilpotent ideal
    (`jetConstantTerm_isClosedImmersion_nilpotent`), so `formallyEtale_lift_nilpotent` gives a unique
    `γ` with `ι₀ ≫ γ = a` and `γ ≫ g = β`; `γ` is automatically over `S`
    (`γ ≫ pZ = γ ≫ g ≫ pW = β ≫ pW`); put `c := homEquiv⁻¹ γ`. The two conditions follow from
    `jetScheme.homEquiv_map` and `jetScheme.homEquiv_proj`; uniqueness follows from the uniqueness
    of `γ` and the injectivity of `homEquiv`. -/

theorem jetScheme_etale_base_change_existsUnique {k : Type u} [Field k]
    {S Z W : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (pZ : Z ⟶ S) (pW : W ⟶ S) (g : Z ⟶ W) (hg : g ≫ pW = pZ)
    [AlgebraicGeometry.Etale g]
    [AlgebraicGeometry.IsAffineHom pZ] [AlgebraicGeometry.IsAffineHom pW] (r : ℕ)
    (T : AlgebraicGeometry.Scheme.{u}) (t : T ⟶ S) (a : T ⟶ Z) (ha : a ≫ pZ = t)
    (b : T ⟶ jetScheme (k := k) r pW) (hab : b ≫ jetScheme.proj (k := k) r pW = a ≫ g) :
    ∃! c : T ⟶ jetScheme (k := k) r pZ,
      c ≫ jetScheme.map (k := k) r g hg = b ∧ c ≫ jetScheme.proj (k := k) r pZ = a := by
  letI : T.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨t ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : AlgebraicGeometry.FormallyEtale g := AlgebraicGeometry.formallyEtale_of_etale g
  haveI : AlgebraicGeometry.IsClosedImmersion (jetConstantTerm (k := k) r T) :=
    (jetConstantTerm_isClosedImmersion_nilpotent (k := k) r T).1
  have hb : b ≫ jetScheme.proj (k := k) r pW ≫ pW = t := by
    rw [← CategoryTheory.Category.assoc, hab, CategoryTheory.Category.assoc, hg, ha]
  -- `β : T ×_k D_r → W`, with constant term `a ≫ g`
  have hβ0 : a ≫ g = jetConstantTerm (k := k) r T ≫
      (jetScheme.homEquiv (k := k) r pW T t ⟨b, hb⟩).1 := by
    rw [← jetScheme.homEquiv_proj (k := k) r pW T t ⟨b, hb⟩, hab]
  obtain ⟨γ, ⟨hγ0, hγg⟩, hγu⟩ := formallyEtale_lift_nilpotent g (jetConstantTerm (k := k) r T) (r + 1)
    (jetConstantTerm_isClosedImmersion_nilpotent (k := k) r T).2 a
    (jetScheme.homEquiv (k := k) r pW T t ⟨b, hb⟩).1 hβ0
  have hγ : γ ≫ pZ = jetThickeningProj (k := k) r T ≫ t := by
    rw [← hg, ← CategoryTheory.Category.assoc, hγg]
    exact (jetScheme.homEquiv (k := k) r pW T t ⟨b, hb⟩).2
  obtain ⟨c, hc⟩ : ∃ c : T ⟶ jetScheme (k := k) r pZ,
      c = ((jetScheme.homEquiv (k := k) r pZ T t).symm ⟨γ, hγ⟩).1 := ⟨_, rfl⟩
  have hcover : c ≫ jetScheme.proj (k := k) r pZ ≫ pZ = t := by
    rw [hc]; exact ((jetScheme.homEquiv (k := k) r pZ T t).symm ⟨γ, hγ⟩).2
  have hcsub : (⟨c, hcover⟩ : { a : T ⟶ jetScheme (k := k) r pZ //
      a ≫ jetScheme.proj (k := k) r pZ ≫ pZ = t }) =
      (jetScheme.homEquiv (k := k) r pZ T t).symm ⟨γ, hγ⟩ := Subtype.ext hc
  have hcγ : (jetScheme.homEquiv (k := k) r pZ T t ⟨c, hcover⟩).1 = γ := by
    rw [hcsub, Equiv.apply_symm_apply]
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · -- c ≫ J_r(g) = b
    have hover : c ≫ jetScheme.map (k := k) r g hg ≫ jetScheme.proj (k := k) r pW ≫ pW = t := by
      rw [jetScheme.map_over]; exact hcover
    have h3 : jetScheme.homEquiv (k := k) r pW T t ⟨c ≫ jetScheme.map (k := k) r g hg, hover⟩ =
        jetScheme.homEquiv (k := k) r pW T t ⟨b, hb⟩ := by
      apply Subtype.ext
      rw [jetScheme.homEquiv_map (k := k) r g hg T t c hcover, hcγ, hγg]
    exact congrArg Subtype.val ((jetScheme.homEquiv (k := k) r pW T t).injective h3)
  · -- c ≫ π^Z = a
    rw [jetScheme.homEquiv_proj (k := k) r pZ T t ⟨c, hcover⟩, hcγ]
    exact hγ0
  · -- uniqueness
    rintro c' ⟨hc'1, hc'2⟩
    have hc'over : c' ≫ jetScheme.proj (k := k) r pZ ≫ pZ = t := by
      rw [← CategoryTheory.Category.assoc, hc'2, ha]
    have e1 : jetConstantTerm (k := k) r T ≫
        (jetScheme.homEquiv (k := k) r pZ T t ⟨c', hc'over⟩).1 = a := by
      rw [← jetScheme.homEquiv_proj (k := k) r pZ T t ⟨c', hc'over⟩, hc'2]
    have hover' : c' ≫ jetScheme.map (k := k) r g hg ≫ jetScheme.proj (k := k) r pW ≫ pW = t := by
      rw [jetScheme.map_over]; exact hc'over
    have e2 : (jetScheme.homEquiv (k := k) r pZ T t ⟨c', hc'over⟩).1 ≫ g =
        (jetScheme.homEquiv (k := k) r pW T t ⟨b, hb⟩).1 := by
      rw [← jetScheme.homEquiv_map (k := k) r g hg T t c' hc'over]
      have e : (⟨c' ≫ jetScheme.map (k := k) r g hg, hover'⟩ :
          { a : T ⟶ jetScheme (k := k) r pW // a ≫ jetScheme.proj (k := k) r pW ≫ pW = t }) =
          ⟨b, hb⟩ := Subtype.ext hc'1
      rw [e]
    have e3 : (jetScheme.homEquiv (k := k) r pZ T t ⟨c', hc'over⟩).1 = γ := hγu _ ⟨e1, e2⟩
    have e4 : (⟨c', hc'over⟩ : { a : T ⟶ jetScheme (k := k) r pZ //
        a ≫ jetScheme.proj (k := k) r pZ ≫ pZ = t }) =
        (jetScheme.homEquiv (k := k) r pZ T t).symm ⟨γ, hγ⟩ := by
      apply (jetScheme.homEquiv (k := k) r pZ T t).injective
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext e3
    rw [hc]
    exact congrArg Subtype.val e4

/-- **Étale base change for jet schemes** (Ein–Mustaţă, Lemma 2.9): for `g : Z → W` étale over `S`,
the square `J_r(Z/S) → J_r(W/S)`, `J_r(Z/S) → Z`, `J_r(W/S) → W`, `Z → W` is a pullback. -/
theorem jetScheme_etale_base_change {k : Type u} [Field k] {S Z W : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (pZ : Z ⟶ S) (pW : W ⟶ S) (g : Z ⟶ W) (hg : g ≫ pW = pZ)
    [AlgebraicGeometry.Etale g]
    /- `jetScheme` is built from `relativeJetScheme` by the diagonal trick and requires affineness
       over `S`; the only use (`jet_local_coordinates`) takes `pZ := V → U` and
       `pW := 𝔸^{n+1}_U → U`, which are affine. -/
    [AlgebraicGeometry.IsAffineHom pZ] [AlgebraicGeometry.IsAffineHom pW] (r : ℕ) :
    CategoryTheory.IsPullback
      (jetScheme.map (k := k) r g hg) (jetScheme.proj (k := k) r pZ)
      (jetScheme.proj (k := k) r pW) g :=
  isPullback_of_existsUnique_lift (jetScheme.map_proj (k := k) r g hg)
    fun {T} b a hab =>
      jetScheme_etale_base_change_existsUnique (k := k) pZ pW g hg r T (a ≫ pZ) a rfl b hab

end
