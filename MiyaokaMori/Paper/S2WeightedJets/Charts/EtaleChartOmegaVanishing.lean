import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Charts.EtaleChartConormalBasis
import MiyaokaMori.AlgebraicGeometry.Morphisms.EtaleChartSmoothResLE

/-! # Vanishing of the relative differentials near the section

If the classes of `h_1, …, h_{n+1} ∈ I` form a basis of `I/I²` and
`φ_W := homOfVector (p|_U) h : W → 𝔸^{n+1}_U`, then there is an open `V₀ ≤ Zx ⊓ W` containing
`s(U)` with `Ω_{V₀/𝔸^{n+1}_U} = 0`.

Source: §2.2 of the paper ("they define a map `Z|_U → 𝔸^{n+1}_U` that sends `s(U)` to the zero
section and is étale near it"). The paper only says "étale near it"; here the argument is a purely
affine Nakayama argument (see the docstring of `exists_etaleChart_omega_isZero_of_mem`), which
does not need Stacks 01UX / 0474.

**Main result**: `exists_etaleChart_omega_isZero_of_mem`. Note that the conclusion is
`∀ c ∈ U, s.base c ∈ V₀` together with `V₀ ≤ p ⁻¹ᵁ U`: since `p (s c) = c`, `s c ∈ p ⁻¹ᵁ U` forces
`c ∈ U`, so the stronger conclusion `∀ c, s.base c ∈ V₀` would be false whenever `U ≠ ⊤`.

Helper lemmas proved here:
* `IsAffineOpen.exists_basicOpen_le_of_isClosed_inter_subset` — basic-open shrink, relative form;
* `Scheme.Modules.isZero_of_forall_subsingleton`, `Scheme.Modules.subsingleton_sections_of_basicOpen_mul`
  — a sheaf of modules vanishes iff its sections vanish, and vanishing on the basic opens `D(r f)`
  gives vanishing on every open inside `D(r)`;
* `Ideal.le_span_sup_sq_of_cotangent_basis` — a basis of `I/I²` lifts to `I ≤ (h) + I²`;
* `MiyaokaMori.EtaleChartOmega.D_mem_span_sup_smul`, `exists_sub_one_mem_ker_smul_mem_span` (Nakayama),
  `ker_eq_map_of_isLocalization`, `map_le_span_sup_sq`, `subsingleton_kaehler_of_span` (algebra).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.EtaleChartOmega

open KaehlerDifferential

section Nakayama

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- For an `A`-algebra retraction `σ : B → A` with kernel `I`, and `h : ι → I` whose classes
generate `I/I²` (i.e. `I ≤ (h) + I²`), every `D b` lies in `span (D h) + I • Ω[B/A]`. -/
theorem D_mem_span_sup_smul (σ : B →ₐ[A] A) {ι : Type*} (h : ι → B)
    (hmem : ∀ i, h i ∈ RingHom.ker σ)
    (hI : RingHom.ker σ ≤ Ideal.span (Set.range h) ⊔ RingHom.ker σ ^ 2) (b : B) :
    D A B b ∈ Submodule.span B (Set.range fun i => D A B (h i)) ⊔
      (RingHom.ker σ) • (⊤ : Submodule B Ω[B⁄A]) := by
  set I := RingHom.ker σ with hIdef
  set N := Submodule.span B (Set.range fun i => D A B (h i)) ⊔ I • (⊤ : Submodule B Ω[B⁄A])
    with hN
  have hspanI : Ideal.span (Set.range h) ≤ I := by
    rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact hmem i
  have hIN : ∀ x ∈ I, D A B x ∈ N := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hI hx)
    rw [map_add]
    refine add_mem ?_ ?_
    · refine Submodule.span_induction (p := fun y _ => D A B y ∈ N) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, rfl⟩
        exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      · simp
      · intro y₁ y₂ _ _ h₁ h₂; rw [map_add]; exact add_mem h₁ h₂
      · intro c y hy' hc
        rw [smul_eq_mul, Derivation.leibniz]
        refine add_mem (N.smul_mem c hc) (Submodule.mem_sup_right ?_)
        exact Submodule.smul_mem_smul (hspanI hy') Submodule.mem_top
    · rw [pow_two] at hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        rw [Derivation.leibniz]
        refine Submodule.mem_sup_right (add_mem ?_ ?_)
        · exact Submodule.smul_mem_smul ha Submodule.mem_top
        · exact Submodule.smul_mem_smul hb Submodule.mem_top
      · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  have hb : D A B b = D A B (b - algebraMap A B (σ b)) := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  rw [hb]
  apply hIN
  rw [hIdef, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply,
    sub_self]

/-- **Nakayama step.** `σ : B → A` an `A`-algebra retraction with kernel `I`; `h : ι → I` with
`I ≤ (h) + I²`; `Ω[B/A]` finitely generated. Then there is `r ≡ 1 (mod I)` with
`r • Ω[B/A] ⊆ span (D h)`. -/
theorem exists_sub_one_mem_ker_smul_mem_span (σ : B →ₐ[A] A) {ι : Type*} (h : ι → B)
    (hmem : ∀ i, h i ∈ RingHom.ker σ)
    (hI : RingHom.ker σ ≤ Ideal.span (Set.range h) ⊔ RingHom.ker σ ^ 2)
    [Module.Finite B Ω[B⁄A]] :
    ∃ r : B, r - 1 ∈ RingHom.ker σ ∧
      ∀ ω : Ω[B⁄A], r • ω ∈ Submodule.span B (Set.range fun i => D A B (h i)) := by
  set S := Submodule.span B (Set.range fun i => D A B (h i)) with hS
  set I := RingHom.ker σ with hIdef
  have hle : (⊤ : Submodule B (Ω[B⁄A] ⧸ S)) ≤ I • ⊤ := by
    rintro q -
    obtain ⟨ω, rfl⟩ := S.mkQ_surjective q
    have hω : ω ∈ S ⊔ I • (⊤ : Submodule B Ω[B⁄A]) := by
      have hω' : ω ∈ Submodule.span B (Set.range (D A B)) := by
        rw [span_range_derivation]; trivial
      refine Submodule.span_induction (p := fun ω _ => ω ∈ S ⊔ I • (⊤ : Submodule B Ω[B⁄A]))
        ?_ ?_ ?_ ?_ hω'
      · rintro _ ⟨b, rfl⟩; exact D_mem_span_sup_smul σ h hmem hI b
      · exact zero_mem _
      · intro x y _ _ hx hy; exact add_mem hx hy
      · intro c x _ hx; exact Submodule.smul_mem _ c hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hω
    rw [map_add, Submodule.mkQ_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).mpr hs,
      zero_add]
    have h1 := Submodule.mem_map_of_mem (f := S.mkQ) ht
    rw [Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl le_top h1
  obtain ⟨r, hr, hr'⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤ Module.Finite.fg_top hle
  refine ⟨r, hr, fun ω => ?_⟩
  have h2 := hr' (S.mkQ ω) trivial
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

end Nakayama

section Localization

/-- The kernel of a ring map out of a localization is the extension of the kernel of its
restriction. -/
theorem ker_eq_map_of_isLocalization {B B' A : Type*} [CommRing B] [CommRing B'] [CommRing A]
    [Algebra B B'] (M : Submonoid B) [IsLocalization M B'] (σ : B →+* A) (σ' : B' →+* A)
    (hcomp : σ'.comp (algebraMap B B') = σ) :
    RingHom.ker σ' = (RingHom.ker σ).map (algebraMap B B') := by
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨b, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    dsimp only at hx ⊢
    have h1 : σ b = 0 := by
      have : algebraMap B B' b = IsLocalization.mk' B' b m * algebraMap B B' m :=
        (IsLocalization.mk'_spec B' b m).symm
      rw [← hcomp, RingHom.comp_apply, this, map_mul, RingHom.mem_ker.mp hx, zero_mul]
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr h1))
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hcomp]
    exact hb

/-- Transfer of "`I ≤ (h) + I²`" along a ring map. -/
theorem map_le_span_sup_sq {B B' : Type*} [CommRing B] [CommRing B'] (f : B →+* B')
    (I : Ideal B) {ι : Type*} (h : ι → B)
    (hI : I ≤ Ideal.span (Set.range h) ⊔ I ^ 2) :
    I.map f ≤ Ideal.span (Set.range fun i => f (h i)) ⊔ (I.map f) ^ 2 := by
  have := Ideal.map_mono (f := f) hI
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at this
  exact this

/-- **Unramifiedness after localization.** `B''` is an `A`-algebra through `B` (with
`Ω[B''/B] = 0`, e.g. a localization) and through `P`; `h : ι → B`, `x : ι → P` have the same
image in `B''`; `r ∈ B` becomes a unit in `B''` and `r • Ω[B/A] ⊆ span (D h)`. Then
`Ω[B''/P] = 0`. -/
theorem subsingleton_kaehler_of_span {A B B'' P : Type*} [CommRing A] [CommRing B] [CommRing B'']
    [CommRing P] [Algebra A B] [Algebra A B''] [Algebra B B''] [IsScalarTower A B B'']
    [Algebra A P] [Algebra P B''] [IsScalarTower A P B'']
    [Subsingleton Ω[B''⁄B]]
    {ι : Type*} (h : ι → B) (x : ι → P)
    (hx : ∀ i, algebraMap P B'' (x i) = algebraMap B B'' (h i))
    (r : B) (hr : IsUnit (algebraMap B B'' r))
    (hspan : ∀ ω : Ω[B⁄A], r • ω ∈ Submodule.span B (Set.range fun i => D A B (h i))) :
    Subsingleton Ω[B''⁄P] := by
  set T := Submodule.span B'' (Set.range fun i => D A B'' (algebraMap B B'' (h i))) with hT
  -- Step 1: `Ω[B''/A]` is spanned by the `D (h i)`.
  have hmapT : ∀ ω₀ : Ω[B⁄A], map A A B B'' ω₀ ∈ T := by
    intro ω₀
    have h1 : map A A B B'' (r • ω₀) ∈ T := by
      have h2 := Submodule.mem_map_of_mem (f := map A A B B'') (hspan ω₀)
      rw [← Submodule.span_image] at h2
      refine Submodule.span_le_restrictScalars B B'' _ (Submodule.span_mono ?_ h2)
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by rw [map_D]⟩
    rw [map_smul, ← algebraMap_smul B''] at h1
    have h3 := T.smul_mem (↑hr.unit⁻¹ : B'') h1
    rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at h3
  have hgen : ∀ ω : Ω[B''⁄A], ω ∈ T := by
    intro ω
    have hk : ω ∈ LinearMap.ker (map A B B'' B'') := by
      rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
    rw [← range_mapBaseChange] at hk
    obtain ⟨t, rfl⟩ := hk
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b'' ω₀ =>
      rw [mapBaseChange_tmul]
      exact T.smul_mem _ (hmapT ω₀)
    | add s t hs ht => rw [map_add]; exact add_mem hs ht
  -- Step 2: `Ω[B''/P]` is the image of `Ω[B''/A]`, and the generators map to `0`.
  have hzero : ∀ ω : Ω[B''⁄A], map A P B'' B'' ω = 0 := by
    intro ω
    refine Submodule.span_induction (p := fun ω _ => map A P B'' B'' ω = 0) ?_ ?_ ?_ ?_ (hgen ω)
    · rintro _ ⟨i, rfl⟩
      rw [map_D, ← hx, Algebra.algebraMap_self_apply, Derivation.map_algebraMap]
    · simp
    · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
    · intro c a _ ha; rw [map_smul, ha, smul_zero]
  refine (subsingleton_iff_forall_eq 0).mpr fun y => ?_
  obtain ⟨ω, rfl⟩ := map_surjective A P B'' y
  exact hzero ω

end Localization


section Geometry

open AlgebraicGeometry

/-- **Basic-open shrink (relative form).** `W` affine open of `X`, `V ≤ W` open, `T ⊆ X` closed with
`T ∩ W ⊆ V`. Then there is `b : Γ(X, W)` with `T ∩ W ⊆ D(b) ⊆ V`. (Same proof as
`IsAffineOpen.exists_isAffineOpen_le_of_isClosed_subset`, but returning the basic open and only
requiring `T ∩ W ⊆ V`.) -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le_of_isClosed_inter_subset
    {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W) {V : X.Opens}
    {T : Set X} (hT : IsClosed T) (hTV : ∀ x ∈ T, x ∈ W → x ∈ V) :
    ∃ b : Γ(X, W), X.basicOpen b ≤ V ∧ ∀ x ∈ T, x ∈ W → x ∈ X.basicOpen b := by
  set f := hW.fromSpec with hf
  have hT' : IsClosed (f.base ⁻¹' T) := hT.preimage f.continuous
  have hK' : IsClosed (f.base ⁻¹' (V : Set X)ᶜ) := V.isOpen.isClosed_compl.preimage f.continuous
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hT'
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hK'
  have hdisj : PrimeSpectrum.zeroLocus (I : Set Γ(X, W)) ∩
      PrimeSpectrum.zeroLocus (J : Set Γ(X, W)) = ∅ := by
    rw [← hI, ← hJ]
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    have hyW : f.base y ∈ (W : Set X) := by
      rw [← hW.range_fromSpec]; exact ⟨y, rfl⟩
    exact hy.2 (hTV _ hy.1 hyW)
  have htop : I ⊔ J = ⊤ := by
    rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_sup]
    exact hdisj
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp htop)
  refine ⟨b, ?_, ?_⟩
  · rw [← hW.fromSpec_image_basicOpen]
    rintro _ ⟨y, hy, rfl⟩
    by_contra hyV
    have : y ∈ PrimeSpectrum.zeroLocus (J : Set Γ(X, W)) := by
      rw [← hJ]; exact hyV
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hy (this hb)
  · intro x hx hxW
    have hxW' : x ∈ (W : Set X) := hxW
    rw [← hW.range_fromSpec] at hxW'
    obtain ⟨y, rfl⟩ := hxW'
    rw [← hW.fromSpec_image_basicOpen]
    refine ⟨y, ?_, rfl⟩
    change b ∉ y.asIdeal
    intro hby
    have hyI : y ∈ PrimeSpectrum.zeroLocus (I : Set Γ(X, W)) := by
      rw [← hI]; exact hx
    have h1 : (1 : Γ(X, W)) ∈ y.asIdeal := by
      rw [← hab]; exact y.asIdeal.add_mem (hyI ha) hby
    exact y.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- A sheaf of modules all of whose section modules are trivial is a zero object. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isZero_of_forall_subsingleton {X : Scheme.{u}}
    (M : X.Modules) (h : ∀ U : X.Opens, Subsingleton Γ(M, U)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  have := h U
  exact Subsingleton.elim _ _

/-- Sections of a sheaf of modules over any open inside `D(r)` (with `r` a section over an affine
open `U`) vanish as soon as they vanish over all `D(r * f)`, `f : Γ(X, U)`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.subsingleton_sections_of_basicOpen_mul
    {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    (h : ∀ f : Γ(X, U), Subsingleton Γ(M, X.basicOpen (r * f)))
    (V : X.Opens) (hV : V ≤ X.basicOpen r) : Subsingleton Γ(M, V) := by
  refine ⟨fun s t => ?_⟩
  have key : ∀ x : V, ∃ f : Γ(X, U),
      X.basicOpen (r * f) ≤ V ∧ (x : X) ∈ X.basicOpen (r * f) := by
    intro x
    have hxU : (x : X) ∈ U := X.basicOpen_le r (hV x.2)
    obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le x hxU
    refine ⟨f, ?_, ?_⟩
    · rw [X.basicOpen_mul]; exact inf_le_right.trans hfV
    · rw [X.basicOpen_mul]; exact ⟨hV x.2, hxf⟩
  choose f hfV hxf using key
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun x : V => X.basicOpen (r * f x)) V (fun x => homOfLE (hfV x))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxf ⟨x, hx⟩⟩) s t (fun x => ?_)
  have := h (f x)
  exact Subsingleton.elim _ _

/-- If the classes of `h i ∈ I` form a `B ⧸ I`-basis of `I/I²`, then `I ≤ (h) + I²`. -/
theorem _root_.Ideal.le_span_sup_sq_of_cotangent_basis {B : Type*} [CommRing B] (I : Ideal B)
    {ι : Type*} (h : ι → B) (hmem : ∀ i, h i ∈ I)
    (b : Module.Basis ι (B ⧸ I) I.Cotangent) (hb : ∀ i, b i = I.toCotangent ⟨h i, hmem i⟩) :
    I ≤ Ideal.span (Set.range h) ⊔ I ^ 2 := by
  intro x hx
  set h' : ι → I := fun i => ⟨h i, hmem i⟩ with hh'
  -- the `B`-span of the `b i` is everything
  have hspanB : ∀ m : I.Cotangent, m ∈ Submodule.span B (Set.range b) := by
    intro m
    have hm : m ∈ Submodule.span (B ⧸ I) (Set.range b) := by rw [b.span_eq]; trivial
    refine Submodule.span_induction (p := fun m _ => m ∈ Submodule.span B (Set.range b))
      ?_ ?_ ?_ ?_ hm
    · intro y hy; exact Submodule.subset_span hy
    · exact zero_mem _
    · intro y z _ _ hy hz; exact add_mem hy hz
    · intro c y _ hy
      obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
      exact Submodule.smul_mem _ l hy
  have hrange : Set.range b = I.toCotangent '' Set.range h' := by
    rw [← Set.range_comp]; congr 1; funext i; exact hb i
  have h1 : I.toCotangent ⟨x, hx⟩ ∈ Submodule.map I.toCotangent (Submodule.span B (Set.range h')) := by
    rw [← Submodule.span_image, ← hrange]; exact hspanB _
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp h1
  have h2 : ((⟨x, hx⟩ : I) - y : B) ∈ I ^ 2 := I.toCotangent_eq.mp hyx.symm
  have h3 : (y : B) ∈ Ideal.span (Set.range h) := by
    have := Submodule.mem_map_of_mem (f := I.subtype) hy
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this
  have hx' : x = (y : B) + ((⟨x, hx⟩ : I) - y : B) := by simp
  rw [hx']
  exact Submodule.add_mem_sup h3 h2

end Geometry

section Main

open AlgebraicGeometry

/-- **`Ω` of the chart map vanishes near the section.**

Setting as in `exists_etaleChart_conormal_basis`: `W := p ⁻¹ᵁ U`, `B := Γ(W, ⊤)`,
`σ : B ⟶ Γ(U, ⊤)` the ring map of `s|_U : U ⟶ W`, `I := ker σ`; `h : Fin (n+1) → B` with `h i ∈ I`
whose classes `h i mod I²` form a `B ⧸ I`-basis `b` of `I.Cotangent`. Let
`φ_W := AffineSpace.homOfVector (p ∣_ U) h : W ⟶ 𝔸^{n+1}_U` (the `U`-morphism `x_i ↦ h i`).
Conclusion: there is an open `V₀ ≤ W`, `V₀ ≤ Zx`, containing `s(U)` (i.e. `∀ c ∈ U, s c ∈ V₀`), such
that `Ω_{V₀ / 𝔸^{n+1}_U} := Omega (Z.homOfLE hV₀ ≫ φ_W)` is the zero module.

Source: §2.2 of the paper ("étale near `s(U)`"). The proof is the standard
affine Nakayama argument, written out here in full (no reference needed):

1. *Shrink.* `X := W.toScheme` is affine, `T := s|_U(U) ⊆ X` is closed and contained in the open
   `V := ι_W⁻¹ Zx`. Writing `T = V(I₀)`, `X ∖ V = V(J₀)` in `Spec Γ(X, ⊤)`, disjointness gives
   `I₀ + J₀ = ⊤`, so `1 = a + j` with `a ∈ I₀`, `j ∈ J₀`; then `T ⊆ D(j) ⊆ V`
   (`IsAffineOpen.exists_basicOpen_le_of_isClosed_inter_subset`).
2. *Rings.* `A := Γ(U, ⊤)`, `B₁ := Γ(X, D(j))`, a localization of `B` at `j`
   (`IsAffineOpen.isLocalization_basicOpen`). `σ₁ := (s|_U).appLE D(j) ⊤ : B₁ → A` is an `A`-algebra
   retraction of `π₁ := (p ∣_ U).appLE ⊤ D(j)` because `s|_U ≫ p ∣_ U = 𝟙`. Its kernel is
   `I₁ = I·B₁` (`ker_eq_map_of_isLocalization`), and `I ≤ (h) + I²` (from the basis `b`,
   `Ideal.le_span_sup_sq_of_cotangent_basis`) gives `I₁ ≤ (h) + I₁²`.
3. *Finiteness.* `p.resLE U (ι_W(D(j)))` is smooth of relative dimension `n+1`
   (`smoothOfRelativeDimension_resLE_of_le`), hence locally of finite type, so `A → B₁` is of finite
   type (`HasRingHomProperty.appLE`) and `Ω[B₁/A]` is a finitely generated `B₁`-module.
4. *Nakayama.* For `b ∈ B₁`, `d b = d(b - σ₁ b)` and `b - σ₁ b ∈ I₁ ≤ (h) + I₁²`, so by Leibniz
   `d b ∈ span(d h_i) + I₁·Ω[B₁/A]`. Thus `N := Ω[B₁/A]/span(d h_i)` satisfies `N = I₁ N`, and
   Nakayama (`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`) yields
   `r ∈ B₁`, `r ≡ 1 (mod I₁)`, with `r·Ω[B₁/A] ⊆ span(d h_i)` (`exists_sub_one_mem_ker_smul_mem_span`).
5. *The open.* `V₀ := ι_W(D(r))`. Since `σ₁ r = 1`, `(s|_U)⁻¹ D(r) = D(σ₁ r) = ⊤`, so `s(U) ⊆ V₀`;
   `V₀ ≤ W` and `V₀ ≤ Zx` are clear.
6. *Vanishing.* `Omega (homOfLE ≫ φ_W) ≅ (Omega φ_W)|_{V₀}` (`Omega.restrictIso`, Stacks 01US), so it
   suffices that all sections of `Omega φ_W` over opens inside `D(r)` vanish; by sheaf separatedness
   it suffices to treat the basic opens `D(r f)`, `f ∈ B₁`. There
   `Γ(Omega φ_W, D(rf)) ≅ Ω[B''/P]` with `B'' := Γ(X, D(rf))`, `P := Γ(𝔸^{n+1}_U, ⊤)`
   (`Omega_appIso`, Stacks 01UT). Now `B''` is a localization of `B₁`, so `Ω[B''/B₁] = 0` and the exact
   sequence `B'' ⊗ Ω[B₁/A] → Ω[B''/A] → Ω[B''/B₁] → 0` shows `Ω[B''/A]` is spanned by the
   `d(h_i)` (as `r` is a unit in `B''`). Finally `Ω[B''/A] → Ω[B''/P]` is surjective and kills
   `d(h_i) = d(x_i) = 0` (`homOfVector_appTop_coord`), so `Ω[B''/P] = 0`
   (`subsingleton_kaehler_of_span`). No generation statement for `P` and no 01UX/0474 are needed.

Edge cases: `U = ⊥` (all rings zero, `V₀ = ⊥`); `n` arbitrary. -/
theorem _root_.exists_etaleChart_omega_isZero_of_mem {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    {Z : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ C.toScheme) (s : C.toScheme ⟶ Z)
    (hs : s ≫ p = CategoryTheory.CategoryStruct.id C.toScheme)
    [AlgebraicGeometry.IsClosedImmersion s] [AlgebraicGeometry.IsAffineHom p]
    (Zx : Z.Opens) (hsZx : ∀ c, s.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ p)]
    (U : C.toScheme.affineOpens)
    (h : ULift.{u} (Fin (n + 1)) → Γ((p ⁻¹ᵁ U.1).toScheme, ⊤))
    (hmem : ∀ i, h i ∈ RingHom.ker
      (s.resLE (p ⁻¹ᵁ U.1) U.1 (etaleChart_le_preimage p s hs U.1)).appTop.hom)
    (b : Module.Basis (ULift.{u} (Fin (n + 1)))
      (Γ((p ⁻¹ᵁ U.1).toScheme, ⊤) ⧸ RingHom.ker
        (s.resLE (p ⁻¹ᵁ U.1) U.1 (etaleChart_le_preimage p s hs U.1)).appTop.hom)
      (RingHom.ker
        (s.resLE (p ⁻¹ᵁ U.1) U.1 (etaleChart_le_preimage p s hs U.1)).appTop.hom).Cotangent)
    (hb : ∀ i, b i = Ideal.toCotangent _ ⟨h i, hmem i⟩) :
    ∃ (V₀ : Z.Opens) (hV₀ : V₀ ≤ p ⁻¹ᵁ U.1), V₀ ≤ Zx ∧ (∀ c ∈ U.1, s.base c ∈ V₀) ∧
      CategoryTheory.Limits.IsZero (AlgebraicGeometry.Omega
        (Z.homOfLE hV₀ ≫ AlgebraicGeometry.AffineSpace.homOfVector (p ∣_ U.1) h)) := by
  classical
  -- Step 0: the hypothesis on the basis, before any abbreviation.
  have hI : RingHom.ker (s.resLE (p ⁻¹ᵁ U.1) U.1 (etaleChart_le_preimage p s hs U.1)).appTop.hom ≤
      Ideal.span (Set.range h) ⊔
        RingHom.ker (s.resLE (p ⁻¹ᵁ U.1) U.1 (etaleChart_le_preimage p s hs U.1)).appTop.hom ^ 2 :=
    Ideal.le_span_sup_sq_of_cotangent_basis _ h hmem b hb
  clear b hb
  have hW : IsAffineOpen (p ⁻¹ᵁ U.1) := U.2.preimage p
  haveI : IsAffine (p ⁻¹ᵁ U.1).toScheme := hW
  haveI : IsAffine U.1.toScheme := U.2
  set sW := s.resLE (p ⁻¹ᵁ U.1) U.1 (etaleChart_le_preimage p s hs U.1) with hsWdef
  set φ := AffineSpace.homOfVector (p ∣_ U.1) h with hφdef
  have e1 : sW ≫ p ∣_ U.1 = 𝟙 U.1.toScheme := by
    rw [← cancel_mono U.1.ι, Category.assoc, morphismRestrict_ι,
      Scheme.Hom.resLE_comp_ι_assoc, hs, Category.comp_id, Category.id_comp]
  have hιsW : ∀ c' : U.1.toScheme, (p ⁻¹ᵁ U.1).ι (sW c') = s (U.1.ι c') := by
    intro c'
    have := congrArg (fun g => g c')
      (Scheme.Hom.resLE_comp_ι s (etaleChart_le_preimage p s hs U.1))
    simpa only [Scheme.Hom.comp_apply] using this
  -- Step 1: shrink to a basic open `D(j) ⊆ Zx ∩ W` containing `s(U)`.
  have hT : IsClosed (Set.range sW.base) := by
    have hrange : Set.range sW.base = (p ⁻¹ᵁ U.1).ι.base ⁻¹' Set.range s.base := by
      ext y; constructor
      · rintro ⟨c', rfl⟩; exact ⟨U.1.ι c', (hιsW c').symm⟩
      · rintro ⟨c, hc⟩
        have hcU : c ∈ U.1 := by
          have hy : p ((p ⁻¹ᵁ U.1).ι y) ∈ U.1 := y.2
          rw [← hc, ← Scheme.Hom.comp_apply, hs] at hy
          exact hy
        refine ⟨⟨c, hcU⟩, (p ⁻¹ᵁ U.1).ι.isOpenEmbedding.injective ?_⟩
        exact (hιsW _).trans hc
    rw [hrange]
    exact (IsClosedImmersion.isClosedEmbedding s).isClosed_range.preimage
      (p ⁻¹ᵁ U.1).ι.continuous
  have hTV : ∀ x ∈ Set.range sW.base, x ∈ (⊤ : (p ⁻¹ᵁ U.1).toScheme.Opens) →
      x ∈ (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ Zx := by
    rintro _ ⟨c', rfl⟩ -
    rw [Scheme.Hom.mem_preimage, hιsW]; exact hsZx _
  obtain ⟨j, hjZx, hTj⟩ :=
    (isAffineOpen_top (p ⁻¹ᵁ U.1).toScheme).exists_basicOpen_le_of_isClosed_inter_subset hT hTV
  set Dj := (p ⁻¹ᵁ U.1).toScheme.basicOpen j with hDjdef
  have hDj : IsAffineOpen Dj := (isAffineOpen_top _).basicOpen j
  -- Step 2: the rings `A → B₁ → A` (retraction) and `B → B₁` (localization).
  have e₁ : (⊤ : U.1.toScheme.Opens) ≤ sW ⁻¹ᵁ Dj := fun c' _ => hTj _ ⟨c', rfl⟩ trivial
  set σ₁ := sW.appLE Dj ⊤ e₁ with hσ₁def
  set π₁ := (p ∣_ U.1).appLE ⊤ Dj le_top with hπ₁def
  set ρ := (p ⁻¹ᵁ U.1).toScheme.presheaf.map (homOfLE (le_top : Dj ≤ ⊤)).op with hρdef
  have hπσ : π₁ ≫ σ₁ = 𝟙 _ := by
    have h1 := Scheme.Hom.appLE_comp_appLE sW (p ∣_ U.1) ⊤ Dj ⊤ le_top e₁
    rw [e1] at h1
    refine h1.trans ?_
    exact (Scheme.Hom.appLE_eq_app (𝟙 _)).trans (Scheme.Hom.id_app _)
  have hρσ : ρ ≫ σ₁ = sW.appTop := by
    rw [hρdef, hσ₁def, Scheme.Hom.map_appLE]
    exact Scheme.Hom.appLE_eq_app sW
  letI : Algebra Γ(U.1.toScheme, ⊤) Γ((p ⁻¹ᵁ U.1).toScheme, Dj) := π₁.hom.toAlgebra
  let σ₁' : Γ((p ⁻¹ᵁ U.1).toScheme, Dj) →ₐ[Γ(U.1.toScheme, ⊤)] Γ(U.1.toScheme, ⊤) :=
    { σ₁.hom with
      commutes' := fun a => by
        change σ₁.hom (π₁.hom a) = a
        rw [← CommRingCat.comp_apply, hπσ]; rfl }
  have hmem₁ : ∀ i, ρ.hom (h i) ∈ RingHom.ker σ₁' := by
    intro i
    change σ₁.hom (ρ.hom (h i)) = 0
    rw [← CommRingCat.comp_apply, hρσ]
    exact RingHom.mem_ker.mp (hmem i)
  haveI : IsLocalization.Away j Γ((p ⁻¹ᵁ U.1).toScheme, Dj) :=
    (isAffineOpen_top _).isLocalization_basicOpen j
  have hker : RingHom.ker σ₁' = (RingHom.ker sW.appTop.hom).map ρ.hom := by
    refine ker_eq_map_of_isLocalization (Submonoid.powers j) sW.appTop.hom
      (σ₁' : Γ((p ⁻¹ᵁ U.1).toScheme, Dj) →+* Γ(U.1.toScheme, ⊤)) ?_
    exact congrArg CommRingCat.Hom.hom hρσ
  have hI₁ : RingHom.ker σ₁' ≤
      Ideal.span (Set.range fun i => ρ.hom (h i)) ⊔ RingHom.ker σ₁' ^ 2 := by
    rw [hker]; exact map_le_span_sup_sq ρ.hom _ h hI
  -- Step 3: `Ω[B₁/A]` is finitely generated (smoothness of `p` over `Zx`).
  have hfin : Module.Finite Γ((p ⁻¹ᵁ U.1).toScheme, Dj)
      Ω[Γ((p ⁻¹ᵁ U.1).toScheme, Dj)⁄Γ(U.1.toScheme, ⊤)] := by
    have hOW : (p ⁻¹ᵁ U.1).ι ''ᵁ Dj ≤ p ⁻¹ᵁ U.1 := (p ⁻¹ᵁ U.1).ι_image_le Dj
    have hOZx : (p ⁻¹ᵁ U.1).ι ''ᵁ Dj ≤ Zx :=
      (Scheme.Hom.image_mono _ hjZx).trans ((p ⁻¹ᵁ U.1).ι.image_preimage_le Zx)
    have hO : IsAffineOpen ((p ⁻¹ᵁ U.1).ι ''ᵁ Dj) := hDj.image_of_isOpenImmersion (p ⁻¹ᵁ U.1).ι
    haveI := smoothOfRelativeDimension_resLE_of_le p Zx (n + 1) U.1 _ hOZx hOW
    haveI : Smooth (p.resLE U.1 _ hOW) := SmoothOfRelativeDimension.smooth (n + 1) _
    haveI : IsAffine ((p ⁻¹ᵁ U.1).ι ''ᵁ Dj).toScheme := hO
    have hFT : ((p.resLE U.1 _ hOW).appLE ⊤ ⊤ le_top).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (f := p.resLE U.1 _ hOW)
        inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩ le_top
    have hFT2 := (congrArg (fun g => g.hom.FiniteType)
      (Scheme.Hom.resLE_appLE p hOW ⊤ ⊤ le_top)).mp hFT
    have hFT3 := (Scheme.Hom.appLE_congr p _ rfl ((p ⁻¹ᵁ U.1).ι ''ᵁ Dj).ι_image_top
      (fun f => f.hom.FiniteType)).mp hFT2
    have hπ₁ : π₁ = p.appLE (U.1.ι ''ᵁ ⊤) ((p ⁻¹ᵁ U.1).ι ''ᵁ Dj)
        ((Scheme.Hom.le_resLE_preimage_iff p le_rfl ⊤ Dj).mp le_top) :=
      (congrArg (fun g => Scheme.Hom.appLE g ⊤ Dj le_top)
        (Scheme.Hom.resLE_eq_morphismRestrict p).symm).trans
        (Scheme.Hom.resLE_appLE p le_rfl ⊤ Dj le_top)
    have hFT' : π₁.hom.FiniteType :=
      (congrArg (fun g => g.hom.FiniteType) hπ₁).mpr hFT3
    haveI : Algebra.FiniteType Γ(U.1.toScheme, ⊤) Γ((p ⁻¹ᵁ U.1).toScheme, Dj) := hFT'
    infer_instance
  -- Step 4: Nakayama.
  obtain ⟨r, hr1, hr⟩ :=
    exists_sub_one_mem_ker_smul_mem_span σ₁' (fun i => ρ.hom (h i)) hmem₁ hI₁
  -- Step 5: the open `V₀ := D(r)`.
  have hV₀W : (p ⁻¹ᵁ U.1).ι ''ᵁ ((p ⁻¹ᵁ U.1).toScheme.basicOpen r) ≤ p ⁻¹ᵁ U.1 :=
    (p ⁻¹ᵁ U.1).ι_image_le _
  have hrDj : (p ⁻¹ᵁ U.1).toScheme.basicOpen r ≤ Dj := (p ⁻¹ᵁ U.1).toScheme.basicOpen_le r
  have hV₀Zx : (p ⁻¹ᵁ U.1).ι ''ᵁ ((p ⁻¹ᵁ U.1).toScheme.basicOpen r) ≤ Zx :=
    (Scheme.Hom.image_mono _ (hrDj.trans hjZx)).trans ((p ⁻¹ᵁ U.1).ι.image_preimage_le Zx)
  have hσr : σ₁.hom r = 1 := by
    have h1 := hr1
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h1
    exact h1
  have hsV₀ : ∀ c ∈ U.1, s.base c ∈ (p ⁻¹ᵁ U.1).ι ''ᵁ ((p ⁻¹ᵁ U.1).toScheme.basicOpen r) := by
    intro c hc
    have hc' : sW ⟨c, hc⟩ ∈ (p ⁻¹ᵁ U.1).toScheme.basicOpen r := by
      have hpre : sW ⁻¹ᵁ (p ⁻¹ᵁ U.1).toScheme.basicOpen r = ⊤ := by
        rw [Scheme.preimage_basicOpen]
        have h1 : U.1.toScheme.basicOpen (σ₁.hom r) = ⊤ := by
          rw [hσr, Scheme.basicOpen_one]
        have h2 : U.1.toScheme.basicOpen (σ₁.hom r) =
            ⊤ ⊓ U.1.toScheme.basicOpen (sW.app Dj r) :=
          Scheme.basicOpen_res _ _ _
        rw [top_inf_eq] at h2
        rw [← h2, h1]
      have hmem' : (⟨c, hc⟩ : U.1.toScheme) ∈ sW ⁻¹ᵁ (p ⁻¹ᵁ U.1).toScheme.basicOpen r := by
        rw [hpre]; trivial
      exact (Scheme.Hom.mem_preimage sW).mp hmem'
    refine ⟨sW ⟨c, hc⟩, hc', ?_⟩
    exact hιsW _
  refine ⟨_, hV₀W, hV₀Zx, hsV₀, ?_⟩
  -- Step 6: `Ω` vanishes on `V₀`.
  have hiso := Omega.restrictIso φ (Z.homOfLE hV₀W ≫ φ) (Z.homOfLE hV₀W) (𝟙 _)
    (by rw [Category.comp_id])
  refine IsZero.of_iso ?_ hiso.symm
  apply Scheme.Modules.isZero_of_forall_subsingleton
  intro O
  show Subsingleton Γ(Omega φ, (Z.homOfLE hV₀W) ''ᵁ O)
  refine Scheme.Modules.subsingleton_sections_of_basicOpen_mul (Omega φ) hDj r ?_ _ ?_
  · intro f
    have hO' : IsAffineOpen ((p ⁻¹ᵁ U.1).toScheme.basicOpen (r * f)) := hDj.basicOpen (r * f)
    have hV𝔸 : IsAffineOpen (⊤ : (𝔸(ULift.{u} (Fin (n + 1)); U.1.toScheme)).Opens) :=
      isAffineOpen_top _
    letI : Algebra Γ(𝔸(ULift.{u} (Fin (n + 1)); U.1.toScheme), ⊤)
        Γ((p ⁻¹ᵁ U.1).toScheme, (p ⁻¹ᵁ U.1).toScheme.basicOpen (r * f)) :=
      (φ.appLE ⊤ _ le_top).hom.toAlgebra
    have e := Omega_appIso φ hV𝔸 hO' le_top
    refine (Equiv.subsingleton_congr e.toEquiv).mpr ?_
    letI : Algebra Γ(U.1.toScheme, ⊤)
        Γ((p ⁻¹ᵁ U.1).toScheme, (p ⁻¹ᵁ U.1).toScheme.basicOpen (r * f)) :=
      ((p ∣_ U.1).appLE ⊤ _ le_top).hom.toAlgebra
    letI : Algebra Γ(U.1.toScheme, ⊤) Γ(𝔸(ULift.{u} (Fin (n + 1)); U.1.toScheme), ⊤) :=
      ((𝔸(ULift.{u} (Fin (n + 1)); U.1.toScheme) ↘ U.1.toScheme).appLE ⊤ ⊤ le_top).hom.toAlgebra
    haveI : IsScalarTower Γ(U.1.toScheme, ⊤) Γ((p ⁻¹ᵁ U.1).toScheme, Dj)
        Γ((p ⁻¹ᵁ U.1).toScheme, (p ⁻¹ᵁ U.1).toScheme.basicOpen (r * f)) :=
      IsScalarTower.of_algebraMap_eq' (by
        change ((p ∣_ U.1).appLE ⊤ _ le_top).hom =
          ((p ⁻¹ᵁ U.1).toScheme.presheaf.map
            (homOfLE ((p ⁻¹ᵁ U.1).toScheme.basicOpen_le (r * f))).op).hom.comp π₁.hom
        exact (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_map (p ∣_ U.1) le_top
          (homOfLE ((p ⁻¹ᵁ U.1).toScheme.basicOpen_le (r * f))).op)).symm)
    haveI : IsScalarTower Γ(U.1.toScheme, ⊤) Γ(𝔸(ULift.{u} (Fin (n + 1)); U.1.toScheme), ⊤)
        Γ((p ⁻¹ᵁ U.1).toScheme, (p ⁻¹ᵁ U.1).toScheme.basicOpen (r * f)) :=
      IsScalarTower.of_algebraMap_eq' (by
        change ((p ∣_ U.1).appLE ⊤ _ le_top).hom =
          (φ.appLE ⊤ _ le_top).hom.comp
            ((𝔸(ULift.{u} (Fin (n + 1)); U.1.toScheme) ↘ U.1.toScheme).appLE ⊤ ⊤ le_top).hom
        exact (congrArg CommRingCat.Hom.hom
          ((Scheme.Hom.appLE_comp_appLE φ (𝔸(ULift.{u} (Fin (n + 1)); U.1.toScheme) ↘ U.1.toScheme)
            ⊤ ⊤ _ le_top le_top).trans
            (congrArg (fun g => Scheme.Hom.appLE g ⊤ ((p ⁻¹ᵁ U.1).toScheme.basicOpen (r * f)) le_top)
              (AffineSpace.homOfVector_over (p ∣_ U.1) h)))).symm)
    haveI : IsLocalization.Away (r * f)
        Γ((p ⁻¹ᵁ U.1).toScheme, (p ⁻¹ᵁ U.1).toScheme.basicOpen (r * f)) :=
      hDj.isLocalization_basicOpen (r * f)
    haveI : Algebra.FormallyUnramified Γ((p ⁻¹ᵁ U.1).toScheme, Dj)
        Γ((p ⁻¹ᵁ U.1).toScheme, (p ⁻¹ᵁ U.1).toScheme.basicOpen (r * f)) :=
      Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers (r * f))
    refine subsingleton_kaehler_of_span (A := Γ(U.1.toScheme, ⊤)) (fun i => ρ.hom (h i))
      (fun i => AffineSpace.coord U.1.toScheme i) ?_ r ?_ hr
    · intro i
      change (φ.appLE ⊤ _ le_top).hom (AffineSpace.coord U.1.toScheme i) =
        ((p ⁻¹ᵁ U.1).toScheme.presheaf.map
          (homOfLE ((p ⁻¹ᵁ U.1).toScheme.basicOpen_le (r * f))).op).hom (ρ.hom (h i))
      rw [← CommRingCat.comp_apply, hρdef, ← Functor.map_comp, ← op_comp]
      show (φ.appTop ≫ (p ⁻¹ᵁ U.1).toScheme.presheaf.map (homOfLE le_top).op).hom _ = _
      rw [CommRingCat.comp_apply, hφdef, AffineSpace.homOfVector_appTop_coord]
      rfl
    · have hu := IsLocalization.Away.algebraMap_isUnit
        (S := Γ((p ⁻¹ᵁ U.1).toScheme, (p ⁻¹ᵁ U.1).toScheme.basicOpen (r * f))) (r * f)
      rw [map_mul] at hu
      exact isUnit_of_mul_isUnit_left hu
  · rintro _ ⟨y, -, rfl⟩
    have h1 : (p ⁻¹ᵁ U.1).ι ((Z.homOfLE hV₀W) y) ∈
        (p ⁻¹ᵁ U.1).ι ''ᵁ ((p ⁻¹ᵁ U.1).toScheme.basicOpen r) := by
      have := congrArg (fun g => g y) (Z.homOfLE_ι hV₀W)
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact y.2
    have h2 : (Z.homOfLE hV₀W) y ∈
        (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ ((p ⁻¹ᵁ U.1).ι ''ᵁ ((p ⁻¹ᵁ U.1).toScheme.basicOpen r)) :=
      (Scheme.Hom.mem_preimage _).mpr h1
    rwa [Scheme.Hom.preimage_image_eq] at h2

end Main

end MiyaokaMori.EtaleChartOmega

end
