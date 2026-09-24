import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistPushTransition
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01mw

/-! # Chart bookkeeping for the local evaluation on a relative Proj

Generic bookkeeping for the naturality of the local evaluation `evaluationLocal` of
module `RelativeProjEvaluation` on the affine base
(Stacks 01NR: the map `A_m → Γ(Proj A, O(m))`, `a ↦ a/1`, is compatible with restriction `A(V) → A(W)`).

Contents (everything is stated for **variables** — schemes, morphisms, sheaves —
so that the kernel never unfolds the concrete relative Proj):

* `Adjunction.homEquiv_iso_hom_app_comp_of_conjugateEquiv`: if `α : L₁ ≅ L₂` and `β : R₁ ≅ R₂` are conjugate
  isomorphisms between two adjunctions, transposing `α.hom.app X ≫ ψ` along the first adjunction is transposing
  `ψ` along the second followed by `β.inv`.
* `Scheme.Modules.chartHomShape φ c ι hc k`: the shape of the chart comparison map `twistAffineHom`
  (`Stacks01nr.lean`): `T|_ι ≅ ι^*T ≅ (φ ≫ c)^*T ≅ φ^*c^*T → φ^*G`, the last map being `φ^*` of the adjoint
  transpose of `k : T ⟶ c_*G` (for `twistAffineHom`, `k = twistπ` and the transpose is `twistChartHom`).
* `Scheme.Modules.pullbackToRestrictPushforward φ c ι hc : φ^*G ⟶ (c_*G)|_ι`, the canonical comparison, and
  - `chartHomShape_comp_pullbackToRestrictPushforward`: `chartHomShape k ≫ pullbackToRestrictPushforward =
    (restrictFunctor ι).map k` (purely formal: naturality of the three isomorphisms and
    `homEquiv_counit`);
  - `presheaf_map_map_homOfLE` (two restrictions compose), `restrictFunctor_map_app_image` (sections of
    `(restrictFunctor f).map k`, definitional);
  - `pullbackToRestrictPushforward_app_unit`: on sections, `pullbackToRestrictPushforward` sends the unit
    `Γ(G, U) → Γ(φ^*G, φ⁻¹U)` to the restriction `Γ(G, U) → Γ(G, c⁻¹(ι''(φ⁻¹U)))`. Proof: the adjoint transpose of
    `pullbackToRestrictPushforward` is computed with the conjugate lemma above (`conjugateEquiv_pullbackComp_inv`,
    `homEquiv_leftAdjointUniq_hom_app`), it is `c_*`-preimage of `restrictAdjunction.unit ≫ pushforwardComp.inv`,
    whose components are restrictions (`restrictAdjunction_unit_app_app`, `pushforwardComp_inv_app_app`).
  Together (`app_image_eq_of_chartHomShape_heq`, with `Eq`/`HEq` bridges for a second spelling of the objects):
  for `z ∈ Γ(T|_ι, φ⁻¹U)` with `chartHomShape k (z) = unit (s)`, `k.app (ι''(φ⁻¹U)) z = s|_{…}`.
* `Proj.twistPushTransition_res_twistSection_apply`: the transition map θ_f of `ProjTwistPushTransition`
  sends (the restriction of) the section `a/1` to `(f a)/1`, pointwise (`twistPushTransition_app_apply` +
  `Localization.localRingHom_mk`).

Source: Stacks 01NR (compatibility of `A_n → Γ(Proj A, O(n))` with the gluing), 01LI; Proposition 3.2 of the paper.
-/

set_option autoImplicit false

universe u v₁ u₁ v₂ u₂

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- If `α : L₁ ≅ L₂` and `β : R₁ ≅ R₂` are conjugate (`conjugateEquiv adj₁ adj₂ α.inv = β.hom`), then
transposing `α.hom.app X ≫ ψ` along `adj₁` is transposing `ψ` along `adj₂` followed by `β.inv`. -/
theorem homEquiv_iso_hom_app_comp_of_conjugateEquiv (α : L₁ ≅ L₂) (β : R₁ ≅ R₂)
    (hβ : conjugateEquiv adj₁ adj₂ α.inv = β.hom) {X : C} {Y : D} (ψ : L₂.obj X ⟶ Y) :
    adj₁.homEquiv X Y (α.hom.app X ≫ ψ) = adj₂.homEquiv X Y ψ ≫ β.inv.app Y := by
  have h1 := unit_conjugateEquiv adj₁ adj₂ α.inv X
  rw [hβ] at h1
  have h2 : adj₁.unit.app X =
      adj₂.unit.app X ≫ R₂.map (α.inv.app X) ≫ β.inv.app (L₁.obj X) := by
    rw [← reassoc_of% h1, Iso.hom_inv_id_app, Category.comp_id]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, h2, Functor.map_comp]
  simp only [Category.assoc]
  rw [β.inv.naturality_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, β.inv.naturality]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme.Modules

variable {Q P Y : AlgebraicGeometry.Scheme.{u}} (φ : Q ⟶ P) (c : P ⟶ Y)
  [AlgebraicGeometry.IsOpenImmersion φ] [AlgebraicGeometry.IsOpenImmersion c]
  (ι : Q ⟶ Y) [AlgebraicGeometry.IsOpenImmersion ι] (hc : φ ≫ c = ι)
  {T : Y.Modules} {G : P.Modules}

/-- Two successive restrictions of a section of a module sheaf compose to one restriction. -/
theorem presheaf_map_map_homOfLE (M : Y.Modules) {U V W : Y.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W) (t : Γ(M, W)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op t) =
      M.presheaf.map (homOfLE (h₁.trans h₂)).op t := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- Sections of `(restrictFunctor f).map k` over `W` are `k.app (f ''ᵁ W)` (definitional; stated on variables so
that the kernel checks it on generic terms only). -/
theorem restrictFunctor_map_app_image {f : Q ⟶ Y} [AlgebraicGeometry.IsOpenImmersion f] {M N : Y.Modules}
    (k : M ⟶ N) (W : Q.Opens) : ((restrictFunctor f).map k).app W = k.app (f ''ᵁ W) := rfl

/-- The shape of the chart comparison map `twistAffineHom` (`Stacks01nr.lean`):
`T|_ι ≅ ι^*T ≅ (φ ≫ c)^*T ≅ φ^*c^*T → φ^*G`, the last map being `φ^*` of the adjoint transpose of `k : T ⟶ c_*G`. -/
def chartHomShape (k : T ⟶ (pushforward c).obj G) : T.restrict ι ⟶ (pullback φ).obj G :=
  (restrictFunctorIsoPullback ι).hom.app T ≫
    (pullbackCongr hc.symm).hom.app T ≫
    (pullbackComp φ c).inv.app T ≫
    (pullback φ).map (((pullbackPushforwardAdjunction c).homEquiv _ _).symm k)

/-- The canonical map `φ^*G ⟶ (c_*G)|_ι`: `G ≅ c^*c_*G` (inverse counit; `c` is an open immersion, so `c_*` is
fully faithful), then `φ^*c^*(c_*G) ≅ (φ ≫ c)^*(c_*G) ≅ ι^*(c_*G) ≅ (c_*G)|_ι`. -/
def pullbackToRestrictPushforward : (pullback φ).obj G ⟶ ((pushforward c).obj G).restrict ι :=
  (pullback φ).map (inv ((pullbackPushforwardAdjunction c).counit.app G)) ≫
    (pullbackComp φ c).hom.app ((pushforward c).obj G) ≫
    (pullbackCongr hc.symm).inv.app ((pushforward c).obj G) ≫
    (restrictFunctorIsoPullback ι).inv.app ((pushforward c).obj G)

omit [AlgebraicGeometry.IsOpenImmersion φ] in
/-- `chartHomShape k ≫ pullbackToRestrictPushforward = (restrictFunctor ι).map k`. -/
theorem chartHomShape_comp_pullbackToRestrictPushforward (k : T ⟶ (pushforward c).obj G) :
    chartHomShape φ c ι hc k ≫ pullbackToRestrictPushforward φ c ι hc =
      (restrictFunctor ι).map k := by
  unfold chartHomShape pullbackToRestrictPushforward
  have h1 : (((pullbackPushforwardAdjunction c).homEquiv _ _).symm k) ≫
      inv ((pullbackPushforwardAdjunction c).counit.app G) = (pullback c).map k := by
    rw [Adjunction.homEquiv_counit, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, h1]
  have h2 := NatIso.naturality_1 (pullbackComp φ c) k
  rw [Functor.comp_map] at h2
  rw [reassoc_of% h2, reassoc_of% (NatIso.naturality_2 (pullbackCongr hc.symm) k),
    NatIso.naturality_2]

include hc in
theorem preimage_image_preimage_le (U : P.Opens) : c ⁻¹ᵁ (ι ''ᵁ (φ ⁻¹ᵁ U)) ≤ U := by
  subst hc
  rw [AlgebraicGeometry.Scheme.Hom.comp_image, c.preimage_image_eq]
  exact φ.image_preimage_le U

/-- The adjoint transpose of `(restrictFunctorIsoPullback f).inv.app M` is the unit of `restrictAdjunction`. -/
theorem homEquiv_restrictFunctorIsoPullback_inv_app (f : Q ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f]
    (M : Y.Modules) :
    (pullbackPushforwardAdjunction f).homEquiv _ _ ((restrictFunctorIsoPullback f).inv.app M) =
      (restrictAdjunction f).unit.app M := by
  rw [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq_inv_app,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]

/-- On sections, `pullbackToRestrictPushforward` sends the unit `Γ(G, U) → Γ(φ^*G, φ⁻¹U)` to the restriction
`Γ(G, U) → Γ(G, c⁻¹(ι''(φ⁻¹U)))` (`Γ((c_*G)|_ι, φ⁻¹U) = Γ(G, c⁻¹(ι''(φ⁻¹U)))` by definition). -/
theorem pullbackToRestrictPushforward_app_unit (U : P.Opens) (s : Γ(G, U)) :
    (pullbackToRestrictPushforward φ c ι hc (G := G)).app (φ ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction φ).unit.app G).app U s) =
      (show Γ(((pushforward c).obj G).restrict ι, φ ⁻¹ᵁ U) from
        G.presheaf.map (homOfLE (preimage_image_preimage_le φ c ι hc U)).op s) := by
  subst hc
  set M : Y.Modules := (pushforward c).obj G with hM
  set N : Q.Modules := M.restrict (φ ≫ c) with hN
  set ν := pullbackToRestrictPushforward φ c (φ ≫ c) rfl (G := G) with hν
  -- Step 1: the value is the adjoint transpose of `ν` applied to `s`
  have e1 : ν.app (φ ⁻¹ᵁ U) (((pullbackPushforwardAdjunction φ).unit.app G).app U s) =
      ((pullbackPushforwardAdjunction φ).homEquiv _ _ ν).app U s := by
    rw [Adjunction.homEquiv_unit, Hom.comp_app, pushforward_map_app]; rfl
  -- Step 2: the transpose of `ν` is the `c_*`-preimage of `restrictAdjunction.unit ≫ pushforwardComp.inv`
  have hB : (pullbackCongr (rfl : φ ≫ c = φ ≫ c).symm).inv.app M = 𝟙 _ := rfl
  set ru := (restrictAdjunction (φ ≫ c)).unit.app M with hru
  set pcinv := (pushforwardComp φ c).inv.app N with hpcinv
  have e3 : (pullbackPushforwardAdjunction φ).homEquiv _ _
      ((pullbackComp φ c).hom.app M ≫ (restrictFunctorIsoPullback (φ ≫ c)).inv.app M) =
      ((pullbackPushforwardAdjunction c).homEquiv _ _).symm (ru ≫ pcinv) := by
    rw [Equiv.eq_symm_apply]
    have h := Adjunction.homEquiv_iso_hom_app_comp_of_conjugateEquiv
      ((pullbackPushforwardAdjunction c).comp (pullbackPushforwardAdjunction φ))
      (pullbackPushforwardAdjunction (φ ≫ c)) (pullbackComp φ c) (pushforwardComp φ c)
      (conjugateEquiv_pullbackComp_inv φ c) ((restrictFunctorIsoPullback (φ ≫ c)).inv.app M)
    rw [Adjunction.comp_homEquiv] at h
    erw [Equiv.trans_apply] at h
    rw [homEquiv_restrictFunctorIsoPullback_inv_app] at h
    exact h
  obtain ⟨μ, hμ⟩ : ∃ μ : G ⟶ (pushforward φ).obj N, (pushforward c).map μ = ru ≫ pcinv :=
    ⟨_, Functor.map_preimage _ _⟩
  have e4 : (pullbackPushforwardAdjunction φ).homEquiv _ _ ν = μ := by
    rw [hν]
    unfold pullbackToRestrictPushforward
    rw [hB, Category.id_comp, Adjunction.homEquiv_naturality_left]
    erw [e3]
    rw [Adjunction.homEquiv_counit, ← hμ]
    have hn := (pullbackPushforwardAdjunction c).counit.naturality μ
    rw [Functor.comp_map, Functor.id_map] at hn
    rw [hn, IsIso.inv_hom_id_assoc]
  rw [e1, e4]
  -- Step 3: the components of `μ` are restrictions
  have hW : ∀ W : Y.Opens, μ.app (c ⁻¹ᵁ W) = (ru ≫ pcinv).app W := fun W => by
    rw [← hμ]; rfl
  have hU : μ.app (c ⁻¹ᵁ (c ''ᵁ U)) =
      M.presheaf.map (homOfLE ((φ ≫ c).image_preimage_le (c ''ᵁ U))).op := by
    rw [hW, Hom.comp_app, hru, hpcinv, restrictAdjunction_unit_app_app, pushforwardComp_inv_app_app]
    exact Category.comp_id _
  have i₁ : U ≤ c ⁻¹ᵁ (c ''ᵁ U) := le_of_eq (c.preimage_image_eq U).symm
  have i₂ : c ⁻¹ᵁ (c ''ᵁ U) ≤ U := le_of_eq (c.preimage_image_eq U)
  have hs : G.presheaf.map (homOfLE i₁).op (G.presheaf.map (homOfLE i₂).op s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have : (homOfLE i₂).op ≫ (homOfLE i₁).op = 𝟙 (op U) := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]; rfl
  have hnat : μ.app U (G.presheaf.map (homOfLE i₁).op (G.presheaf.map (homOfLE i₂).op s)) =
      ((pushforward φ).obj N).presheaf.map (homOfLE i₁).op
        (μ.app (c ⁻¹ᵁ (c ''ᵁ U)) (G.presheaf.map (homOfLE i₂).op s)) := by
    have := ConcreteCategory.congr_hom (μ.mapPresheaf.naturality (homOfLE i₁).op)
      (G.presheaf.map (homOfLE i₂).op s)
    simpa only [ConcreteCategory.comp_apply, mapPresheaf_app, unop_op] using this
  rw [hs] at hnat
  rw [hnat, hU]
  have j₂ : c ⁻¹ᵁ ((φ ≫ c) ''ᵁ (φ ⁻¹ᵁ (c ⁻¹ᵁ (c ''ᵁ U)))) ≤ c ⁻¹ᵁ (c ''ᵁ U) :=
    c.preimage_mono ((φ ≫ c).image_preimage_le (c ''ᵁ U))
  have j₁ : c ⁻¹ᵁ ((φ ≫ c) ''ᵁ (φ ⁻¹ᵁ U)) ≤ c ⁻¹ᵁ ((φ ≫ c) ''ᵁ (φ ⁻¹ᵁ (c ⁻¹ᵁ (c ''ᵁ U)))) :=
    c.preimage_mono ((φ ≫ c).image_mono (φ.preimage_mono i₁))
  show G.presheaf.map (homOfLE j₁).op (G.presheaf.map (homOfLE j₂).op (G.presheaf.map (homOfLE i₂).op s)) =
    G.presheaf.map (homOfLE (preimage_image_preimage_le φ c (φ ≫ c) rfl U)).op s
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 2

/-- **Sections of the limit projection on the chart, from the chart comparison map.** Let `H` be the
chart comparison map `T|_ι → φ^*G` written out as `RFIP ≫ pullbackCongr ≫ pullbackComp ≫ φ^*θ` (this is the
literal body of `twistAffineHom`, `Stacks01nr.lean`), where `θ` is the adjoint transpose of `k' : T' ⟶ c'_*G'`
(`hθ`). If `H z = unit s` for `z ∈ Γ(T|_ι, φ⁻¹U)`, `s ∈ Γ(G, U)`, then `k z = s|_{c⁻¹(ι''(φ⁻¹U))}` for any `k`
with `HEq k' k`.

**Binder discipline (kernel cost).** Everything that occurs in `hz` — `φ c ι`, the open
immersion proof `hιOI`, the iso `B` (`pullbackCongr` of the body's own proof of `φ ≫ c = ι`; proofs cannot be
unified because of proof irrelevance, so the *iso* is the variable and `hB` relates it to the caller's proof at top
level), `T G θ U s z` — is implicit and meant to be *unified from the actual hypothesis*
(the unfolded body of `twistAffineHom`), and everything that occurs in `hθ` — `c' T' G' k'` — is unified from `θ`
(the unfolded `twistChartHom`). Nothing may be re-elaborated by the caller: the body's instance proofs are
auxiliary constants (`twistAffineHom._proof_n`), and a hypothesis differing from the body only in such proof
constants under `Iso.hom`/`NatTrans.app`/`≫` makes the kernel `whnf` the whole pullback machinery (measured
40–50 s per declaration). The bridges `hP hY hc' hT hG hk` between the two spellings are `rfl`/`HEq.rfl` at top
level (cheap). -/
theorem app_image_eq_of_chartHomShape_heq {Q P Y : AlgebraicGeometry.Scheme.{u}} {φ : Q ⟶ P} {c : P ⟶ Y}
    {ι : Q ⟶ Y} [hφOI : AlgebraicGeometry.IsOpenImmersion φ] [hcOI : AlgebraicGeometry.IsOpenImmersion c]
    {hιOI : AlgebraicGeometry.IsOpenImmersion ι} (hc : φ ≫ c = ι)
    {B : pullback ι ≅ pullback (φ ≫ c)} (hB : B = pullbackCongr hc.symm)
    {T : Y.Modules} {G : P.Modules} {θ : (pullback c).obj T ⟶ G} {U : P.Opens} {s : Γ(G, U)}
    {z : Γ(@AlgebraicGeometry.Scheme.Modules.restrict _ _ T ι hιOI, φ ⁻¹ᵁ U)}
    (hz : ((@restrictFunctorIsoPullback _ _ ι hιOI).hom.app T ≫ B.hom.app T ≫
        (pullbackComp φ c).inv.app T ≫ (pullback φ).map θ).app (φ ⁻¹ᵁ U) z =
      ((pullbackPushforwardAdjunction φ).unit.app G).app U s)
    (k : T ⟶ (pushforward c).obj G)
    {P' Y' : AlgebraicGeometry.Scheme.{u}} {c' : P' ⟶ Y'} {T' : Y'.Modules} {G' : P'.Modules}
    {k' : T' ⟶ (pushforward c').obj G'}
    (hθ : HEq θ (((pullbackPushforwardAdjunction c').homEquiv T' G').symm k'))
    (hP : P' = P) (hY : Y' = Y) (hc' : HEq c' c) (hT : HEq T' T) (hG : HEq G' G) (hk : HEq k' k) :
    k.app (@AlgebraicGeometry.Scheme.Hom.opensFunctor _ _ ι hιOI |>.obj (φ ⁻¹ᵁ U)) z =
      (show Γ((pushforward c).obj G, @AlgebraicGeometry.Scheme.Hom.opensFunctor _ _ ι hιOI |>.obj (φ ⁻¹ᵁ U)) from
        G.presheaf.map (homOfLE (@preimage_image_preimage_le _ _ _ φ c hφOI hcOI ι hιOI hc U)).op s) := by
  haveI := hιOI
  subst hB
  obtain rfl := hP.symm
  obtain rfl := hY.symm
  obtain rfl := (eq_of_heq hc').symm
  obtain rfl := (eq_of_heq hT).symm
  obtain rfl := (eq_of_heq hG).symm
  obtain rfl := (eq_of_heq hk).symm
  obtain rfl := eq_of_heq hθ
  have h1 := ConcreteCategory.congr_hom (congrArg (fun m => Hom.app m (φ ⁻¹ᵁ U))
    (chartHomShape_comp_pullbackToRestrictPushforward φ c ι hc k)) z
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, restrictFunctor_map_app_image] at h1
  unfold chartHomShape at h1
  rw [hz, pullbackToRestrictPushforward_app_unit] at h1
  exact h1.symm

end AlgebraicGeometry.Scheme.Modules

theorem Localization.localRingHom_mk_one {R P : Type u} [CommRing R] [CommRing P] (I : Ideal R)
    [I.IsPrime] (J : Ideal P) [J.IsPrime] (f : R →+* P) (h : I = J.comap f) (a : R) :
    Localization.localRingHom I J f h (Localization.mk a 1) = Localization.mk (f a) 1 := by
  rw [Localization.localRingHom_mk]
  congr 1
  exact Subtype.ext (map_one f)

namespace AlgebraicGeometry.Proj

-- The instance binders are named so that callers can pass them explicitly: when `f` is given in one spelling of the
-- graded ring and `𝒜` in another (definitionally equal) one, unification assigns the instances from `f`, and
-- instance search for `GradedRing 𝒜` then fails at reducible transparency.
variable {σ τ A B : Type u} [instA : CommRing A] [instσ : SetLike σ A]
    [instσ' : AddSubgroupClass σ A] [instB : CommRing B] [instτ : SetLike τ B] [instτ' : AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [inst𝒜 : GradedRing 𝒜] [instℬ : GradedRing ℬ]

/-- Pointwise: the transition map `T(f)` (`ProjTwistPushTransition`) sends a section `y` of `O_{Proj 𝒜}(d)`
whose value is `a/1` at every point to a section with value `(f a)/1` at every point. (Stated for an arbitrary
`y` with a pointwise hypothesis so that the caller never has to match the syntactic form of `y`.) -/
theorem twistPushTransition_apply_of_val (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (d : ℤ) (a : A)
    {Y : AlgebraicGeometry.Scheme.{u}} (ιA : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (ιB : AlgebraicGeometry.Proj ℬ ⟶ Y) (w : AlgebraicGeometry.Proj.map f hf ≫ ιA = ιB) (U : Y.Opens)
    (y : Γ(AlgebraicGeometry.Proj.twist 𝒜 d, ιA ⁻¹ᵁ U))
    (hy : ∀ q, Subtype.val (y : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 d (ιA ⁻¹ᵁ U)) q =
      Localization.mk a 1)
    (p : (ιB ⁻¹ᵁ U : (AlgebraicGeometry.Proj ℬ).Opens)) :
    Subtype.val (((twistPushTransition f hf d ιA ιB w).app U).hom y :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ℬ d (ιB ⁻¹ᵁ U)) p =
      Localization.mk (f a) 1 := by
  subst w
  have hp : ProjectiveSpectrum.comap f hf p.1 ∈ (ιA ⁻¹ᵁ U : (AlgebraicGeometry.Proj 𝒜).Opens) := p.2
  have := p.1.isPrime
  have := (ProjectiveSpectrum.comap f hf p.1).isPrime
  refine (twistPushTransition_app_apply f hf d ιA _ rfl U _ p hp).trans ?_
  rw [hy]
  exact Localization.localRingHom_mk_one _ _ (f : A →+* B) rfl a

/-- Pointwise: the transition map `T(f)` (`ProjTwistPushTransition`) sends the restriction of the section
`x_a = a/1` (`twistSection`, Stacks 01MN) to `(f a)/1`. -/
theorem twistPushTransition_res_twistSection_apply (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) {d : ℕ} (a : A)
    (ha : a ∈ 𝒜 d) {Y : AlgebraicGeometry.Scheme.{u}} (ιA : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (ιB : AlgebraicGeometry.Proj ℬ ⟶ Y) (w : AlgebraicGeometry.Proj.map f hf ≫ ιA = ιB) (U : Y.Opens)
    (y : (ιB ⁻¹ᵁ U : (AlgebraicGeometry.Proj ℬ).Opens)) :
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ℬ (d : ℤ) (ιB ⁻¹ᵁ U) from
      ((twistPushTransition f hf (d : ℤ) ιA ιB w).app U).hom
        ((AlgebraicGeometry.Proj.twist 𝒜 (d : ℤ)).presheaf.map (homOfLE le_top).op
          (AlgebraicGeometry.Proj.twistSection 𝒜 a ha))).1 y =
      Localization.mk (f a) 1 := by
  subst w
  have hy : ProjectiveSpectrum.comap f hf y.1 ∈ (ιA ⁻¹ᵁ U : (AlgebraicGeometry.Proj 𝒜).Opens) := y.2
  have := y.1.isPrime
  have := (ProjectiveSpectrum.comap f hf y.1).isPrime
  refine (twistPushTransition_app_apply f hf (d : ℤ) ιA _ rfl U _ y hy).trans ?_
  exact Localization.localRingHom_mk_one _ _ (f : A →+* B) rfl a

end AlgebraicGeometry.Proj

end
