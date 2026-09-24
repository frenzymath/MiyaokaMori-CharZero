import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf
import MiyaokaMori.RingTheory.GradedRing.VeroneseGradedRing

/-! # The degree-rescaling comparison morphism for a Veronese subring

The **degree-rescaling comparison morphism** for a Veronese subring (Stacks 0B5J, the identification
`O_{Proj S^{(d)}}(n) ↔ O_{Proj S}(nd)` that accompanies the Veronese isomorphism `Proj S ≅ Proj S^{(d)}`).

Setting. `𝒜` an `ℕ`-graded ring on `A`, `d > 0`, `B := veroneseGrading 𝒜 d` the `d`-th Veronese subring
(`B_k = 𝒜_{kd}`, carrier `veroneseSubring 𝒜 d`), `ι : B → A` the subring inclusion (`(veroneseSubring 𝒜 d).subtype`).
Let `φ : Proj 𝒜 ⟶ Proj B` and `ψ : Proj B ⟶ Proj 𝒜` be morphisms of schemes such that
* `hφψ`: `ψ ∘ φ = id` on points;
* `hpt`: on points `φ` is the contraction `𝔭 ↦ ι⁻¹ 𝔭` (as ideals: `(φ 𝔭).toIdeal = Ideal.comap ι 𝔭.toIdeal`);
* `happ`: on structure-sheaf sections `ψ` is compatible with the fibre maps `B_{φ 𝔭} → A_𝔭` (ordinary localizations,
  `Localization.localRingHom`): `localRingHom ((ψ^# r)(φ 𝔭)) = r(𝔭)` in `A_𝔭` for every section `r` of `O_{Proj 𝒜}`.

(For `φ = Proj.veroneseHom 𝒜 d hd`, `ψ = (Proj.veroneseIso 𝒜 d hd).hom = inv veroneseHom`, these are
proved in the module `VeroneseTwistPullbackVeroneseHomApp`. They are taken as **hypotheses** here so that the data
below does not depend on any proposition.)

Construction. For a section `s` of `O_{Proj B}(n)` over `V ⊆ Proj B` (a function
`𝔮 ↦ s(𝔮) ∈ B_𝔮`, locally a fraction `b/t` with `b ∈ B_{j+n}`, `t ∈ B_j`) and `𝔭 ∈ φ⁻¹ V`, put
`(Ψ s)(𝔭) := localRingHom (φ 𝔭) 𝔭 ι (s (φ 𝔭)) ∈ A_𝔭`, i.e. `b/t ↦ b/t`. This is locally a fraction of degree `nd`
(`b ∈ 𝒜_{(j+n)d}`, `t ∈ 𝒜_{jd}`, `t ∉ 𝔭` because `t ∉ ι⁻¹ 𝔭`; `veroneseComapFun_isLocallyFraction`), additive,
and `O_{Proj 𝒜}`-linear by `happ` (the structure sheaves correspond by the same fibre maps in degree `0`).
Hence a morphism of sheaves of modules `veroneseTwistHom : ψ_* O_{Proj B}(n) ⟶ O_{Proj 𝒜}(k)` for `k = n * d`,
with the pointwise formula `veroneseTwistHom_app_apply` (definitional).

Its bijectivity on every open (hence `IsIso`) is proved separately
(`veroneseTwistHom_app_bijective`, below): injectivity is the injectivity of `b/t ↦ b/t` on homogeneous fractions
(`u b = 0`, `u ∉ 𝔭` ⇒ a homogeneous component `u_i ∉ 𝔭` with `u_i b = 0` ⇒ `u_i^d ∈ B ∖ φ 𝔭` kills `b`), surjectivity is
`a/t = (a t^{d-1}) / t^d` with `a t^{d-1} ∈ B`, `t^d ∈ B`, together with `φ` being a homeomorphism (inverse `ψ`).

Source: Stacks 0B5J (lemma-d-uple); Stacks 01MX (the comparison map `θ`, whose degree-preserving version is
`Proj.twistToPushforward`, `ProjMapTwistComparison`, which this module imitates);
Lemma 2.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- as in `ProjTwistingSheaf` / `WeightedProjTwisting`: defeq checks on homogeneous
-- localizations are very slow at default transparency
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ)

/-- The subring inclusion `ι : S^{(d)} → S` as a ring homomorphism. -/
abbrev veroneseSubringHom : veroneseSubring 𝒜 d →+* A := (veroneseSubring 𝒜 d).subtype

/-- `φ : Proj 𝒜 ⟶ Proj 𝒜^{(d)}` is **pointwise the contraction along `ι`**:
`(φ 𝔭).toIdeal = ι⁻¹ 𝔭.toIdeal` for every `𝔭`. (For `φ = veroneseHom` this is
`veroneseHom_base_toIdeal_eq`, `Stacks0b5j`.) -/
def IsVeroneseContraction (φ : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)) :
    Prop :=
  ∀ x : AlgebraicGeometry.Proj 𝒜,
    (φ.base x).asHomogeneousIdeal.toIdeal = Ideal.comap (veroneseSubringHom 𝒜 d) x.asHomogeneousIdeal.toIdeal

variable {𝒜 d}

/-- The fibre map `B_{φ 𝔭} → A_𝔭`, `b/t ↦ b/t` (`Localization.localRingHom` along `ι`). -/
def veroneseFiberMap {φ : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)}
    (hpt : IsVeroneseContraction 𝒜 d φ) (x : AlgebraicGeometry.Proj 𝒜) :
    MiyaokaMori.WeightedJets.ProjTwisting.Fiber (veroneseGrading 𝒜 d) (φ.base x) →+*
      MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 x :=
  Localization.localRingHom (φ.base x).asHomogeneousIdeal.toIdeal x.asHomogeneousIdeal.toIdeal
    (veroneseSubringHom 𝒜 d) (hpt x)

/-- A homogeneous `t ∈ B_j` not in `φ 𝔭` is (as an element of `A`) not in `𝔭`. -/
theorem notMem_of_notMem_base {φ : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)}
    (hpt : IsVeroneseContraction 𝒜 d φ) (x : AlgebraicGeometry.Proj 𝒜) {t : veroneseSubring 𝒜 d}
    (ht : t ∉ (φ.base x).asHomogeneousIdeal) : (t : A) ∉ x.asHomogeneousIdeal := by
  intro h
  apply ht
  change t ∈ (φ.base x).asHomogeneousIdeal.toIdeal
  rw [hpt x, Ideal.mem_comap]
  exact h

theorem veroneseFiberMap_mk {φ : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)}
    (hpt : IsVeroneseContraction 𝒜 d φ) (x : AlgebraicGeometry.Proj 𝒜) (b : veroneseSubring 𝒜 d)
    (t : (φ.base x).asHomogeneousIdeal.toIdeal.primeCompl) :
    veroneseFiberMap hpt x (Localization.mk b t) =
      Localization.mk (b : A) ⟨(t : veroneseSubring 𝒜 d), notMem_of_notMem_base hpt x t.2⟩ :=
  Localization.localRingHom_mk _ _ _ _ _ _

/-- The comparison function on sections: `s ↦ (𝔭 ↦ localRingHom (s (φ 𝔭)))` (cf. `Proj.twistComapFun`). -/
def veroneseComapFun {φ : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)}
    (hpt : IsVeroneseContraction 𝒜 d φ)
    (U : Opens (ProjectiveSpectrum.top (veroneseGrading 𝒜 d))) (V : Opens (ProjectiveSpectrum.top 𝒜))
    (hUV : V.1 ⊆ φ.base ⁻¹' U.1)
    (s : ∀ x : U, MiyaokaMori.WeightedJets.ProjTwisting.Fiber (veroneseGrading 𝒜 d) x.1) (y : V) :
    MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 y.1 :=
  veroneseFiberMap hpt y.1 (s ⟨φ.base y.1, hUV y.2⟩)

/-- Degree bookkeeping: a fraction of degree `n` for `B` (`(i : ℤ) = j + n`) is a fraction of degree `n * d` for `𝒜`
(`(i * d : ℤ) = j * d + n * d`). -/
theorem veronese_degree_eq {i j : ℕ} {n k : ℤ} (hk : k = n * d) (hij : (i : ℤ) = j + n) :
    ((i * d : ℕ) : ℤ) = (j * d : ℕ) + k := by
  subst hk
  push_cast
  rw [hij]
  ring

/-- The comparison function preserves "locally a homogeneous fraction", rescaling the degree by `d`
(cf. `Proj.twistComapFun_isLocallyFraction`). -/
theorem veroneseComapFun_isLocallyFraction
    {φ : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)}
    (hpt : IsVeroneseContraction 𝒜 d φ) (n k : ℤ) (hk : k = n * d)
    (U : Opens (ProjectiveSpectrum.top (veroneseGrading 𝒜 d))) (V : Opens (ProjectiveSpectrum.top 𝒜))
    (hUV : V.1 ⊆ φ.base ⁻¹' U.1)
    (s : ∀ x : U, MiyaokaMori.WeightedJets.ProjTwisting.Fiber (veroneseGrading 𝒜 d) x.1)
    (hs : (MiyaokaMori.WeightedJets.ProjTwisting.locallyFraction (veroneseGrading 𝒜 d) n).pred s) :
    (MiyaokaMori.WeightedJets.ProjTwisting.locallyFraction 𝒜 k).pred (veroneseComapFun hpt U V hUV s) := by
  intro y
  obtain ⟨W, hmW, iWU, hfrac⟩ := hs ⟨φ.base y.1, hUV y.2⟩
  refine ⟨W.comap ⟨φ.base, φ.base.hom.continuous⟩ ⊓ V, ⟨hmW, y.2⟩, Opens.infLERight _ _, ?_⟩
  rcases hfrac with h0 | ⟨i, j, a, b, hij, hb, hrep⟩
  · refine Or.inl (funext fun q => ?_)
    obtain ⟨q, hqW, hqV⟩ := q
    have hq : s ⟨φ.base q, hUV hqV⟩ = 0 := congrFun h0 ⟨_, hqW⟩
    show veroneseFiberMap hpt q (s ⟨φ.base q, hUV hqV⟩) = 0
    rw [hq, map_zero]
  · refine Or.inr ⟨i * d, j * d, ⟨(a.1 : A), a.2.1⟩, ⟨(b.1 : A), b.2.1⟩, veronese_degree_eq hk hij,
      fun q => notMem_of_notMem_base hpt q.1 (hb ⟨_, q.2.1⟩), fun q => ?_⟩
    obtain ⟨q, hqW, hqV⟩ := q
    have hq : s ⟨φ.base q, hUV hqV⟩ = Localization.mk a.1 ⟨b.1, hb ⟨_, hqW⟩⟩ := hrep ⟨_, hqW⟩
    show veroneseFiberMap hpt q (s ⟨φ.base q, hUV hqV⟩) = _
    rw [hq]
    exact veroneseFiberMap_mk hpt q a.1 ⟨b.1, hb ⟨_, hqW⟩⟩

/-- `ψ : Proj 𝒜^{(d)} ⟶ Proj 𝒜` is **compatible with the fibre maps on structure-sheaf sections** relative to
`φ` (with `ψ ∘ φ = id` on points): for `W ⊆ Proj 𝒜` open, `r ∈ Γ(Proj 𝒜, W)` and `𝔭 ∈ W`,
`localRingHom (φ 𝔭) 𝔭 ι ((ψ^# r)(φ 𝔭)) = r(𝔭)` in the ordinary localization `A_𝔭`
(sections of the structure sheaf are functions `𝔮 ↦ r(𝔮) ∈ B_{(𝔮)}`, compared through `HomogeneousLocalization.val`).
(For `φ = veroneseHom`, `ψ = (veroneseIso).hom` this is derived from `veroneseHom_app_val_apply`, `VeroneseTwistPullbackVeroneseHomApp`.) -/
def IsVeroneseSectionCompatible
    (φ : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒜 d))
    (ψ : AlgebraicGeometry.Proj (veroneseGrading 𝒜 d) ⟶ AlgebraicGeometry.Proj 𝒜)
    (hφψ : ∀ x : AlgebraicGeometry.Proj 𝒜, ψ.base (φ.base x) = x) (hpt : IsVeroneseContraction 𝒜 d φ) : Prop :=
  ∀ (W : (AlgebraicGeometry.Proj 𝒜).Opens) (r : Γ(AlgebraicGeometry.Proj 𝒜, W)) (x : W),
    veroneseFiberMap hpt x.1
      (((show (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒜 d)).1.obj (op (ψ ⁻¹ᵁ W)) from
        ψ.app W r).1 ⟨φ.base x.1, show ψ.base (φ.base x.1) ∈ W by rw [hφψ]; exact x.2⟩).val) =
    ((show (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op W) from r).1 x).val

section hom

variable {φ : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)}
    {ψ : AlgebraicGeometry.Proj (veroneseGrading 𝒜 d) ⟶ AlgebraicGeometry.Proj 𝒜}
    (hφψ : ∀ x : AlgebraicGeometry.Proj 𝒜, ψ.base (φ.base x) = x) (hpt : IsVeroneseContraction 𝒜 d φ)
    (happ : IsVeroneseSectionCompatible φ ψ hφψ hpt)

include hφψ in
/-- `W ⊆ φ⁻¹ (ψ⁻¹ W)` when `ψ ∘ φ = id` on points. -/
theorem subset_preimage_preimage (W : (AlgebraicGeometry.Proj 𝒜).Opens) :
    W.1 ⊆ φ.base ⁻¹' (ψ ⁻¹ᵁ W : (AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)).Opens).1 := by
  intro x hx
  change ψ.base (φ.base x) ∈ W
  rw [hφψ]
  exact hx

include hφψ hpt happ in
/-- **The degree-rescaling comparison morphism** `ψ_* O_{Proj 𝒜^{(d)}}(n) ⟶ O_{Proj 𝒜}(k)`, `k = n * d`:
on sections, `s ↦ (𝔭 ↦ localRingHom (s (φ 𝔭)))`. -/
def veroneseTwistHom (n k : ℤ) (hk : k = n * d) :
    (AlgebraicGeometry.Scheme.Modules.pushforward ψ).obj (AlgebraicGeometry.Proj.twist (veroneseGrading 𝒜 d) n) ⟶
      AlgebraicGeometry.Proj.twist 𝒜 k where
  val :=
    { app W := ModuleCat.ofHom
        (X := ((AlgebraicGeometry.Scheme.Modules.pushforward ψ).obj
          (AlgebraicGeometry.Proj.twist (veroneseGrading 𝒜 d) n)).val.obj W)
        (Y := (AlgebraicGeometry.Proj.twist 𝒜 k).val.obj W)
        { toFun s := (⟨veroneseComapFun hpt (ψ ⁻¹ᵁ W.unop) W.unop (subset_preimage_preimage hφψ W.unop)
              (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (veroneseGrading 𝒜 d) n
                (ψ ⁻¹ᵁ W.unop) from s).1,
              veroneseComapFun_isLocallyFraction hpt n k hk (ψ ⁻¹ᵁ W.unop) W.unop
                (subset_preimage_preimage hφψ W.unop) _
                (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (veroneseGrading 𝒜 d) n
                  (ψ ⁻¹ᵁ W.unop) from s).2⟩ :
            MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 k W.unop)
          map_add' := fun a b ↦ Subtype.ext (funext fun y ↦ map_add _ _ _)
          map_smul' := fun r a ↦ Subtype.ext (funext fun y ↦ by
            refine (map_mul _ _ _).trans ?_
            exact congrArg₂ (· * ·) (happ W.unop r y) rfl) }
      naturality := fun _ ↦ rfl }

/-- The pointwise formula for `veroneseTwistHom` (definitional). -/
theorem veroneseTwistHom_app_apply (n k : ℤ) (hk : k = n * d) (W : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (veroneseGrading 𝒜 d) n (ψ ⁻¹ᵁ W)) (y : W) :
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 k W from
      ((veroneseTwistHom hφψ hpt happ n k hk).app W).hom s).1 y =
      veroneseFiberMap hpt y.1 (s.1 ⟨φ.base y.1, subset_preimage_preimage hφψ W y.2⟩) :=
  rfl

end hom

/-- Homogeneous-component trick: if `u * c = 0` with `c` homogeneous and `u ∉ 𝔭` (`𝔭` a homogeneous prime), then some
homogeneous component `v` of `u` satisfies `v ∉ 𝔭` and `v * c = 0`. -/
theorem exists_homogeneous_notMem_mul_eq_zero (x : ProjectiveSpectrum 𝒜) {c : A} {i : ℕ} (hc : c ∈ 𝒜 i)
    {u : A} (hu : u ∉ x.asHomogeneousIdeal) (huc : u * c = 0) :
    ∃ (j : ℕ) (v : A), v ∈ 𝒜 j ∧ v ∉ x.asHomogeneousIdeal ∧ v * c = 0 := by
  have hne : ¬ ∀ j, (DirectSum.decompose 𝒜 u j : A) ∈ x.asHomogeneousIdeal.toIdeal := fun h =>
    hu ((x.asHomogeneousIdeal.isHomogeneous.mem_iff).mpr h)
  push_neg at hne
  obtain ⟨j, hj⟩ := hne
  refine ⟨j, DirectSum.decompose 𝒜 u j, (DirectSum.decompose 𝒜 u j).2, hj, ?_⟩
  have h1 : (DirectSum.decompose 𝒜 (u * c) (j + i) : A) = DirectSum.decompose 𝒜 u (j + i - i) * c :=
    DirectSum.coe_decompose_mul_of_right_mem_of_le 𝒜 hc (Nat.le_add_left i j)
  rw [huc, Nat.add_sub_cancel] at h1
  simpa using h1.symm

/-- **Injectivity of the fibre map on homogeneous fractions**: if `c ∈ B` is homogeneous (as an element of `A`) and
`c/t ↦ 0` in `A_𝔭`, then `c/t = 0` in `B_{φ 𝔭}` (`u c = 0` for some `u ∉ 𝔭`; a homogeneous component `v ∉ 𝔭` of `u`
kills `c`; `v^d ∈ B ∖ φ 𝔭`). -/
theorem veroneseFiberMap_mk_eq_zero {φ : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)}
    (hpt : IsVeroneseContraction 𝒜 d φ) (hd : 0 < d) (x : AlgebraicGeometry.Proj 𝒜) {i : ℕ}
    (c : veroneseSubring 𝒜 d) (hc : (c : A) ∈ 𝒜 i) (t : (φ.base x).asHomogeneousIdeal.toIdeal.primeCompl)
    (h : veroneseFiberMap hpt x (Localization.mk c t) = 0) : Localization.mk c t = 0 := by
  rw [veroneseFiberMap_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at h
  obtain ⟨u, hu⟩ := h
  obtain ⟨j, v, hv, hvx, hvc⟩ := exists_homogeneous_notMem_mul_eq_zero x hc u.2 hu
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨⟨v ^ d, (veronese_pow_mem 𝒜 d hd hv).1⟩, fun hmem => hvx ?_⟩, Subtype.ext ?_⟩
  · have hmem' : (⟨v ^ d, (veronese_pow_mem 𝒜 d hd hv).1⟩ : veroneseSubring 𝒜 d) ∈
        (φ.base x).asHomogeneousIdeal.toIdeal := hmem
    rw [hpt x, Ideal.mem_comap] at hmem'
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance d hmem'
  · have hvd : v ^ d = v ^ (d - 1) * v := by rw [← pow_succ, Nat.sub_add_cancel hd]
    change v ^ d * (c : A) = 0
    rw [hvd, mul_assoc, hvc, mul_zero]

/-- The value of a section of `O_{Proj B}(n)` at a point, if it is not zero there, is a homogeneous fraction
`mk a b` with `a ∈ B_i` (from `locallyFraction`). -/
theorem exists_mk_of_locallyFraction {V : Opens (ProjectiveSpectrum.top (veroneseGrading 𝒜 d))} (n : ℤ)
    (s : ∀ x : V, MiyaokaMori.WeightedJets.ProjTwisting.Fiber (veroneseGrading 𝒜 d) x.1)
    (hs : (MiyaokaMori.WeightedJets.ProjTwisting.locallyFraction (veroneseGrading 𝒜 d) n).pred s) (q : V) :
    s q = 0 ∨ ∃ (i : ℕ) (a : veroneseGrading 𝒜 d i) (b : veroneseSubring 𝒜 d)
      (hb : b ∉ q.1.asHomogeneousIdeal), s q = Localization.mk a.1 ⟨b, hb⟩ := by
  obtain ⟨V', hqV', iV', hfrac⟩ := hs q
  rcases hfrac with h0 | ⟨i, j, a, b, _, hb, hrep⟩
  · exact Or.inl (congrFun h0 ⟨q.1, hqV'⟩)
  · exact Or.inr ⟨i, a, b.1, hb ⟨q.1, hqV'⟩, hrep ⟨q.1, hqV'⟩⟩


/-! ### Surjectivity: point-free fibre maps and pointwise homogeneous fractions

For the surjectivity leaf we need the fibre map `B_𝔮 → A_𝔭` for a point `𝔮 ∈ Proj B` which is only known to be
`φ (ψ 𝔮)` (equal to `𝔮` by `hψφ`), so we state it for an arbitrary pair `(𝔮, 𝔭)` with `𝔮 = ι⁻¹ 𝔭` as ideals
(`fiberMapAt`), which avoids transporting elements of localizations along equalities of points. -/

section pointwise

variable (𝒜)

/-- `z ∈ A_𝔭` is **a homogeneous fraction of degree `n` at the point `𝔭`**: `z = 0` or `z = a/b` with `a ∈ 𝒜_i`,
`b ∈ 𝒜_j`, `b ∉ 𝔭`, `i = j + n` (the pointwise version of `ProjTwisting.IsFraction`). -/
def IsPointFraction (n : ℤ) (x : ProjectiveSpectrum 𝒜) (z : MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 x) :
    Prop :=
  z = 0 ∨ ∃ (i j : ℕ) (a : 𝒜 i) (b : 𝒜 j), (i : ℤ) = j + n ∧
    ∃ hb : b.1 ∉ x.asHomogeneousIdeal, z = Localization.mk a.1 ⟨b.1, hb⟩

/-- A section that is locally a fraction of degree `n` is a homogeneous fraction of degree `n` at every point. -/
theorem isPointFraction_of_locallyFraction {V : Opens (ProjectiveSpectrum.top 𝒜)} (n : ℤ)
    (s : ∀ x : V, MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 x.1)
    (hs : (MiyaokaMori.WeightedJets.ProjTwisting.locallyFraction 𝒜 n).pred s) (q : V) :
    IsPointFraction 𝒜 n q.1 (s q) := by
  obtain ⟨V', hqV', iV', hfrac⟩ := hs q
  rcases hfrac with h0 | ⟨i, j, a, b, hij, hb, hrep⟩
  · exact Or.inl (congrFun h0 ⟨q.1, hqV'⟩)
  · exact Or.inr ⟨i, j, a, b, hij, hb ⟨q.1, hqV'⟩, hrep ⟨q.1, hqV'⟩⟩

end pointwise

/-- The fibre map `B_𝔮 → A_𝔭`, `b/t ↦ b/t`, for any pair of points with `𝔮 = ι⁻¹ 𝔭` as ideals
(`veroneseFiberMap hpt x` is the case `𝔮 = φ x`, `𝔭 = x`, definitionally). -/
def fiberMapAt (q : ProjectiveSpectrum (veroneseGrading 𝒜 d)) (p : ProjectiveSpectrum 𝒜)
    (h : q.asHomogeneousIdeal.toIdeal = Ideal.comap (veroneseSubringHom 𝒜 d) p.asHomogeneousIdeal.toIdeal) :
    MiyaokaMori.WeightedJets.ProjTwisting.Fiber (veroneseGrading 𝒜 d) q →+*
      MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 p :=
  Localization.localRingHom q.asHomogeneousIdeal.toIdeal p.asHomogeneousIdeal.toIdeal (veroneseSubringHom 𝒜 d) h

/-- `t ∈ B ∖ 𝔮` is, as an element of `A`, not in `𝔭` (when `𝔮 = ι⁻¹ 𝔭`). -/
theorem notMem_of_notMem_of_eq_comap {q : ProjectiveSpectrum (veroneseGrading 𝒜 d)} {p : ProjectiveSpectrum 𝒜}
    (h : q.asHomogeneousIdeal.toIdeal = Ideal.comap (veroneseSubringHom 𝒜 d) p.asHomogeneousIdeal.toIdeal)
    {t : veroneseSubring 𝒜 d} (ht : t ∉ q.asHomogeneousIdeal) : (t : A) ∉ p.asHomogeneousIdeal := by
  intro h'
  apply ht
  change t ∈ q.asHomogeneousIdeal.toIdeal
  rw [h, Ideal.mem_comap]
  exact h'

theorem fiberMapAt_mk (q : ProjectiveSpectrum (veroneseGrading 𝒜 d)) (p : ProjectiveSpectrum 𝒜)
    (h : q.asHomogeneousIdeal.toIdeal = Ideal.comap (veroneseSubringHom 𝒜 d) p.asHomogeneousIdeal.toIdeal)
    (b : veroneseSubring 𝒜 d) (t : q.asHomogeneousIdeal.toIdeal.primeCompl) :
    fiberMapAt q p h (Localization.mk b t) =
      Localization.mk (b : A) ⟨(t : veroneseSubring 𝒜 d), notMem_of_notMem_of_eq_comap h t.2⟩ :=
  Localization.localRingHom_mk _ _ _ _ _ _

/-- **Injectivity of the fibre map on homogeneous fractions** (point-free version of `veroneseFiberMap_mk_eq_zero`):
if `c ∈ B` is homogeneous as an element of `A` and `c/t ↦ 0` in `A_𝔭`, then `c/t = 0` in `B_𝔮`. Proof: `u c = 0` for
some `u ∉ 𝔭`; a homogeneous component `v ∉ 𝔭` of `u` kills `c` (`exists_homogeneous_notMem_mul_eq_zero`); `v^d ∈ B ∖ 𝔮`. -/
theorem fiberMapAt_mk_eq_zero (hd : 0 < d) (q : ProjectiveSpectrum (veroneseGrading 𝒜 d))
    (p : ProjectiveSpectrum 𝒜)
    (h : q.asHomogeneousIdeal.toIdeal = Ideal.comap (veroneseSubringHom 𝒜 d) p.asHomogeneousIdeal.toIdeal)
    {i : ℕ} (c : veroneseSubring 𝒜 d) (hc : (c : A) ∈ 𝒜 i) (t : q.asHomogeneousIdeal.toIdeal.primeCompl)
    (h0 : fiberMapAt q p h (Localization.mk c t) = 0) : Localization.mk c t = 0 := by
  rw [fiberMapAt_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at h0
  obtain ⟨u, hu⟩ := h0
  obtain ⟨j, v, hv, hvx, hvc⟩ := exists_homogeneous_notMem_mul_eq_zero p hc u.2 hu
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨⟨v ^ d, (veronese_pow_mem 𝒜 d hd hv).1⟩, fun hmem => hvx ?_⟩, Subtype.ext ?_⟩
  · have hmem' : (⟨v ^ d, (veronese_pow_mem 𝒜 d hd hv).1⟩ : veroneseSubring 𝒜 d) ∈
        q.asHomogeneousIdeal.toIdeal := hmem
    rw [h, Ideal.mem_comap] at hmem'
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance d hmem'
  · have hvd : v ^ d = v ^ (d - 1) * v := by rw [← pow_succ, Nat.sub_add_cancel hd]
    change v ^ d * (c : A) = 0
    rw [hvd, mul_assoc, hvc, mul_zero]

/-- **Uniqueness of the homogeneous preimage**: two homogeneous fractions of degree `n` at `𝔮` with the same image in
`A_𝔭` are equal (their difference is a fraction with homogeneous numerator, `Localization.sub_mk`, killed by
`fiberMapAt_mk_eq_zero`). -/
theorem isPointFraction_unique (hd : 0 < d) (q : ProjectiveSpectrum (veroneseGrading 𝒜 d))
    (p : ProjectiveSpectrum 𝒜)
    (h : q.asHomogeneousIdeal.toIdeal = Ideal.comap (veroneseSubringHom 𝒜 d) p.asHomogeneousIdeal.toIdeal)
    (n : ℤ) {z z' : MiyaokaMori.WeightedJets.ProjTwisting.Fiber (veroneseGrading 𝒜 d) q}
    (hz : IsPointFraction (veroneseGrading 𝒜 d) n q z) (hz' : IsPointFraction (veroneseGrading 𝒜 d) n q z')
    (heq : fiberMapAt q p h z = fiberMapAt q p h z') : z = z' := by
  have hsub : ∃ (i : ℕ) (c : veroneseSubring 𝒜 d) (t : q.asHomogeneousIdeal.toIdeal.primeCompl),
      (c : A) ∈ 𝒜 i ∧ z - z' = Localization.mk c t := by
    rcases hz with rfl | ⟨i, j, a, b, hij, hb, rfl⟩ <;> rcases hz' with rfl | ⟨i', j', a', b', hij', hb', rfl⟩
    · exact ⟨0, 0, 1, zero_mem _, by rw [sub_zero, Localization.mk_zero]⟩
    · exact ⟨i' * d, -a'.1, ⟨b'.1, hb'⟩, neg_mem a'.2.1, by rw [zero_sub, Localization.neg_mk]⟩
    · exact ⟨i * d, a.1, ⟨b.1, hb⟩, a.2.1, by rw [sub_zero]⟩
    · refine ⟨(j' + i) * d, _, _, ?_, Localization.sub_mk _ _ _ _⟩
      have e1 : j' * d + i * d = (j' + i) * d := (Nat.add_mul _ _ _).symm
      have e2 : j * d + i' * d = (j' + i) * d := by
        have : j + i' = j' + i := by omega
        rw [← Nat.add_mul, this]
      have h1 := SetLike.mul_mem_graded b'.2.1 a.2.1
      have h2 := SetLike.mul_mem_graded b.2.1 a'.2.1
      rw [e1] at h1
      rw [e2] at h2
      exact sub_mem h1 h2
  obtain ⟨i, c, t, hc, hzz'⟩ := hsub
  rw [← sub_eq_zero, hzz']
  apply fiberMapAt_mk_eq_zero hd q p h c hc t
  rw [← hzz', map_sub, heq, sub_self]

/-- **Degree bookkeeping for the lift** `a/b = (a b^{d-1}) / b^d`: for `a ∈ 𝒜_i`, `b ∈ 𝒜_j`, `i = j + k`, `k = n d`,
there are `a' ∈ B_m` (`a' = a b^{d-1}`, `m = j + n ≥ 0`) and `b' ∈ B_j` (`b' = b^d`) with `a' b = a b'`. -/
theorem exists_veronese_lift (hd : 0 < d) {n k : ℤ} (hk : k = n * d) {i j : ℕ} (a : 𝒜 i) (b : 𝒜 j)
    (hij : (i : ℤ) = j + k) :
    ∃ (m : ℕ) (a' : veroneseGrading 𝒜 d m) (b' : veroneseGrading 𝒜 d j), (m : ℤ) = j + n ∧
      ((b'.1 : veroneseSubring 𝒜 d) : A) = b.1 ^ d ∧
      ((a'.1 : veroneseSubring 𝒜 d) : A) * b.1 = a.1 * ((b'.1 : veroneseSubring 𝒜 d) : A) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hjn : (0 : ℤ) ≤ j + n := by
    rcases le_or_gt 0 n with hn | hn
    · omega
    · have h1 : n * ((e + 1 : ℕ) : ℤ) ≤ n * 1 :=
        mul_le_mul_of_nonpos_left (by push_cast; omega) hn.le
      have h2 : (0 : ℤ) ≤ i := by positivity
      linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = j + n := ⟨(j + n).toNat, Int.toNat_of_nonneg hjn⟩
  have hmem : a.1 * b.1 ^ e ∈ 𝒜 (m * (e + 1)) := by
    have h := SetLike.mul_mem_graded a.2 (SetLike.pow_mem_graded e b.2)
    have hdeg : i + e • j = m * (e + 1) := by
      have : ((i : ℤ) + e * j = m * (e + 1)) := by rw [hij, hk, hm]; push_cast; ring
      rw [smul_eq_mul]
      exact_mod_cast this
    rwa [hdeg] at h
  obtain ⟨hsub, hsub', hgr⟩ := veronese_pow_mem 𝒜 (e + 1) hd b.2
  refine ⟨m, ⟨⟨a.1 * b.1 ^ e, veroneseSubring.mem_of_mem_graded 𝒜 (e + 1) (dvd_mul_left _ _) hmem⟩, hmem,
    fun h0 => absurd h0 (Nat.succ_ne_zero e)⟩, ⟨⟨b.1 ^ (e + 1), hsub'⟩, hgr⟩, hm, rfl, ?_⟩
  show a.1 * b.1 ^ e * b.1 = a.1 * b.1 ^ (e + 1)
  rw [pow_succ, mul_assoc]

/-- If `b' = b^d` in `A` and `b ∉ 𝔭`, then `b' ∉ 𝔮` (`𝔮 = ι⁻¹ 𝔭`). -/
theorem notMem_of_coe_eq_pow {q : ProjectiveSpectrum (veroneseGrading 𝒜 d)} {p : ProjectiveSpectrum 𝒜}
    (h : q.asHomogeneousIdeal.toIdeal = Ideal.comap (veroneseSubringHom 𝒜 d) p.asHomogeneousIdeal.toIdeal)
    {b : A} {b' : veroneseSubring 𝒜 d} (hb'd : (b' : A) = b ^ d) (hb : b ∉ p.asHomogeneousIdeal) :
    b' ∉ q.asHomogeneousIdeal := by
  intro hmem
  have hmem' : b' ∈ q.asHomogeneousIdeal.toIdeal := hmem
  rw [h, Ideal.mem_comap] at hmem'
  change (b' : A) ∈ p.asHomogeneousIdeal.toIdeal at hmem'
  rw [hb'd] at hmem'
  exact hb (Ideal.IsPrime.mem_of_pow_mem inferInstance d hmem')

/-- `fiberMapAt (a'/b') = a/b` whenever `a' b = a b'` in `A`. -/
theorem fiberMapAt_mk_eq (q : ProjectiveSpectrum (veroneseGrading 𝒜 d)) (p : ProjectiveSpectrum 𝒜)
    (h : q.asHomogeneousIdeal.toIdeal = Ideal.comap (veroneseSubringHom 𝒜 d) p.asHomogeneousIdeal.toIdeal)
    {a b : A} {a' b' : veroneseSubring 𝒜 d} (hb : b ∉ p.asHomogeneousIdeal) (hb' : b' ∉ q.asHomogeneousIdeal)
    (hrel : (a' : A) * b = a * (b' : A)) :
    fiberMapAt q p h (Localization.mk a' ⟨b', hb'⟩) = Localization.mk a ⟨b, hb⟩ := by
  rw [fiberMapAt_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq]
  show algebraMap A _ (b * (a' : A)) = algebraMap A _ ((b' : A) * a)
  congr 1
  rw [mul_comm, hrel, mul_comm]

/-- **Existence of the homogeneous preimage**: every homogeneous fraction of degree `k = n d` at `𝔭` is the image of a
homogeneous fraction of degree `n` at `𝔮` (`a/b = (a b^{d-1})/b^d`). -/
theorem exists_isPointFraction_lift (hd : 0 < d) (q : ProjectiveSpectrum (veroneseGrading 𝒜 d))
    (p : ProjectiveSpectrum 𝒜)
    (h : q.asHomogeneousIdeal.toIdeal = Ideal.comap (veroneseSubringHom 𝒜 d) p.asHomogeneousIdeal.toIdeal)
    {n k : ℤ} (hk : k = n * d) {w : MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 p}
    (hw : IsPointFraction 𝒜 k p w) :
    ∃ z : MiyaokaMori.WeightedJets.ProjTwisting.Fiber (veroneseGrading 𝒜 d) q,
      IsPointFraction (veroneseGrading 𝒜 d) n q z ∧ fiberMapAt q p h z = w := by
  rcases hw with rfl | ⟨i, j, a, b, hij, hb, rfl⟩
  · exact ⟨0, Or.inl rfl, map_zero _⟩
  · obtain ⟨m, a', b', hm, hb'd, hab'⟩ := exists_veronese_lift hd hk a b hij
    have hb' : b'.1 ∉ q.asHomogeneousIdeal := notMem_of_coe_eq_pow h hb'd hb
    exact ⟨Localization.mk a'.1 ⟨b'.1, hb'⟩, Or.inr ⟨m, j, a', b', hm, hb', rfl⟩, fiberMapAt_mk_eq q p h hb hb' hab'⟩

/-- Transport of the defining identity of the lift along an equality of points `𝔭 = 𝔭'` (both with the same `𝔮`). -/
theorem fiberMapAt_congr_point {q : ProjectiveSpectrum (veroneseGrading 𝒜 d)} {p p' : ProjectiveSpectrum 𝒜}
    (e : p = p')
    (h : q.asHomogeneousIdeal.toIdeal = Ideal.comap (veroneseSubringHom 𝒜 d) p.asHomogeneousIdeal.toIdeal)
    (h' : q.asHomogeneousIdeal.toIdeal = Ideal.comap (veroneseSubringHom 𝒜 d) p'.asHomogeneousIdeal.toIdeal)
    (z : MiyaokaMori.WeightedJets.ProjTwisting.Fiber (veroneseGrading 𝒜 d) q) {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hp : p ∈ W) (hp' : p' ∈ W) (σ : ∀ x : W, MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 x.1)
    (hz : fiberMapAt q p h z = σ ⟨p, hp⟩) : fiberMapAt q p' h' z = σ ⟨p', hp'⟩ := by
  subst e
  exact hz

section hom

variable {φ : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)}
    {ψ : AlgebraicGeometry.Proj (veroneseGrading 𝒜 d) ⟶ AlgebraicGeometry.Proj 𝒜}
    (hφψ : ∀ x : AlgebraicGeometry.Proj 𝒜, ψ.base (φ.base x) = x) (hpt : IsVeroneseContraction 𝒜 d φ)
    (happ : IsVeroneseSectionCompatible φ ψ hφψ hpt)

include hφψ hpt happ in
/-- A section of `ψ_* O_B(n)` over `W` whose image under the comparison morphism is `0` vanishes at every point
`φ p` (`p ∈ W`). -/
theorem veroneseTwistHom_apply_eq_zero_at (hd : 0 < d) (n k : ℤ) (hk : k = n * d) (W : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (veroneseGrading 𝒜 d) n (ψ ⁻¹ᵁ W))
    (h0 : ((veroneseTwistHom hφψ hpt happ n k hk).app W).hom s = 0) (p : W) :
    s.1 ⟨φ.base p.1, subset_preimage_preimage hφψ W p.2⟩ = 0 := by
  have hv : veroneseFiberMap hpt p.1 (s.1 ⟨φ.base p.1, subset_preimage_preimage hφψ W p.2⟩) = 0 := by
    have := congrArg (fun t : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 k W => t.1 p) h0
    exact this
  rcases exists_mk_of_locallyFraction n s.1 s.2 ⟨φ.base p.1, subset_preimage_preimage hφψ W p.2⟩ with hz | ⟨i, a, b, hb, hab⟩
  · exact hz
  · rw [hab] at hv ⊢
    exact veroneseFiberMap_mk_eq_zero hpt hd p.1 a.1 a.2.1 ⟨b, hb⟩ hv

include hφψ hpt happ in
/-- **Injectivity** of the comparison morphism on sections (given `φ ∘ ψ = id` on points): a section with image `0`
vanishes at every `q = φ (ψ q)` by `veroneseTwistHom_apply_eq_zero_at`. -/
theorem veroneseTwistHom_app_injective (hψφ : ∀ y : AlgebraicGeometry.Proj (veroneseGrading 𝒜 d), φ.base (ψ.base y) = y)
    (hd : 0 < d) (n k : ℤ) (hk : k = n * d) (W : (AlgebraicGeometry.Proj 𝒜).Opens) :
    Function.Injective ((veroneseTwistHom hφψ hpt happ n k hk).app W) := by
  intro s s' hss'
  have h0 : ((veroneseTwistHom hφψ hpt happ n k hk).app W).hom (s - s') = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hss'
  rw [← sub_eq_zero]
  refine Subtype.ext (funext fun q => ?_)
  obtain ⟨q, hq⟩ := q
  have hp : ψ.base q ∈ W := hq
  have := veroneseTwistHom_apply_eq_zero_at hφψ hpt happ hd n k hk W (s - s') h0 ⟨ψ.base q, hp⟩
  have e : (⟨φ.base (ψ.base q), subset_preimage_preimage hφψ W hp⟩ :
      (ψ ⁻¹ᵁ W : (AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)).Opens)) = ⟨q, hq⟩ :=
    Subtype.ext (hψφ q)
  rw [e] at this
  exact this

include hpt in
/-- For `𝔮 ∈ Proj B`, `𝔮 = ι⁻¹ (ψ 𝔮)` as ideals (from `hpt` at `ψ 𝔮` and `φ (ψ 𝔮) = 𝔮`). -/
theorem toIdeal_eq_comap_of_section (hψφ : ∀ y : AlgebraicGeometry.Proj (veroneseGrading 𝒜 d), φ.base (ψ.base y) = y)
    (q : AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)) :
    q.asHomogeneousIdeal.toIdeal =
      Ideal.comap (veroneseSubringHom 𝒜 d) (ψ.base q).asHomogeneousIdeal.toIdeal := by
  have := hpt (ψ.base q)
  rwa [hψφ q] at this

include hpt in
/-- A pointwise homogeneous lift of a section `σ` of `O_𝒜(k)` over `W` is **locally a fraction** of degree `n` on
`ψ⁻¹ W`: on `ψ⁻¹ V` (`V ⊆ W` where `σ = a/b`), the lift equals `(a b^{d-1})/b^d` by uniqueness
(`isPointFraction_unique`); where `σ = 0` it is `0`. -/
theorem locallyFraction_of_pointwise_lift
    (hψφ : ∀ y : AlgebraicGeometry.Proj (veroneseGrading 𝒜 d), φ.base (ψ.base y) = y) (hd : 0 < d) (n k : ℤ)
    (hk : k = n * d) (W : (AlgebraicGeometry.Proj 𝒜).Opens)
    (σ : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 k W)
    (s : ∀ q : (ψ ⁻¹ᵁ W : (AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)).Opens),
      MiyaokaMori.WeightedJets.ProjTwisting.Fiber (veroneseGrading 𝒜 d) q.1)
    (hs1 : ∀ q, IsPointFraction (veroneseGrading 𝒜 d) n q.1 (s q))
    (hs2 : ∀ q, fiberMapAt q.1 (ψ.base q.1) (toIdeal_eq_comap_of_section hpt hψφ q.1) (s q) =
      σ.1 ⟨ψ.base q.1, q.2⟩) :
    (MiyaokaMori.WeightedJets.ProjTwisting.locallyFraction (veroneseGrading 𝒜 d) n).pred s := by
  intro q
  obtain ⟨V, hpV, iVW, hfrac⟩ := σ.2 ⟨ψ.base q.1, q.2⟩
  refine ⟨ψ ⁻¹ᵁ V, hpV, homOfLE fun r hr => iVW.le hr, ?_⟩
  rcases hfrac with h0 | ⟨i, j, a, b, hij, hb, hrep⟩
  · refine Or.inl (funext fun r => ?_)
    refine isPointFraction_unique hd _ _ (toIdeal_eq_comap_of_section hpt hψφ _) n (hs1 _) (Or.inl rfl) ?_
    rw [hs2, Pi.zero_apply, map_zero]
    exact congrFun h0 ⟨ψ.base r.1, r.2⟩
  · obtain ⟨m, a', b', hm, hb'd, hab'⟩ := exists_veronese_lift hd hk a b hij
    refine Or.inr ⟨m, j, a', b', hm, fun r =>
      notMem_of_coe_eq_pow (toIdeal_eq_comap_of_section hpt hψφ r.1) hb'd (hb ⟨ψ.base r.1, r.2⟩), fun r => ?_⟩
    refine isPointFraction_unique hd _ _ (toIdeal_eq_comap_of_section hpt hψφ _) n (hs1 _)
      (Or.inr ⟨m, j, a', b', hm, _, rfl⟩) ?_
    rw [hs2]
    exact ((fiberMapAt_mk_eq _ _ _ (hb ⟨ψ.base r.1, r.2⟩) _ hab').trans
      (hrep ⟨ψ.base r.1, r.2⟩).symm).symm

/-- **Surjectivity of the comparison morphism.** The comparison morphism is surjective on the
sections over every open `W ⊆ Proj 𝒜`, provided `φ` and `ψ` are mutually inverse on points (so `φ` is a
homeomorphism `Proj 𝒜 ≃ₜ Proj 𝒜^{(d)}`, `ψ⁻¹ W = φ(W)`).

Source: Stacks 0B5J (lemma-d-uple), the identification `O_{Proj S}(nd) ↔ O_{Proj S^{(d)}}(n)`; self-contained proof below.

Proof. Write `B := 𝒜^{(d)}`, `ι : B → A`, and for `𝔭 ∈ W` put `𝔮 := φ 𝔭` (so `𝔮 = ι⁻¹ 𝔭`, `hpt`); the fibre map is
`F_𝔭 := veroneseFiberMap hpt 𝔭 : B_𝔮 → A_𝔭`, `b/t ↦ b/t`. Let `σ` be a section of `O_𝒜(k)` over `W`, locally `a/t` with
`a ∈ 𝒜_{j+k}`, `t ∈ 𝒜_j`, `t ∉ 𝔭`. Define `s : ψ⁻¹W → ⨆ B_𝔮` by `s 𝔮 := ` the unique `z ∈ B_𝔮` with
`F_{ψ 𝔮} z = σ (ψ 𝔮)` that is a homogeneous fraction of degree `n` (exists: `a/t = (a t^{d-1})/t^d`,
`a t^{d-1} ∈ 𝒜_{(j+n)d} = B_{j+n}`, `t^d ∈ B_j`, `t^d ∉ 𝔮`; unique by `veroneseFiberMap_mk_eq_zero` applied to the
difference of two such fractions, which is again a fraction with homogeneous numerator (`Localization.sub_mk`);
formally `s 𝔮 := Classical.choose` of this existence-and-uniqueness, or the explicit formula from a chosen local
representation, checked independent of the representation by the uniqueness). Then `s` is locally a fraction of degree `n`:
on the image `φ(V)` of a neighbourhood `V ⊆ W` where `σ = a/t`, which is open because `φ` is a homeomorphism (inverse
`ψ`: `hφψ`, `hψφ`; continuity of both — Mathlib `Homeomorph.mk`, `Homeomorph.isOpen_image`), `s = (a t^{d-1})/t^d`
(`IsFraction` with `i := (j+k), j := j·d` transported by `veronese_degree_eq`). The zero-section branch of `IsFraction`
gives `s = 0` there. And `F_𝔭 (s (φ 𝔭)) = σ 𝔭` by construction, i.e. the image of `s` is `σ`
(`veroneseTwistHom_app_apply`, `Subtype.ext`, `funext`).

Edge cases: `W = ∅` — both sides are singletons; `Proj 𝒜 = ∅` — everything is empty; `d = 1` — `B = 𝒜` with relabelled
pieces, the map is the identity on values; `n < 0` allowed (fractions with `deg numerator < deg denominator`);
the zero section is represented by the `s = 0` branch of `IsFraction`, which maps to `0`.

Formalization: (i) the pointwise inverse is `choose` on
`exists_isPointFraction_lift` (existence, via `exists_veronese_lift` for `a/b = (a b^{d-1})/b^d`), unique by
`isPointFraction_unique` (`Localization.sub_mk` + `fiberMapAt_mk_eq_zero`); (ii) "locally a fraction" is
`locallyFraction_of_pointwise_lift`, on the open `ψ⁻¹ V` (no `Homeomorph` is needed: `ψ⁻¹ V = φ(V)` is open because
`ψ` is continuous); (iii) the fibre maps are stated point-free (`fiberMapAt`, for any `𝔮 = ι⁻¹ 𝔭`), so that no
transport of localization elements along `φ (ψ 𝔮) = 𝔮` is needed — only the trivial `fiberMapAt_congr_point`. -/
theorem veroneseTwistHom_app_surjective (hψφ : ∀ y : AlgebraicGeometry.Proj (veroneseGrading 𝒜 d), φ.base (ψ.base y) = y)
    (hd : 0 < d) (n k : ℤ) (hk : k = n * d) (W : (AlgebraicGeometry.Proj 𝒜).Opens) :
    Function.Surjective ((veroneseTwistHom hφψ hpt happ n k hk).app W) := by
  intro σ
  have key : ∀ q : (ψ ⁻¹ᵁ W : (AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)).Opens),
      ∃ z : MiyaokaMori.WeightedJets.ProjTwisting.Fiber (veroneseGrading 𝒜 d) q.1,
        IsPointFraction (veroneseGrading 𝒜 d) n q.1 z ∧
        fiberMapAt q.1 (ψ.base q.1) (toIdeal_eq_comap_of_section hpt hψφ q.1) z =
          (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 k W from σ).1 ⟨ψ.base q.1, q.2⟩ :=
    fun q => exists_isPointFraction_lift hd _ _ _ hk
      (isPointFraction_of_locallyFraction 𝒜 k _
        (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 k W from σ).2 ⟨ψ.base q.1, q.2⟩)
  choose s hs1 hs2 using key
  refine ⟨(⟨s, locallyFraction_of_pointwise_lift hpt hψφ hd n k hk W _ s hs1 hs2⟩ :
    MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (veroneseGrading 𝒜 d) n (ψ ⁻¹ᵁ W)), ?_⟩
  refine Subtype.ext (funext fun y => ?_)
  show veroneseFiberMap hpt y.1 (s ⟨φ.base y.1, subset_preimage_preimage hφψ W y.2⟩) =
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 k W from σ).1 y
  exact fiberMapAt_congr_point (hφψ y.1) _ _ _ _ _ _ (hs2 ⟨φ.base y.1, subset_preimage_preimage hφψ W y.2⟩)

/-- The comparison morphism is bijective on the sections over every open (injectivity proved above, surjectivity is the
leaf `veroneseTwistHom_app_surjective`). -/
theorem veroneseTwistHom_app_bijective (hψφ : ∀ y : AlgebraicGeometry.Proj (veroneseGrading 𝒜 d), φ.base (ψ.base y) = y)
    (hd : 0 < d) (n k : ℤ) (hk : k = n * d) (W : (AlgebraicGeometry.Proj 𝒜).Opens) :
    Function.Bijective ((veroneseTwistHom hφψ hpt happ n k hk).app W) :=
  ⟨veroneseTwistHom_app_injective hφψ hpt happ hψφ hd n k hk W,
    veroneseTwistHom_app_surjective hφψ hpt happ hψφ hd n k hk W⟩

/-- The comparison morphism is an isomorphism (from `veroneseTwistHom_app_bijective`, componentwise). -/
theorem isIso_veroneseTwistHom (hψφ : ∀ y : AlgebraicGeometry.Proj (veroneseGrading 𝒜 d), φ.base (ψ.base y) = y)
    (hd : 0 < d) (n k : ℤ) (hk : k = n * d) :
    IsIso (veroneseTwistHom hφψ hpt happ n k hk) := by
  rw [AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  exact veroneseTwistHom_app_bijective hφψ hpt happ hψφ hd n k hk W

end hom

end AlgebraicGeometry.Proj

end
