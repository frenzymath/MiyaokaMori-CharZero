import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentOfAffineLocalizing
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y1
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.EmbeddedPartSubsheaf

/-! # The embedded part of a coherent sheaf is coherent

The subsheaf `K = embeddedPart F ⊆ F` of Stacks 02OL (`EmbeddedPartSubsheaf`) is coherent
(`X` locally Noetherian, `F` coherent). This is the sheaf form of Stacks 02M7 (`K(M)_f = K(M_f)`).

* `Ideal.exists_mul_pow_mem_of_mem_minimalPrimes'`: `p` minimal over `I`, `x ∈ p` ⟹ `∃ y ∉ p, ∃ n,
  y * x ^ n ∈ I`. Proof (as Mathlib's `Ideal.iUnion_minimalPrimes`): in `R_p` the only prime containing
  `I_p` is `p_p` (primes of `R_p` are primes `q ⊆ p`, and `I ≤ q ⊆ p` forces `q = p`), so
  `x/1 ∈ rad(I_p)`, `(x/1)^n = a/b` with `a ∈ I`, `b ∉ p`, i.e. `t * b * x^n = t * a ∈ I` for some `t ∉ p`.
* `primeIdealOf_mem_minimalPrimes_annihilator`: for `U` affine and `y ∈ U` a generic point of
  `Supp F`, the prime `p_y ⊆ A := Γ(U, O_X)` is a minimal prime over `Ann_A Γ(U, F)`. Proof:
  `Supp Γ(U, F) = V(Ann)` (`Module.support_eq_zeroLocus`, `Γ(U, F)` is finite by Stacks 01PB), and
  `q ∈ Supp Γ(U, F)` iff the stalk of `F` at the point `z_q` of `U` is nonzero (the stalk is the
  localization of `Γ(U, F)` at `q`, Stacks 01I8; spelled out: `F_z = 0` iff some `u ∉ q` kills
  `Γ(U, F)`); `q ≤ p_y` means `z_q ⤳ y`, so minimality of `y` in `Supp F` gives `z_q = y`, `q = p_y`.
* `exists_pow_smul_germ_eq_zero`: `y` generic, `y ∉ D(h)` ⟹ `germ_y (h^n • t) = 0` for some `n`
  (`h ∈ p_y`, so `u * h^n ∈ Ann` for some `u ∉ p_y`).
* `embeddedPart_isQuasicoherent`: by the affine-local criterion `isQuasicoherent_of_affine_localizing`
  (Stacks 01IB): (a) a section `s ∈ Γ(D(h), K)` lifts, after multiplying by a power of `h`, to
  `t ∈ Γ(U, F)` (quasi-coherence of `F`); the generic points in `U \ D(h)` are finitely many, and by
  the previous item a further power `h^N` kills the germs of `t` there, while at generic points in
  `D(h)` the germ of `t` already vanishes (it is `h^n • germ s`); so `h^N • t ∈ Γ(U, K)`.
  (b) uniqueness is inherited from `F`.
* `embeddedPart_isCoherent`: Stacks 01Y1 (`isCoherent_of_mono`).

Source: Stacks 02OL, 02M6, 02M7, 01IB, 01Y1, 00L2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open scoped AlgebraicGeometry

noncomputable section

/-- If `p` is a minimal prime over `I` and `x ∈ p`, then `y * x ^ n ∈ I` for some `y ∉ p`
(see the module docstring). -/
theorem Ideal.exists_mul_pow_mem_of_mem_minimalPrimes' {R : Type*} [CommRing R] {I p : Ideal R}
    (hp : p ∈ I.minimalPrimes) {x : R} (hx : x ∈ p) : ∃ y ∉ p, ∃ n : ℕ, y * x ^ n ∈ I := by
  obtain ⟨⟨hp₁, hp₂⟩, hp₃⟩ := hp
  have hrad : p.map (algebraMap R (Localization.AtPrime p)) ≤
      (I.map (algebraMap _ _)).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro q ⟨hq', hq⟩
    obtain ⟨h₁, h₂⟩ := ((IsLocalization.AtPrime.orderIsoOfPrime _ p) ⟨q, hq⟩).2
    rw [Ideal.map_le_iff_le_comap] at hq' ⊢
    exact hp₃ ⟨h₁, hq'⟩ h₂
  obtain ⟨n, hn⟩ := hrad (Ideal.mem_map_of_mem _ hx)
  rw [IsLocalization.mem_map_algebraMap_iff (M := p.primeCompl)] at hn
  obtain ⟨⟨a, b⟩, hn⟩ := hn
  rw [← map_pow, ← map_mul, IsLocalization.eq_iff_exists p.primeCompl] at hn
  obtain ⟨t, ht⟩ := hn
  refine ⟨t.1 * b.1, (t * b).2, n, ?_⟩
  have : t.1 * b.1 * x ^ n = t.1 * a.1 := by rw [← ht]; ring
  rw [this]
  exact I.mul_mem_left _ a.2

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- If the stalk of a coherent module at `z ∈ U` (`U` affine) vanishes, some `u` with `z ∈ D(u)`
kills all sections over `U`. -/
theorem exists_smul_eq_zero_of_subsingleton_stalk (F : X.Modules) [F.IsCoherent] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {z : X} (hz : z ∈ U)
    (h : Subsingleton (F.presheaf.stalk z)) :
    ∃ u : Γ(X, U), z ∈ X.basicOpen u ∧ ∀ m : Γ(F, U), u • m = 0 := by
  haveI : F.IsQuasicoherent := IsCoherent.quasicoherent
  haveI : F.IsFiniteType := IsCoherent.finiteType
  have hz0 : ∀ m : Γ(F, U), F.presheaf.germ U z hz m = 0 := (subsingleton_stalk_iff F hU hz).mp h
  have hfin : Module.Finite Γ(X, U) Γ(F, U) := finite_sections_of_isFiniteType F hU
  obtain ⟨s, hs⟩ := hfin.fg_top
  have hchoice : ∀ m : Γ(F, U), ∃ u : Γ(X, U), z ∈ X.basicOpen u ∧ u • m = 0 := fun m =>
    (germ_eq_zero_iff F hU hz m).mp (hz0 m)
  choose uf huf using hchoice
  classical
  refine ⟨∏ m ∈ s, uf m, ?_, ?_⟩
  · rw [X.mem_basicOpen _ z hz, map_prod]
    exact IsUnit.prod_iff.mpr fun m hm => (X.mem_basicOpen (uf m) z hz).mp (huf m).1
  · intro m
    have hm : m ∈ Submodule.span Γ(X, U) (s : Set Γ(F, U)) := by rw [hs]; trivial
    refine Submodule.span_induction (p := fun m _ => (∏ m ∈ s, uf m) • m = 0) ?_ ?_ ?_ ?_ hm
    · intro m hm
      rw [← Finset.prod_erase_mul s uf hm, mul_smul, (huf m).2, smul_zero]
    · simp
    · intro a b _ _ ha hb
      rw [smul_add, ha, hb, add_zero]
    · intro r a _ ha
      rw [smul_comm, ha, smul_zero]

/-- `z ∈ D(u)` iff `u ∉ p_z` for `z ∈ U` affine. -/
theorem mem_basicOpen_iff_notMem_primeIdealOf {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    {z : X} (hz : z ∈ U) (u : Γ(X, U)) :
    z ∈ X.basicOpen u ↔ u ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
  letI := X.presheaf.algebra_section_stalk ⟨z, hz⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hz⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hz⟩
  exact (X.mem_basicOpen u z hz).trans
    (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hz⟩).asIdeal u)

/-- For a generic point `y ∈ U` of `Supp F` (`U` affine), the prime `p_y` is a minimal prime over the
annihilator of `Γ(U, F)` (see the module docstring). -/
theorem primeIdealOf_mem_minimalPrimes_annihilator (F : X.Modules) [F.IsCoherent] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {y : X} (hy : y ∈ U) (hyg : y ∈ F.genericPoints) :
    (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∈ (Module.annihilator Γ(X, U) Γ(F, U)).minimalPrimes := by
  haveI : F.IsQuasicoherent := IsCoherent.quasicoherent
  -- a point `z ∈ U` lies in `Supp F` iff `Ann ≤ p_z`
  have key : ∀ (z : X) (hz : z ∈ U),
      z ∈ F.support ↔ Module.annihilator Γ(X, U) Γ(F, U) ≤ (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
    intro z hz
    constructor
    · intro hzs a ha
      by_contra hap
      have hzu : z ∈ X.basicOpen a := (mem_basicOpen_iff_notMem_primeIdealOf hU hz a).mpr hap
      have hsub : Subsingleton (F.presheaf.stalk z) := by
        rw [subsingleton_stalk_iff F hU hz]
        intro m
        rw [germ_eq_zero_iff F hU hz m]
        exact ⟨a, hzu, Module.mem_annihilator.mp ha m⟩
      have hnt : Nontrivial (F.presheaf.stalk z) := hzs
      exact not_subsingleton_iff_nontrivial.mpr hnt hsub
    · intro hle
      by_contra hzs
      have hsub : Subsingleton (F.presheaf.stalk z) := by
        have : ¬ Nontrivial (F.presheaf.stalk z) := hzs
        exact not_nontrivial_iff_subsingleton.mp this
      obtain ⟨u, hzu, hu⟩ := exists_smul_eq_zero_of_subsingleton_stalk F hU hz hsub
      have hu' : u ∈ Module.annihilator Γ(X, U) Γ(F, U) := Module.mem_annihilator.mpr hu
      exact (mem_basicOpen_iff_notMem_primeIdealOf hU hz u).mp hzu (hle hu')
  refine ⟨⟨(hU.primeIdealOf ⟨y, hy⟩).isPrime, (key y hy).mp hyg.1⟩, ?_⟩
  rintro q ⟨hq, hIq⟩ hqp
  -- the point of `U` corresponding to `q`
  let q' : PrimeSpectrum Γ(X, U) := ⟨q, hq⟩
  let z : X := hU.fromSpec q'
  have hzU : z ∈ U := by
    have : z ∈ Set.range hU.fromSpec.base := ⟨q', rfl⟩
    rwa [hU.range_fromSpec] at this
  have hqz : hU.primeIdealOf ⟨z, hzU⟩ = q' := by
    apply hU.fromSpec.isOpenEmbedding.injective
    exact hU.fromSpec_primeIdealOf ⟨z, hzU⟩
  have hzs : z ∈ F.support := by
    rw [key z hzU, hqz]
    exact hIq
  have hzy : z ⤳ y := by
    have h1 : q' ⤳ hU.primeIdealOf ⟨y, hy⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hqp
    have h2 := h1.map hU.fromSpec.base.hom.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨y, hy⟩] at h2
  have hzy' : z = y := hyg.2 z hzs hzy
  have : q' = hU.primeIdealOf ⟨y, hy⟩ := by
    rw [← hqz]
    congr 1
    exact Subtype.ext hzy'
  rw [show q = q'.asIdeal from rfl, this]

/-- At a generic point `y ∉ D(h)` of the support, a power of `h` kills the germ of any section. -/
theorem exists_pow_smul_germ_eq_zero (F : X.Modules) [F.IsCoherent] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {y : X} (hy : y ∈ U) (hyg : y ∈ F.genericPoints)
    (h : Γ(X, U)) (hyh : y ∉ X.basicOpen h) (t : Γ(F, U)) :
    ∃ n : ℕ, F.presheaf.germ U y hy (h ^ n • t) = 0 := by
  haveI : F.IsQuasicoherent := IsCoherent.quasicoherent
  have hp := primeIdealOf_mem_minimalPrimes_annihilator F hU hy hyg
  have hhp : h ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
    by_contra hnot
    exact hyh ((mem_basicOpen_iff_notMem_primeIdealOf hU hy h).mpr hnot)
  obtain ⟨u, hu, n, hun⟩ := Ideal.exists_mul_pow_mem_of_mem_minimalPrimes' hp hhp
  refine ⟨n, ?_⟩
  rw [germ_eq_zero_iff F hU hy]
  refine ⟨u, (mem_basicOpen_iff_notMem_primeIdealOf hU hy u).mpr hu, ?_⟩
  rw [smul_smul]
  exact Module.mem_annihilator.mp hun t

/-- **`K` is quasi-coherent** (sheaf form of Stacks 02M7; see the module docstring). -/
theorem embeddedPart_isQuasicoherent (F : X.Modules) [AlgebraicGeometry.IsLocallyNoetherian X]
    [F.IsCoherent] : F.embeddedPart.IsQuasicoherent := by
  haveI : F.IsQuasicoherent := IsCoherent.quasicoherent
  apply isQuasicoherent_of_affine_localizing
  · intro U hU h s
    obtain ⟨sv, hsv⟩ : ∃ sv : Γ(F, X.basicOpen h), sv = s.val := ⟨s.val, rfl⟩
    have hsv0 : ∀ (y : X) (hy : y ∈ X.basicOpen h), y ∈ F.genericPoints →
        F.presheaf.germ (X.basicOpen h) y hy sv = 0 := by
      intro y hy hyg
      rw [hsv]
      exact embeddedPart.property F s hy hyg
    obtain ⟨n, t, ht⟩ := F.exists_pow_smul_eq_map_basicOpen hU h sv
    -- the generic points of `U` outside `D(h)`
    let B : Set X := (F.genericPoints ∩ (U : Set X)) \ (X.basicOpen h : Set X)
    have hBfin : B.Finite := (finite_genericPoints_inter F hU).subset Set.sdiff_subset
    have hB : ∀ y ∈ B, ∃ k : ℕ, ∀ hy : y ∈ U, F.presheaf.germ U y hy (h ^ k • t) = 0 := by
      intro y hyB
      obtain ⟨k, hk⟩ := exists_pow_smul_germ_eq_zero F hU hyB.1.2 hyB.1.1 h hyB.2 t
      exact ⟨k, fun _ => hk⟩
    choose! kf hkf using hB
    classical
    let N : ℕ := hBfin.toFinset.sup kf
    have hN : ∀ y ∈ B, ∀ hy : y ∈ U, F.presheaf.germ U y hy (h ^ N • t) = 0 := by
      intro y hyB hy
      have hle : kf y ≤ N := Finset.le_sup (f := kf) (hBfin.mem_toFinset.mpr hyB)
      have : h ^ N • t = h ^ (N - kf y) • (h ^ kf y • t) := by
        rw [smul_smul, ← pow_add, Nat.sub_add_cancel hle]
      rw [this, CoherentFreeStalksAux.germ_smul', hkf y hyB hy, smul_zero]
    -- `h ^ N • t` is a section of `K`
    have htK : h ^ N • t ∈ F.embeddedPartSections U := by
      intro y hy hyg
      by_cases hyh : y ∈ X.basicOpen h
      · have e1 : F.presheaf.germ U y hy t = F.presheaf.germ (X.basicOpen h) y hyh
            (F.presheaf.map (homOfLE (X.basicOpen_le h)).op t) :=
          (F.presheaf.germ_res_apply (homOfLE (X.basicOpen_le h)) y hyh t).symm
        have h1 : F.presheaf.germ U y hy t = 0 := by
          rw [e1, ht, CoherentFreeStalksAux.germ_smul', hsv0 y hyh hyg, smul_zero]
        rw [CoherentFreeStalksAux.germ_smul' F hy (h ^ N) t, h1, smul_zero]
      · exact hN y ⟨⟨hyg, hy⟩, hyh⟩ hy
    refine ⟨N + n, ⟨h ^ N • t, htK⟩, Subtype.ext ?_⟩
    change F.presheaf.map (homOfLE (X.basicOpen_le h)).op (h ^ N • t) = _
    rw [Scheme.Modules.map_smul, map_pow, ht, smul_smul, ← pow_add, hsv]
    rfl
  · intro U hU h t ht
    obtain ⟨n, hn⟩ := F.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero hU h t.val
      (congrArg Subtype.val ht)
    exact ⟨n, Subtype.ext hn⟩

/-- **`K` is coherent** (Stacks 01Y1: a quasi-coherent submodule of a coherent module on a locally
Noetherian scheme). -/
theorem embeddedPart_isCoherent (F : X.Modules) [AlgebraicGeometry.IsLocallyNoetherian X]
    [F.IsCoherent] : F.embeddedPart.IsCoherent := by
  haveI := embeddedPart_isQuasicoherent F
  haveI := embeddedPart.mono_ι F
  exact isCoherent_of_mono (embeddedPart.ι F)

end AlgebraicGeometry.Scheme.Modules

end
