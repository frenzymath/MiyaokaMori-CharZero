import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleUnit
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RegularMeromorphicDenominatorIdeal
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentOfAffineLocalizing
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforwardQuasicoherent

/-! # The ideal of denominators is quasi-coherent

Second paragraph of the proof of Stacks 02P0 (`Stacks02p0`).

**Statement.** `s` a regular meromorphic section of the line bundle `L` on the scheme `X`, with local
fraction representation `s|_{U i} = num i / den i`. The ideal of denominators `I = denomIdeal s ⊆ O_X`
(`RegularMeromorphicDenominatorIdeal`) is quasi-coherent.

**Proof (Stacks 02P0, as formalized).** Quasi-coherence is local (`SheafOfModules.IsQuasicoherent.of_coversTop`),
so it suffices to treat the affine opens `U` contained in some chart `U i`; these cover `X` because the affine
opens form a basis. On such a `U`, we use the localization criterion for quasi-coherence
(`QcOfAffineLocalizingAux.isLocalizing_restrict` + `isQuasicoherent_over_of_isLocalizing`): for `h ∈ Γ(X, U)`,
the restriction `I(U) → I(D(h))` is the localization at `h`, i.e.
* (uniqueness) `t ∈ I(U)` with `t|_{D(h)} = 0` is killed by a power of `h`: this holds already in `O_X`
  (`O_X` is quasi-coherent, `isQuasicoherent_unit`);
* (existence) every `g ∈ I(D(h))` is `h^N • t|_{D(h)}` for some `t ∈ I(U)`. With Stacks: `g = c / h^n` with
  `c ∈ O(U)` (quasi-coherence of `O_X`), and `g • s ∈ L(D(h))` means `den i • l = g • num i` for some
  `l ∈ L(D(h))`. Lift `h^n • l` to `l' ∈ L(U)` with `l'|_{D(h)} = h^{m+n} • l` (quasi-coherence of `L`). The
  section `z := den i • l' - (h^m c) • num i ∈ L(U)` restricts to `0` on `D(h)`, hence `h^k • z = 0`. Thus
  `den i • (h^k • l') = (h^{k+m} c) • num i` on `U`, so `t := h^{k+m} c ∈ I(U)` (`IsMul.of_single`, the
  identity in the single chart `U ≤ U i` suffices), and `t|_{D(h)} = h^{k+m+n} • g`.

Source: Stacks 02P0, second paragraph ("`I_f = {x ∈ A_f | x (a/b) ∈ A_f}`"), 01IB.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection

variable {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules} [L.IsLineBundle]
  (s : AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection L)

theorem resX_self {A : X.Opens} (r : Γ(X, A)) : X.presheaf.map (homOfLE (le_refl A)).op r = r := by
  rw [show (homOfLE (le_refl A)).op = 𝟙 (op A) from rfl, X.presheaf.map_id]; rfl

theorem resM_self (M : X.Modules) {A : X.Opens} (m : Γ(M, A)) :
    M.presheaf.map (homOfLE (le_refl A)).op m = m := by
  rw [show (homOfLE (le_refl A)).op = 𝟙 (op A) from rfl, M.presheaf.map_id]; rfl

/-- Uniqueness half of the localization property for `I` on an affine open `U`: a section of `I(U)`
vanishing on `D(h)` is killed by a power of `h` (this already holds in `O_X`). -/
theorem denomIdeal_pow_smul_eq_zero {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) (h : Γ(X, U))
    (t : Γ(s.denomIdeal, U))
    (ht : s.denomIdeal.presheaf.map (homOfLE (X.basicOpen_le h)).op t = 0) : ∃ n : ℕ, h ^ n • t = 0 := by
  haveI := AlgebraicGeometry.Scheme.Modules.AffinePushforwardAux.isQuasicoherent_unit X
  obtain ⟨n, hn⟩ := (unitModule X).exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero hU h t.val
    (congrArg Subtype.val ht)
  exact ⟨n, Subtype.ext hn⟩

/-- Existence half of the localization property for `I` on an affine open `U ≤ U i`: every section of
`I(D(h))` is `h^N • t|_{D(h)}` for some `t ∈ I(U)` (see the module docstring). -/
theorem denomIdeal_exists_pow_smul_eq (i : s.ι) {U : X.Opens} (hUi : U ≤ s.U i)
    (hU : AlgebraicGeometry.IsAffineOpen U) (h : Γ(X, U)) (g : Γ(s.denomIdeal, X.basicOpen h)) :
    ∃ (n : ℕ) (t : Γ(s.denomIdeal, U)),
      s.denomIdeal.presheaf.map (homOfLE (X.basicOpen_le h)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) ^ n • g := by
  haveI := AlgebraicGeometry.Scheme.Modules.AffinePushforwardAux.isQuasicoherent_unit X
  haveI : L.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree L
  have hD : X.basicOpen h ≤ U := X.basicOpen_le h
  obtain ⟨l, hl⟩ := g.property
  -- lift `g` to `c ∈ O(U)` with `c|_{D(h)} = h^n g`
  obtain ⟨n, c, hc⟩ := (unitModule X).exists_pow_smul_eq_map_basicOpen hU h g.val
  have hc' : X.presheaf.map (homOfLE hD).op (toRing c) =
      (X.presheaf.map (homOfLE hD).op h) ^ n * toRing g.val := congrArg toRing hc
  -- lift `h^n • l` to `l' ∈ L(U)` with `l'|_{D(h)} = h^m • h^n • l`
  obtain ⟨m, l', hl'⟩ :=
    L.exists_pow_smul_eq_map_basicOpen hU h ((X.presheaf.map (homOfLE hD).op h) ^ n • l)
  -- the identity `den i • l = g • num i` on `D(h)`
  have key : X.presheaf.map (homOfLE (hD.trans hUi)).op (s.den i) • l =
      toRing g.val • L.presheaf.map (homOfLE (hD.trans hUi)).op (s.num i) := by
    have := hl i (X.basicOpen h) le_rfl (hD.trans hUi)
    rwa [resM_self, resX_self] at this
  -- `z := den i • l' - (h^m c) • num i` restricts to `0` on `D(h)`
  have hz : L.presheaf.map (homOfLE hD).op
      (X.presheaf.map (homOfLE hUi).op (s.den i) • l' -
        (h ^ m * toRing c) • L.presheaf.map (homOfLE hUi).op (s.num i)) = 0 := by
    rw [map_sub, Scheme.Modules.map_smul, Scheme.Modules.map_smul, hl', map_mul, map_pow, hc',
      resX_resX, resM_resM, sub_eq_zero,
      smul_comm (X.presheaf.map (homOfLE (hD.trans hUi)).op (s.den i))
        ((X.presheaf.map (homOfLE hD).op h) ^ m),
      smul_comm (X.presheaf.map (homOfLE (hD.trans hUi)).op (s.den i))
        ((X.presheaf.map (homOfLE hD).op h) ^ n),
      key, mul_smul, mul_smul]
  obtain ⟨k, hk⟩ := L.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero hU h _ hz
  -- hence `den i • (h^k • l') = (h^k (h^m c)) • num i` on `U`
  have hwit : X.presheaf.map (homOfLE hUi).op (s.den i) • (h ^ k • l') =
      (h ^ k * (h ^ m * toRing c)) • L.presheaf.map (homOfLE hUi).op (s.num i) := by
    rw [smul_sub, sub_eq_zero] at hk
    rw [smul_comm, hk, ← mul_smul]
  refine ⟨k + m + n, ⟨h ^ k * (h ^ m * toRing c), _, IsMul.of_single s i hUi hwit⟩, ?_⟩
  apply Subtype.ext
  change X.presheaf.map (homOfLE hD).op (h ^ k * (h ^ m * toRing c)) =
    (X.presheaf.map (homOfLE hD).op h) ^ (k + m + n) * toRing g.val
  rw [map_mul, map_mul, map_pow, map_pow, hc', pow_add, pow_add]
  ring

/-- **The ideal of denominators is quasi-coherent** (Stacks 02P0, second paragraph). -/
theorem denomIdeal_isQuasicoherent : s.denomIdeal.IsQuasicoherent := by
  -- affine opens contained in some chart `U i`
  let ι' := {U : X.affineOpens // ∃ i, (U : X.Opens) ≤ s.U i}
  have hqc : ∀ U : ι', (s.denomIdeal.over (U.1 : X.Opens)).IsQuasicoherent := fun U => by
    obtain ⟨i, hi⟩ := U.2
    exact QcOfAffineLocalizingAux.isQuasicoherent_over_of_isLocalizing s.denomIdeal U.1.2
      (QcOfAffineLocalizingAux.isLocalizing_restrict s.denomIdeal U.1.2
        (fun h g => s.denomIdeal_exists_pow_smul_eq i hi U.1.2 h g)
        (fun h t ht => s.denomIdeal_pow_smul_eq_zero U.1.2 h t ht))
  refine SheafOfModules.IsQuasicoherent.of_coversTop s.denomIdeal (fun U : ι' => (U.1 : X.Opens)) ?_
  rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover]
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨i, hi⟩ := s.cover x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hi (s.U i).isOpen
  exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, i, hVU⟩, hxV⟩

end AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection

end
