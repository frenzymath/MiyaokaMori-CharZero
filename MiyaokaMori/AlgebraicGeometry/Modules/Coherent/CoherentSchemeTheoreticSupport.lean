import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.FlatFamilyRestrictAffineBase
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.AnnihilatorIdealSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ClosedImmersionPullbackStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ClosedImmersionUnitIsoOfAnnihilated

/-! # Scheme-theoretic support of a coherent sheaf

**Scheme-theoretic support of a coherent sheaf** (first half of Stacks 02OM; Stacks, *Morphisms of
Schemes*, section "Scheme theoretic support", and Stacks 01QY): on a locally Noetherian scheme `X`, a
coherent `F` is the pushforward `i_* G` of a coherent module `G` with full support on the closed
subscheme `Z = V(Ann F)`, `i : Z → X`.

This is the step of Stacks 0AYT (and of 0BEM) that only needs "`F = i_* G` with `Supp G = Z`"; the
additional conclusions of 02OM (`Z` and `G` without embedded points) are not needed there and are not
asserted here. It is the first half of `Scheme.Modules.eq_pushforward_of_noEmbeddedPoints` (`Stacks02om`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Scheme-theoretic support** (Stacks 02OM, first half; Stacks, Morphisms, section "Scheme theoretic
support"; Stacks 01QY). `X` locally Noetherian, `F` coherent. Then there is a quasi-coherent ideal sheaf
`I` and a coherent module `G` on the closed subscheme `Z := I.subscheme` with `Supp G = Z` and
`i_* G ≅ F`, where `i := I.subschemeι`.

Proof (self-contained):
1. **The annihilator ideal.** For an affine open `U = Spec A` of `X` put `I(U) := Ann_A (F(U))`. Since `F`
   is coherent and `X` locally Noetherian, `F(U)` is a finitely presented `A`-module, and the annihilator of
   a finitely presented module commutes with localisation (`Ann(M_f) = Ann(M)_f`, because `M` has a finite
   generating set `m_1, …, m_r` and `Ann(M) = ⋂ Ann(m_i)`, each `Ann(m_i)` being the kernel of `A → M`,
   which commutes with localisation). Hence `U ↦ I(U)` is compatible with restriction to basic opens and
   defines an `X.IdealSheafData` (Mathlib: `Scheme.IdealSheafData` is given by ideals on affine opens
   compatible with `Ideal.map` along basic opens). `I` is quasi-coherent by construction; it is also
   `ker (O_X → 𝓗om(F, F))`, i.e. the annihilator ideal sheaf (Stacks 01Y1 gives coherence, not needed).
2. **`I · F = 0` and `Supp F = V(I)`.** By construction `I(U) F(U) = 0` on every affine open. For
   `x ∈ U = Spec A` with prime `p`, `F_x = F(U)_p` is a finitely generated module over the local ring
   `A_p`, so `F_x ≠ 0 ⟺ Ann(F_x) ≠ A_p ⟺ Ann(F(U))_p ⊆ p A_p ⟺ p ∈ V(Ann F(U))`. Hence
   `Supp F = V(I) = I.support` (Mathlib: `IdealSheafData.mem_support_iff_of_mem`, and
   `Module.mem_support_iff_of_finite` / `rankAtStalk_eq_zero_iff_notMem_support`-style lemmas for the
   finitely generated case).
3. **`F ≅ i_* i^* F`.** Let `Z := I.subscheme`, `i := I.subschemeι` (a closed immersion whose image is
   `I.support`, Mathlib `IdealSheafData.range_subschemeι`) and `G := i^* F`. The adjunction unit
   `η : F → i_* i^* F` is an isomorphism: by `AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective` it suffices to
   check stalks. At `x = i(z)`: `(i_* i^* F)_x = (i^* F)_z` (stalk of a pushforward along a closed
   embedding is the stalk at the preimage, `TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`),
   and `(i^* F)_z = O_{Z,z} ⊗_{O_{X,x}} F_x = (O_{X,x}/I_x) ⊗ F_x = F_x / I_x F_x = F_x` because
   `I_x F_x = 0` (step 2); the composite is the identity of `F_x` (unit–counit compatibility of stalks).
   At `x ∉ i(Z) = Supp F` both stalks are `0` (`F_x = 0` by step 2; `(i_* N)_x = 0` for `x` outside the
   closed image since `x` has an open neighbourhood disjoint from `i(Z)`).
   This is Stacks 01QY: `i_*` is an equivalence between quasi-coherent `O_Z`-modules and quasi-coherent
   `O_X`-modules killed by `I`, with inverse `i^*`.
4. **`G` is coherent with full support.** `G = i^* F` is quasi-coherent (pullback of quasi-coherent,
   Stacks 01BG) and of finite type (Stacks 01B6, `Scheme.Modules.isFiniteType_pullback`), so coherent;
   `G_z = F_{i(z)} ≠ 0` for every `z ∈ Z` by steps 2–3, i.e. `G.support = Set.univ`.

**Formalization.** The three facts (a)(b)(c) are the named declarations used for Stacks 02OM:
* (a) steps 1–2: `IdealSheafData.exists_isAnnihilatorOf` (the annihilator `X.IdealSheafData`),
  `IsAnnihilatorOf.coe_support_eq` (`Supp I = Supp F`), `IsAnnihilatorOf.smul_stalk_eq_zero`
  (`ker(O_{X,ι z} → O_{Z,z})` kills `F_{ι z}`) — all in `AnnihilatorIdealSheaf`;
* (b) step 3: `Modules.nonempty_pushforward_pullback_iso` (`ClosedImmersionUnitIsoOfAnnihilated`);
* (c) step 4: `Modules.isCoherent_pullback` (`FlatFamilyRestrictAffineBase`, for an arbitrary morphism)
  and `Modules.mem_support_pullback_iff` (`ClosedImmersionPullbackStalk`).

Edge cases: `F = 0` ⇒ `I = O_X`, `Z = ∅`, `G = 0` (support `= Set.univ = ∅` on the empty scheme),
`i_* 0 ≅ 0` — fine. `X = ∅` — trivial. Non-reduced `X`/`F` is allowed (nothing is reduced here). -/
theorem AlgebraicGeometry.Scheme.Modules.exists_pushforward_subschemeι_iso_of_isCoherent
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] :
    ∃ (I : X.IdealSheafData) (G : I.subscheme.Modules),
      G.IsCoherent ∧ G.support = Set.univ ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj G ≅ F) := by
  obtain ⟨I, hI⟩ := AlgebraicGeometry.Scheme.IdealSheafData.exists_isAnnihilatorOf F
  have hker : ∀ z : I.subscheme, ∀ a ∈ RingHom.ker (I.subschemeι.stalkMap z).hom,
      ∀ m : F.stalk (I.subschemeι.base z), a • m = 0 :=
    fun z a ha m => hI.smul_stalk_eq_zero z ha m
  refine ⟨I, (AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj F,
    AlgebraicGeometry.Scheme.Modules.isCoherent_pullback _ F, ?_,
    AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_pullback_iso I.subschemeι F hker
      hI.support_subset_range⟩
  -- `Supp G = Z`: `z ∈ Supp (ι^* F) ↔ ι z ∈ Supp F = Supp I = ι(Z)`
  refine Set.eq_univ_of_forall fun z => ?_
  rw [AlgebraicGeometry.Scheme.Modules.mem_support_pullback_iff _ F z (hker z), ← hI.coe_support_eq,
    ← I.range_subschemeι]
  exact ⟨z, rfl⟩

end
