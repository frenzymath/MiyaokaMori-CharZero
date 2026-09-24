import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorLocalData
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueIsoOfLocalFrames
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackFrameRankOne
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierLocalDataPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleFrameRatio
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDominantPullback

/-! # Pullback of Cartier divisors is compatible with pullback of line bundles

The pullback of a Cartier divisor is compatible with the pullback of its line bundle:
`O_X(f^*D) ≅ f^*O_Y(D)` (whenever `f^*D` is defined).

Sources: Hartshorne II.6 (II.6.13, II.6.18); Stacks 0C4U (effective case, `f^*O_S(D) = O_{S'}(f^*D)`),
02OO(2) (pullback defined for a dominant morphism of integral schemes). Used for `f^*(-K_X)` in the
degree identity of the paper.

Proof (steps 1–5):
1. Let `(U_i, g_i)` be any local data of `D`: it is local data and `D = ofLocalData U g`
   (`cartierDivisor_exists_localData`; the proof below takes it with `Classical.epsilon`, in the proof
   only). Then `f^*D = ofLocalData (f^{-1}U_i) (f^♯ g_i)` (`CartierDivisor.pullback_ofLocalData`, the
   well-definedness lemma of the pullback), with
   `f^♯ = AlgebraicGeometry.Scheme.dominantFunctionFieldMap f`, and the pulled-back data is local data
   (`IsLocalData.pullback`, Stacks 02OO(2)). We restrict the index set to the `i` with `U_i ≠ ∅`
   (still a cover); then `f^{-1}U_i ≠ ∅` since `f` is surjective.
2. Local equations: `t_i ∈ 𝒦^*(U_i)` of `D` with generic value `g_i`, and `t'_i ∈ 𝒦^*(f^{-1}U_i)` of
   `f^*D` with generic value `f^♯ g_i` (`IsLocalData.exists_isLocalEquation_ofLocalData`).
3. Frames (Hartshorne II.6.13): `b_i := t'_i^{-1}` is a frame of `O_X(f^*D)` on `f^{-1}U_i`
   (`IsLocalEquation.isFrame`); `c_i := f^*(t_i^{-1})` (the adjunction-unit section of the frame
   `t_i^{-1}` of `O_Y(D)` on `U_i`) is a frame of `f^*O_Y(D)` on `f^{-1}U_i` (`isFrame_unitSec_pullback`).
4. Transition units: on `W = U_i ∩ U_j ≠ ∅` write `t_i^{-1} = w • t_j^{-1}` with `w ∈ O_Y(W)`
   (coordinate in the frame `t_j^{-1}`); then `germ(w) g_j^{-1} = g_i^{-1}` in `K(Y)`
   (`smul_res_frame_iff`). Applying `f^♯` and `f^♯(germ w) = germ(f^♯ w)`
   (`dominantFunctionFieldMap_germToFunctionField`) gives `germ(f^♯ w) (f^♯g_j)^{-1} = (f^♯g_i)^{-1}` in
   `K(X)`, i.e. `b_i = f^♯(w) • b_j` on `f^{-1}W` (`smul_res_frame_iff` again). On the other side
   `c_i = f^*(w • t_j^{-1}) = f^♯(w) • c_j` by linearity of the unit (`unitSec_smul`, `unitSec_res`).
5. Gluing: the two line bundles have frames with the same transition units on the cover
   `f^{-1}U_i`, hence are isomorphic (`exists_iso_of_local_frames_transition`, Stacks 01CR + 04TN).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Frames of `O_X(f^*D)` and `f^*O_Y(D)` on the pulled-back cover have the same transition units;
hence (step 5) the two line bundles are isomorphic. Stated for `lineBundleModules`. -/
theorem CartierDivisor.lineBundleModules_pullback_nonempty_iso {k : Type u} [Field k]
    {X Y : Variety k} (f : X.toScheme ⟶ Y.toScheme) (hf : Function.Surjective f.base)
    (D : CartierDivisor Y) :
    Nonempty (CartierDivisor.lineBundleModules (CartierDivisor.pullback f hf D) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback f).obj (CartierDivisor.lineBundleModules D)) := by
  classical
  have hdom : AlgebraicGeometry.IsDominant f := ⟨hf.denseRange⟩
  -- Step 1: the chosen local data
  let P : (Σ ι : Type u, (ι → Y.toScheme.Opens) × (ι → (Y.toScheme.functionField)ˣ)) → Prop :=
    fun d => CartierDivisor.IsLocalData d.2.1 d.2.2 ∧ D = CartierDivisor.ofLocalData d.2.1 d.2.2
  let d := @Classical.epsilon
    (Σ ι : Type u, (ι → Y.toScheme.Opens) × (ι → (Y.toScheme.functionField)ˣ))
    ⟨⟨PEmpty, fun e => e.elim, fun e => e.elim⟩⟩ P
  have hdspec : P d := by
    obtain ⟨ι, U, g, hUg, hD⟩ := cartierDivisor_exists_localData Y D
    exact Classical.epsilon_spec (p := P) ⟨⟨ι, U, g⟩, hUg, hD⟩
  obtain ⟨hUg, hD⟩ := hdspec
  let U : d.1 → Y.toScheme.Opens := d.2.1
  let g : d.1 → (Y.toScheme.functionField)ˣ := d.2.2
  let g' : d.1 → (X.toScheme.functionField)ˣ :=
    fun i => Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom (g i)
  have hpull : CartierDivisor.pullback f hf D =
      CartierDivisor.ofLocalData (fun i : d.1 => f ⁻¹ᵁ U i) g' :=
    (congrArg (CartierDivisor.pullback f hf) hD).trans (CartierDivisor.pullback_ofLocalData f hf hUg)
  have hUg' : CartierDivisor.IsLocalData (fun i : d.1 => f ⁻¹ᵁ U i) g' :=
    CartierDivisor.IsLocalData.pullback f hUg
  -- the cover by the nonempty pieces
  let ι' := {i : d.1 // Nonempty (U i)}
  let V : ι' → X.toScheme.Opens := fun i => f ⁻¹ᵁ U i.1
  have hcover : (⨆ i, V i) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have hx : x ∈ (⨆ i, f ⁻¹ᵁ U i : X.toScheme.Opens) := by rw [hUg'.1]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨⟨i, ⟨⟨f.base x, hi⟩⟩⟩, hi⟩
  have hne : ∀ i : ι', Nonempty (U i.1) := fun i => i.2
  have hne' : ∀ i : ι', Nonempty (V i) := fun i => by
    obtain ⟨⟨y, hy⟩⟩ := i.2
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩⟩
  -- Step 2: local equations
  choose t ht hloc using fun i : ι' =>
    @CartierDivisor.IsLocalData.exists_isLocalEquation_ofLocalData k _ Y d.1 U g hUg i.1 (hne i)
  choose t' ht' hloc' using fun i : ι' =>
    @CartierDivisor.IsLocalData.exists_isLocalEquation_ofLocalData k _ X d.1
      (fun i : d.1 => f ⁻¹ᵁ U i) g' hUg' i.1 (hne' i)
  have hlocD : ∀ i : ι', CartierDivisor.IsLocalEquation D (U i.1) (t i) := fun i => by
    rw [hD]; exact hloc i
  have hlocP : ∀ i : ι',
      CartierDivisor.IsLocalEquation (CartierDivisor.pullback f hf D) (V i) (t' i) := fun i => by
    rw [hpull]; exact hloc' i
  -- Step 3: frames
  let M := CartierDivisor.lineBundleModules (CartierDivisor.pullback f hf D)
  let N₀ := CartierDivisor.lineBundleModules D
  let N := (AlgebraicGeometry.Scheme.Modules.pullback f).obj N₀
  let b : ∀ i : ι', Γ(M, V i) := fun i => (hlocP i).frame
  let a : ∀ i : ι', Γ(N₀, U i.1) := fun i => (hlocD i).frame
  let c : ∀ i : ι', Γ(N, V i) := fun i => MiyaokaMori.DualPullback.unitSec f N₀ (a i)
  have hb : ∀ i, AlgebraicGeometry.Scheme.Modules.IsFrame M (V i) (b i) :=
    fun i => (hlocP i).isFrame
  have hc : ∀ i, AlgebraicGeometry.Scheme.Modules.IsFrame N (V i) (c i) :=
    fun i => MiyaokaMori.DualPullback.isFrame_unitSec_pullback f N₀ (hlocD i).isFrame
  -- Step 4: transition units
  have htrans : ∀ i j : ι', Nonempty (V i ⊓ V j : X.toScheme.Opens) →
      ∃ u : Γ(X.toScheme, V i ⊓ V j),
        M.res inf_le_left (b i) = u • M.res inf_le_right (b j) ∧
        N.res inf_le_left (c i) = u • N.res inf_le_right (c j) := by
    intro i j hij
    obtain ⟨⟨x, hx⟩⟩ := hij
    let W : Y.toScheme.Opens := U i.1 ⊓ U j.1
    have hWne : Nonempty W := ⟨⟨f.base x, hx⟩⟩
    have hUi : Nonempty (U i.1) := hne i
    have hUj : Nonempty (U j.1) := hne j
    have hVW : V i ⊓ V j ≤ f ⁻¹ᵁ W := fun x hx => hx
    have hVWne : Nonempty (f ⁻¹ᵁ W) := ⟨⟨x, hVW hx⟩⟩
    have h1 : f ⁻¹ᵁ W ≤ V i := fun y hy => hy.1
    have h2 : f ⁻¹ᵁ W ≤ V j := fun y hy => hy.2
    have hVi : Nonempty (V i) := hne' i
    have hVj : Nonempty (V j) := hne' j
    -- the transition unit on Y
    let w : Γ(Y.toScheme, W) :=
      ((hlocD j).isFrame.restrict (inf_le_right : W ≤ U j.1)).coord le_rfl
        (N₀.res inf_le_left (a i))
    have hw : w • N₀.res inf_le_right (a j) = N₀.res inf_le_left (a i) := by
      have := ((hlocD j).isFrame.restrict (inf_le_right : W ≤ U j.1)).coord_smul_frame le_rfl
        (N₀.res inf_le_left (a i))
      rwa [AlgebraicGeometry.Scheme.Modules.res_self] at this
    have hY : Y.toScheme.germToFunctionField W w * ((g j.1)⁻¹ : (Y.toScheme.functionField)ˣ) =
        ((g i.1)⁻¹ : (Y.toScheme.functionField)ˣ) := by
      have := ((hlocD i).smul_res_frame_iff (hlocD j) inf_le_left inf_le_right w).mp hw
      rwa [Y.toScheme.rationalUnitsSectionToFunctionField_res (U j.1) W inf_le_right,
        Y.toScheme.rationalUnitsSectionToFunctionField_res (U i.1) W inf_le_left,
        ht j, ht i] at this
    -- push the unit to X
    let u₀ : Γ(X.toScheme, f ⁻¹ᵁ W) := f.app W w
    have hcoe : ∀ e : (Y.toScheme.functionField)ˣ,
        ((Units.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.toMonoidHom e)⁻¹ :
          (X.toScheme.functionField)ˣ) =
        AlgebraicGeometry.Scheme.dominantFunctionFieldMap f ((e⁻¹ : (Y.toScheme.functionField)ˣ) :
          Y.toScheme.functionField) := by
      intro e
      rw [← map_inv, Units.coe_map]
      rfl
    have hX : X.toScheme.germToFunctionField (f ⁻¹ᵁ W) u₀ *
          ((g' j.1)⁻¹ : (X.toScheme.functionField)ˣ) =
        ((g' i.1)⁻¹ : (X.toScheme.functionField)ˣ) := by
      have := congrArg (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f) hY
      rw [map_mul, AlgebraicGeometry.Intersection.dominantFunctionFieldMap_germToFunctionField f W w] at this
      rw [hcoe, hcoe]
      exact this
    have hMW : u₀ • M.res h2 (b j) = M.res h1 (b i) := by
      refine ((hlocP i).smul_res_frame_iff (hlocP j) h1 h2 u₀).mpr ?_
      rw [X.toScheme.rationalUnitsSectionToFunctionField_res (V j) (f ⁻¹ᵁ W) h2,
        X.toScheme.rationalUnitsSectionToFunctionField_res (V i) (f ⁻¹ᵁ W) h1, ht' j, ht' i]
      exact hX
    have hres_i : N.res h1 (MiyaokaMori.DualPullback.unitSec f N₀ (a i)) =
        MiyaokaMori.DualPullback.unitSec f N₀ (N₀.res inf_le_left (a i)) :=
      (MiyaokaMori.DualPullback.unitSec_res f N₀ (inf_le_left : W ≤ U i.1) (a i)).symm
    have hres_j : N.res h2 (MiyaokaMori.DualPullback.unitSec f N₀ (a j)) =
        MiyaokaMori.DualPullback.unitSec f N₀ (N₀.res inf_le_right (a j)) :=
      (MiyaokaMori.DualPullback.unitSec_res f N₀ (inf_le_right : W ≤ U j.1) (a j)).symm
    have hNW : u₀ • N.res h2 (c j) = N.res h1 (c i) := by
      change u₀ • N.res h2 (MiyaokaMori.DualPullback.unitSec f N₀ (a j)) =
        N.res h1 (MiyaokaMori.DualPullback.unitSec f N₀ (a i))
      rw [hres_i, hres_j, ← hw, MiyaokaMori.DualPullback.unitSec_smul]
    refine ⟨X.toScheme.presheaf.map (homOfLE hVW).op u₀, ?_, ?_⟩
    · have := congrArg (M.res hVW) hMW
      rw [AlgebraicGeometry.Scheme.Modules.res_smul, AlgebraicGeometry.Scheme.Modules.res_res,
        AlgebraicGeometry.Scheme.Modules.res_res] at this
      exact this.symm
    · have := congrArg (N.res hVW) hNW
      rw [AlgebraicGeometry.Scheme.Modules.res_smul, AlgebraicGeometry.Scheme.Modules.res_res,
        AlgebraicGeometry.Scheme.Modules.res_res] at this
      exact this.symm
  -- Step 5: glue
  obtain ⟨e, -⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_of_local_frames_transition
    V hcover b c hb hc htrans
  exact ⟨e⟩

theorem CartierDivisor.lineBundle_pullback {k : Type*} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) (hf : Function.Surjective f.base) (D : CartierDivisor Y) :
    Nonempty ((CartierDivisor.pullback f hf D).lineBundle.toModules
      ≅ (AlgebraicGeometry.Scheme.Modules.pullback f).obj D.lineBundle.toModules) :=
  CartierDivisor.lineBundleModules_pullback_nonempty_iso f hf D

end
