/-
Lower bound, part 3: the test functions `g_ε(s) = ∫_0^s k_ε`, `k_ε(u) = (2/ε) max(0, 1 - |u|/ε)`, the Gaussian
estimates `E|g_ε'(Z)| ≤ 2φ(0)` and `E|g_ε(Z) - c| ≥ 1 - ε φ(0)`, and `√(π/2) ≤ C11a`, hence `C11a = √(π/2)`.
-/
import Poincare11b.LB2
import Poincare11b.Main

namespace Poincare11b

open Poincare11a MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BoundedContinuousFunction

/-- `k_ε(u) = (2/ε) max(0, 1 - |u|/ε)`. -/
noncomputable def kε (ε u : ℝ) : ℝ := 2 / ε * max 0 (1 - |u| / ε)

/-- `g_ε(s) = ∫_0^s k_ε`. -/
noncomputable def gε (ε s : ℝ) : ℝ := ∫ u in (0 : ℝ)..s, kε ε u

variable {ε : ℝ}

lemma continuous_kε (ε : ℝ) : Continuous (kε ε) := by unfold kε; fun_prop

lemma kε_nonneg (hε : 0 < ε) (u : ℝ) : 0 ≤ kε ε u :=
  mul_nonneg (by positivity) (le_max_left _ _)

lemma kε_le (hε : 0 < ε) (u : ℝ) : kε ε u ≤ 2 / ε := by
  unfold kε
  have : max 0 (1 - |u| / ε) ≤ 1 := max_le zero_le_one (by
    have : 0 ≤ |u| / ε := by positivity
    linarith)
  calc 2 / ε * max 0 (1 - |u| / ε) ≤ 2 / ε * 1 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 / ε := mul_one _

lemma kε_zero (hε : 0 < ε) {u : ℝ} (hu : ε ≤ |u|) : kε ε u = 0 := by
  unfold kε
  have : 1 - |u| / ε ≤ 0 := by rw [sub_nonpos, le_div_iff₀ hε]; linarith
  rw [max_eq_left this, mul_zero]

lemma kε_neg (u : ℝ) : kε ε (-u) = kε ε u := by unfold kε; rw [abs_neg]

lemma kε_lip (hε : 0 < ε) (u v : ℝ) : |kε ε u - kε ε v| ≤ 2 / ε ^ 2 * |u - v| := by
  unfold kε
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / ε)]
  have h1 : |max 0 (1 - |u| / ε) - max 0 (1 - |v| / ε)| ≤ |(1 - |u| / ε) - (1 - |v| / ε)| := by
    rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
  have h2 : |(1 - |u| / ε) - (1 - |v| / ε)| = abs (|v| - |u|) / ε := by
    rw [show (1 - |u| / ε) - (1 - |v| / ε) = (|v| - |u|) / ε by ring, abs_div, abs_of_pos hε]
  have h3 : abs (|v| - |u|) ≤ |u - v| := by rw [abs_sub_comm u v]; exact abs_abs_sub_abs_le_abs_sub _ _
  calc 2 / ε * |max 0 (1 - |u| / ε) - max 0 (1 - |v| / ε)|
      ≤ 2 / ε * (|u - v| / ε) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [h2] at h1
        exact h1.trans (div_le_div_of_nonneg_right h3 hε.le)
    _ = 2 / ε ^ 2 * |u - v| := by ring

lemma hasDerivAt_gε (ε s : ℝ) : HasDerivAt (gε ε) (kε ε s) s :=
  ((continuous_kε ε).integral_hasStrictDerivAt 0 s).hasDerivAt

/-- `g_ε(s) = (2/ε)(s - s²/(2ε))` for `0 ≤ s ≤ ε`. -/
lemma gε_small (hε : 0 < ε) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ ε) :
    gε ε s = 2 / ε * (s - s ^ 2 / (2 * ε)) := by
  unfold gε
  have hcongr : ∫ u in (0 : ℝ)..s, kε ε u = ∫ u in (0 : ℝ)..s, 2 / ε * (1 - u / ε) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [uIcc_of_le hs0] at hu
    unfold kε
    rw [abs_of_nonneg hu.1, max_eq_right]
    rw [sub_nonneg, div_le_one hε]; linarith [hu.2]
  rw [hcongr]
  have hd : ∀ u ∈ uIcc (0 : ℝ) s, HasDerivAt (fun u => 2 / ε * (u - u ^ 2 / (2 * ε))) (2 / ε * (1 - u / ε)) u := by
    intro u _
    have := ((hasDerivAt_id u).sub ((hasDerivAt_pow 2 u).div_const (2 * ε))).const_mul (2 / ε)
    convert this using 1
    simp; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (μ := volume) (by fun_prop) _ _)]
  ring

lemma gε_eps (hε : 0 < ε) : gε ε ε = 1 := by
  rw [gε_small hε hε.le le_rfl]; field_simp; ring

lemma gε_neg (s : ℝ) : gε ε (-s) = -gε ε s := by
  unfold gε
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := s) (fun u => kε ε u)
  simp only [kε_neg, neg_zero] at h
  rw [intervalIntegral.integral_symm, ← h]

lemma gε_mono (hε : 0 < ε) {s t : ℝ} (hst : s ≤ t) : gε ε s ≤ gε ε t := by
  unfold gε
  have h := intervalIntegral.integral_interval_sub_left ((continuous_kε ε).intervalIntegrable (μ := volume) 0 t)
    ((continuous_kε ε).intervalIntegrable (μ := volume) 0 s)
  have hnn : 0 ≤ ∫ u in s..t, kε ε u := intervalIntegral.integral_nonneg hst (fun u _ => kε_nonneg hε u)
  linarith

lemma gε_big (hε : 0 < ε) {s : ℝ} (hs : ε ≤ s) : gε ε s = 1 := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    ((continuous_kε ε).intervalIntegrable (μ := volume) 0 ε)
    ((continuous_kε ε).intervalIntegrable (μ := volume) ε s)
  have h0 : ∫ u in ε..s, kε ε u = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun u hu => ?_)]
    · simp
    · rw [uIcc_of_le hs] at hu
      exact kε_zero hε (by rw [abs_of_nonneg (by linarith [hu.1])]; exact hu.1)
  unfold gε
  rw [← h, h0, add_zero]
  exact gε_eps hε

lemma abs_gε_le (hε : 0 < ε) (s : ℝ) : |gε ε s| ≤ 1 := by
  rw [abs_le]
  constructor
  · rcases le_total s (-ε) with h | h
    · rw [show gε ε s = -gε ε (-s) by rw [gε_neg, neg_neg], gε_big hε (by linarith)]
    · have := gε_mono hε h; rw [gε_neg, gε_eps hε] at this; exact this
  · rcases le_total ε s with h | h
    · rw [gε_big hε h]
    · have := gε_mono hε h; rw [gε_eps hε] at this; exact this

/-- `|g_ε(s)| ≥ 1 - (ε/2) k_ε(s)`. -/
lemma abs_gε_ge (hε : 0 < ε) (s : ℝ) : 1 - ε / 2 * kε ε s ≤ |gε ε s| := by
  have key : ∀ s, 0 ≤ s → 1 - ε / 2 * kε ε s ≤ gε ε s := by
    intro s hs
    rcases le_total ε s with h | h
    · rw [gε_big hε h]
      have := kε_nonneg hε s
      nlinarith
    · rw [gε_small hε hs h]
      unfold kε
      rw [abs_of_nonneg hs, max_eq_right (by rw [sub_nonneg, div_le_one hε]; exact h)]
      field_simp
      nlinarith
  rcases le_total 0 s with hs | hs
  · exact (key s hs).trans (le_abs_self _)
  · have := key (-s) (by linarith)
    rw [kε_neg, gε_neg] at this
    exact this.trans (neg_le_abs _)

/-! ### Gaussian estimates -/

lemma integral_gauss (F : ℝ → ℝ) :
    ∫ x, F x ∂(gaussianReal 0 1) = ∫ x, gaussianPDFReal 0 1 x * F x := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  rfl

lemma gaussianPDF_le (x : ℝ) : gaussianPDFReal 0 1 x ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have : Real.exp (-x ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := sq_nonneg x; linarith
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = (Real.sqrt (2 * Real.pi))⁻¹ := mul_one _

lemma gaussianPDF_neg (x : ℝ) : gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  unfold gaussianPDFReal; simp

lemma integral_gauss_neg (F : ℝ → ℝ) :
    ∫ x, F (-x) ∂(gaussianReal 0 1) = ∫ x, F x ∂(gaussianReal 0 1) := by
  rw [integral_gauss, integral_gauss]
  have := integral_neg_eq_self (fun x => gaussianPDFReal 0 1 x * F x) volume
  rw [← this]
  congr 1; funext x
  simp [gaussianPDF_neg]

/-- `∫_ℝ k_ε = 2`. -/
lemma integral_kε (hε : 0 < ε) : ∫ u, kε ε u = 2 := by
  have hsupp : ∀ u, u ∉ Ioc (-ε) ε → kε ε u = 0 := by
    intro u hu
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hu
    apply kε_zero hε
    rcases hu with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, ← intervalIntegral.integral_of_le (by linarith)]
  have h := intervalIntegral.integral_add_adjacent_intervals
    ((continuous_kε ε).intervalIntegrable (μ := volume) (-ε) 0)
    ((continuous_kε ε).intervalIntegrable (μ := volume) 0 ε)
  rw [← h, intervalIntegral.integral_symm]
  change -gε ε (-ε) + gε ε ε = 2
  rw [gε_neg, gε_eps hε]; ring

lemma integrable_kε (hε : 0 < ε) : Integrable (kε ε) := by
  by_contra h
  have := integral_undef h
  rw [integral_kε hε] at this
  norm_num at this

/-- `E|k_ε(Z)| ≤ 2 φ(0)`. -/
lemma gauss_kε_le (hε : 0 < ε) : ∫ x, |kε ε x| ∂(gaussianReal 0 1) ≤ 2 * (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [integral_gauss]
  have hint : Integrable (fun x => (Real.sqrt (2 * Real.pi))⁻¹ * kε ε x) := (integrable_kε hε).const_mul _
  calc ∫ x, gaussianPDFReal 0 1 x * |kε ε x|
      ≤ ∫ x, (Real.sqrt (2 * Real.pi))⁻¹ * kε ε x := by
        refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) hint (Eventually.of_forall (fun x => ?_))
        · exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) (abs_nonneg _)
        · dsimp only
          rw [abs_of_nonneg (kε_nonneg hε x)]
          exact mul_le_mul_of_nonneg_right (gaussianPDF_le x) (kε_nonneg hε x)
    _ = 2 * (Real.sqrt (2 * Real.pi))⁻¹ := by rw [integral_const_mul, integral_kε hε]; ring

lemma integrable_gauss_of_bound {F : ℝ → ℝ} (hF : Continuous F) (M : ℝ) (hM : ∀ x, |F x| ≤ M) :
    Integrable F (gaussianReal 0 1) :=
  Integrable.of_bound hF.aestronglyMeasurable M (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hM x))

lemma continuous_gε (ε : ℝ) : Continuous (gε ε) :=
  continuous_iff_continuousAt.mpr (fun s => (hasDerivAt_gε ε s).continuousAt)

/-- `E|g_ε(Z) - c| ≥ 1 - ε φ(0)` for every `c`. -/
lemma gauss_gε_ge (hε : 0 < ε) (c : ℝ) :
    1 - ε * (Real.sqrt (2 * Real.pi))⁻¹ ≤ ∫ x, |gε ε x - c| ∂(gaussianReal 0 1) := by
  have hcont := continuous_gε ε
  have hb := abs_gε_le hε
  have i1 : Integrable (fun x => |gε ε x - c|) (gaussianReal 0 1) :=
    integrable_gauss_of_bound (by fun_prop) (1 + |c|) (fun x => by
      rw [abs_abs]; have := abs_add_le (gε ε x) (-c); rw [abs_neg, ← sub_eq_add_neg] at this
      linarith [hb x])
  have i2 : Integrable (fun x => |gε ε x + c|) (gaussianReal 0 1) :=
    integrable_gauss_of_bound (by fun_prop) (1 + |c|) (fun x => by
      rw [abs_abs]; linarith [abs_add_le (gε ε x) c, hb x])
  have i3 : Integrable (fun x => |gε ε x|) (gaussianReal 0 1) :=
    integrable_gauss_of_bound (by fun_prop) 1 (fun x => by rw [abs_abs]; exact hb x)
  have i4 : Integrable (fun x => kε ε x) (gaussianReal 0 1) :=
    integrable_gauss_of_bound (continuous_kε ε) (2 / ε) (fun x => by
      rw [abs_of_nonneg (kε_nonneg hε x)]; exact kε_le hε x)
  have hsym : ∫ x, |gε ε x - c| ∂(gaussianReal 0 1) = ∫ x, |gε ε x + c| ∂(gaussianReal 0 1) := by
    rw [← integral_gauss_neg (fun x => |gε ε x + c|)]
    congr 1; funext x
    rw [gε_neg, show -gε ε x + c = -(gε ε x - c) by ring, abs_neg]
  have h2 : ∫ x, 2 * |gε ε x| ∂(gaussianReal 0 1) ≤
      ∫ x, (|gε ε x - c| + |gε ε x + c|) ∂(gaussianReal 0 1) := by
    refine integral_mono (i3.const_mul 2) (i1.add i2) (fun x => ?_)
    have := abs_sub_le (gε ε x - c) 0 (-(gε ε x + c))
    have e : 2 * |gε ε x| = |(gε ε x - c) - -(gε ε x + c)| := by
      rw [show (gε ε x - c) - -(gε ε x + c) = 2 * gε ε x by ring, abs_mul, abs_two]
    rw [e]
    calc |(gε ε x - c) - -(gε ε x + c)| ≤ |gε ε x - c| + |-(gε ε x + c)| := by
          have := abs_add_le (gε ε x - c) (gε ε x + c)
          rw [abs_neg]
          calc |(gε ε x - c) - -(gε ε x + c)| = |(gε ε x - c) + (gε ε x + c)| := by ring_nf
            _ ≤ _ := this
      _ = |gε ε x - c| + |gε ε x + c| := by rw [abs_neg]
  have h3 : ∫ x, (1 - ε / 2 * kε ε x) ∂(gaussianReal 0 1) ≤ ∫ x, |gε ε x| ∂(gaussianReal 0 1) :=
    integral_mono ((integrable_const 1).sub (i4.const_mul _)) i3 (fun x => abs_gε_ge hε x)
  have h4 : ∫ x, (1 - ε / 2 * kε ε x) ∂(gaussianReal 0 1) = 1 - ε / 2 * ∫ x, kε ε x ∂(gaussianReal 0 1) := by
    rw [integral_sub (integrable_const 1) (i4.const_mul _), integral_const, integral_const_mul]
    simp
  have h5 : ∫ x, kε ε x ∂(gaussianReal 0 1) ≤ 2 * (Real.sqrt (2 * Real.pi))⁻¹ := by
    have := gauss_kε_le hε
    have e : ∫ x, |kε ε x| ∂(gaussianReal 0 1) = ∫ x, kε ε x ∂(gaussianReal 0 1) := by
      congr 1; funext x; exact abs_of_nonneg (kε_nonneg hε x)
    rwa [e] at this
  rw [integral_add i1 i2, ← hsym, integral_const_mul] at h2
  have : 0 < ε / 2 := by positivity
  nlinarith

/-- Every valid constant is at least `√(π/2)`. -/
theorem sqrt_le_of_valid {C : ℝ}
    (hC : ∀ (m : ℕ) (f : Cube m → ℝ), avg (fun x => |f x - avg f|) ≤ C * avg (gradNorm f)) :
    Real.sqrt (Real.pi / 2) ≤ C := by
  have hC1 : 1 ≤ C := one_le_of_valid hC
  set φ0 := (Real.sqrt (2 * Real.pi))⁻¹ with hφ0def
  have hφ0 : 0 < φ0 := by positivity
  have key : ∀ ε, 0 < ε → 1 - ε * φ0 ≤ C * (2 * φ0) := by
    intro ε hε
    let G : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (gε ε) (continuous_gε ε) 1
      (fun x => by rw [Real.norm_eq_abs]; exact abs_gε_le hε x)
    let K : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (kε ε) (continuous_kε ε) (2 / ε)
      (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (kε_nonneg hε x)]; exact kε_le hε x)
    have ht := transfer hC G K (fun x => hasDerivAt_gε ε x) (L := 2 / ε ^ 2) (by positivity)
      (fun x y => kε_lip hε x y)
    simp only [G, K, BoundedContinuousFunction.coe_ofNormedAddCommGroup] at ht
    have h1 := gauss_gε_ge hε (∫ r, gε ε r ∂(gaussianReal 0 1))
    have h2 := gauss_kε_le hε
    calc 1 - ε * φ0 ≤ ∫ x, |gε ε x - ∫ r, gε ε r ∂(gaussianReal 0 1)| ∂(gaussianReal 0 1) := h1
      _ ≤ C * ∫ s, |kε ε s| ∂(gaussianReal 0 1) := ht
      _ ≤ C * (2 * φ0) := mul_le_mul_of_nonneg_left h2 (by linarith)
  have h1 : 1 ≤ C * (2 * φ0) := by
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    have := key (δ / φ0) (by positivity)
    rw [div_mul_cancel₀ δ hφ0.ne'] at this
    linarith
  have hpi : 0 < Real.pi / 2 := by positivity
  have e : Real.sqrt (Real.pi / 2) * (2 * φ0) = 1 := by
    have h4 : Real.sqrt (2 * Real.pi) = 2 * Real.sqrt (Real.pi / 2) := by
      rw [show 2 * Real.pi = 2 ^ 2 * (Real.pi / 2) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
    rw [hφ0def, h4]
    have : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr hpi
    field_simp
  have h2φ : 0 < 2 * φ0 := by positivity
  exact le_of_mul_le_mul_right (by rw [e]; exact h1) h2φ

/-- `√(π/2) ≤ C11a`. -/
theorem sqrt_le_C11a : Real.sqrt (Real.pi / 2) ≤ C11a :=
  le_csInf ⟨Real.sqrt (Real.pi / 2), fun m f => poincare_L1_sharp m f⟩ (fun _ hC => sqrt_le_of_valid hC)

/-- The L¹ Poincaré constant of the Hamming cube: `C11a = √(π/2)`. -/
theorem C11a_eq : C11a = Real.sqrt (Real.pi / 2) := le_antisymm C11a_le_sqrt sqrt_le_C11a

end Poincare11b
