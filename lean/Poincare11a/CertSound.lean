/-
Soundness of the certificate checker (paper Proposition 4.1; see README.md, Presentation).
-/
import Poincare11a.Bound
import Poincare11a.Partition
import Mathlib.Analysis.Real.Pi.Bounds

namespace Poincare11a

open Finset Poincare11a.Cert

/-- The power sums of `lam` lie in the box `S0 ≤ 2^60 P4 ≤ S1`, `T0 ≤ 2^60 P6 ≤ T1`, `2^60 P3² ≤ S1`. -/
def InBox (S0 S1 T0 T1 : Int) {n : ℕ} (lam : Fin n → ℝ) : Prop :=
  (S0 : ℝ) ≤ (P60 : ℝ) * psum lam 4 ∧ (P60 : ℝ) * psum lam 4 ≤ S1 ∧
  (T0 : ℝ) ≤ (P60 : ℝ) * psum lam 6 ∧ (P60 : ℝ) * psum lam 6 ≤ T1 ∧ (P60 : ℝ) * psum lam 3 ^ 2 ≤ S1

/-- `U` bounds `E|S_θ|` on the open interval `iv` for every unit vector whose power sums lie in the box. -/
def IvBound (S0 S1 T0 T1 : Int) (iv : Ivl) (U : ℝ) : Prop :=
  U ≤ 1 ∧ ∀ θ ∈ Set.Ioo (thetaOf iv.TL) (thetaOf iv.TR), ∀ (n : ℕ) (lam : Fin n → ℝ),
    psum lam 2 = 1 → InBox S0 S1 T0 T1 lam → Phi (Real.sin θ) (Real.cos θ) lam ≤ U

lemma P60_pos : (0 : ℝ) < (P60 : ℝ) := by norm_num [P60]
lemma ONE_pos : (0 : ℝ) < (ONE : ℝ) := by norm_num [ONE]

lemma cos_facts (iv : Ivl) (hiv : iv.ok = true) (θ : ℝ) (hθ : θ ∈ Set.Ioo (thetaOf iv.TL) (thetaOf iv.TR)) :
    0 < Real.cos θ ∧ Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 :=
  ⟨(iv.VL_le hiv θ hθ).1, by linarith [Real.sin_sq_add_cos_sq θ]⟩

lemma ivBound_one (S0 S1 T0 T1 : Int) (iv : Ivl) (hiv : iv.ok = true) : IvBound S0 S1 T0 T1 iv 1 := by
  refine ⟨le_rfl, fun θ hθ n lam hl _ => ?_⟩
  obtain ⟨hc, hcm⟩ := cos_facts iv hiv θ hθ
  exact Phi_le_one hc hcm lam hl

/-- The bound `min(1, ub/ONE)` of one (leaf, interval) pair is valid. -/
lemma ivBound_poly (S0 S1 T0 T1 : Int) (iv : Ivl) (hiv : iv.ok = true) (hTR : iv.TR < P32)
    (p : Poly) (hp : p.posOK = true) :
    IvBound S0 S1 T0 T1 iv (min 1 (((imax (evalE (mkRunC p S0 S1 T0 T1) iv.w6l iv.w4l iv.w30l)
      (evalE (mkRunC p S0 S1 T0 T1) iv.w6h iv.w4h iv.w30h) : Int) : ℝ) / ONE)) := by
  refine ⟨min_le_left _ _, fun θ hθ n lam hl hbox => ?_⟩
  obtain ⟨hc, hcm⟩ := cos_facts iv hiv θ hθ
  refine le_min (Phi_le_one hc hcm lam hl) ?_
  obtain ⟨-, -, -, -, -, -, -, e6l, e4l, e30l, e6h, e4h, e30h⟩ := iv.ok_facts hiv
  have hVL := (iv.VL_le hiv θ hθ).2
  have hVH := iv.le_VH hiv θ hθ hTR
  have hV : (0 : ℝ) < VSC := by norm_num [VSC]
  set v := 4 / Real.cos θ ^ 2
  have hv1 : (iv.VL : ℝ) / VSC ≤ v := by rw [div_le_iff₀ hV]; linarith
  have hv2 : v ≤ (iv.VH : ℝ) / VSC := by rw [le_div_iff₀ hV]; linarith
  obtain ⟨b1, b2, b3, b4, b5⟩ := hbox
  have hP6 : 0 ≤ psum lam 6 := psum_even_nonneg lam 3
  have hD : (0 : ℝ) ≤ p.D := by exact_mod_cast (p.D_pos hp).le
  have h1 := Phi_le_Ereal hc hcm lam hl p hp
  have h2 := Ereal_le_max p hD (x4 := psum lam 4) (x3 := psum lam 3 ^ 2) hv1 hv2 hP6
  have hb4 : (S0 : ℝ) ≤ (P60 : ℝ) * psum lam 4 ∧ (P60 : ℝ) * psum lam 4 ≤ S1 := ⟨b1, b2⟩
  have hb3 : 0 ≤ psum lam 3 ^ 2 ∧ (P60 : ℝ) * psum lam 3 ^ 2 ≤ S1 := ⟨sq_nonneg _, b5⟩
  have hb6 : (T0 : ℝ) ≤ (P60 : ℝ) * psum lam 6 ∧ (P60 : ℝ) * psum lam 6 ≤ T1 := ⟨b3, b4⟩
  have hl' := Ereal_le_evalE p S0 S1 T0 T1 iv.VL (psum lam 4) (psum lam 3 ^ 2) (psum lam 6) hb4 hb3 hb6
  have hh' := Ereal_le_evalE p S0 S1 T0 T1 iv.VH (psum lam 4) (psum lam 3 ^ 2) (psum lam 6) hb4 hb3 hb6
  rw [← e6l, ← e4l, ← e30l] at hl'
  rw [← e6h, ← e4h, ← e30h] at hh'
  rw [imax_eq, Int.cast_max, le_div_iff₀ ONE_pos]
  calc Phi (Real.sin θ) (Real.cos θ) lam * ONE ≤ Ereal p v (psum lam 4) (psum lam 3 ^ 2) (psum lam 6) * ONE :=
        mul_le_mul_of_nonneg_right h1 ONE_pos.le
    _ ≤ max (Ereal p (iv.VL / VSC) (psum lam 4) (psum lam 3 ^ 2) (psum lam 6))
          (Ereal p (iv.VH / VSC) (psum lam 4) (psum lam 3 ^ 2) (psum lam 6)) * ONE :=
        mul_le_mul_of_nonneg_right h2 ONE_pos.le
    _ ≤ _ := by
        rw [max_mul_of_nonneg _ _ ONE_pos.le]
        exact max_le_max hl' hh'

lemma ivGain_eq (rc : RunC) (iv : Ivl) :
    (ivGain rc iv : ℝ) = (iv.LL : ℝ) * ONE * (1 - min 1 (((imax (evalE rc iv.w6l iv.w4l iv.w30l)
      (evalE rc iv.w6h iv.w4h iv.w30h) : Int) : ℝ) / ONE)) := by
  unfold ivGain
  rw [imin_eq]
  set ub := imax (evalE rc iv.w6l iv.w4l iv.w30l) (evalE rc iv.w6h iv.w4h iv.w30h)
  push_cast
  have h := ONE_pos
  have key : (ONE : ℝ) * min 1 ((ub : ℝ) / ONE) = min (ONE : ℝ) ub := by
    rw [mul_min_of_nonneg _ _ h.le, mul_one, mul_div_cancel₀ _ h.ne']
  rw [mul_assoc, mul_sub (ONE : ℝ), mul_one, key]

/-- Invariant of one run. -/
theorem runGain_sound (S0 S1 T0 T1 : Int) (orc : Option RunC)
    (horc : orc = none ∨ ∃ p : Poly, p.posOK = true ∧ orc = some (mkRunC p S0 S1 T0 T1)) :
    ∀ (len : ℕ) (ivs : List Ivl) (g : Int) (rest : List Ivl) (g' : Int),
      (∀ iv ∈ ivs, iv.ok = true) → runGain orc len ivs g = some (rest, g') →
      ∃ L : List (Ivl × ℝ), ivs = L.map Prod.fst ++ rest ∧ (∀ x ∈ L, IvBound S0 S1 T0 T1 x.1 x.2) ∧
        (g' : ℝ) = g + (L.map (fun x => (x.1.LL : ℝ) * ONE * (1 - x.2))).sum
  | 0, ivs, g, rest, g', _, h => by
    simp only [runGain, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, by simp, by simp⟩
  | len + 1, [], g, rest, g', _, h => by simp [runGain] at h
  | len + 1, iv :: ivs, g, rest, g', hok, h => by
    have hiv : iv.ok = true := hok iv (List.mem_cons_self ..)
    have hok' : ∀ x ∈ ivs, x.ok = true := fun x hx => hok x (List.mem_cons_of_mem _ hx)
    rcases horc with rfl | ⟨p, hp, rfl⟩
    · simp only [runGain] at h
      obtain ⟨L, h1, h2, h3⟩ := runGain_sound S0 S1 T0 T1 none (Or.inl rfl) len ivs g rest g' hok' h
      refine ⟨(iv, 1) :: L, by simp [h1], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ivBound_one S0 S1 T0 T1 iv hiv
        · exact h2 x hx
      · simp [h3]
    · simp only [runGain] at h
      cases hlt : ilt iv.TR P32
      · rw [hlt] at h; exact absurd h (by simp)
      · rw [hlt] at h
        have hTR : iv.TR < P32 := (ilt_iff _ _).1 hlt
        obtain ⟨L, h1, h2, h3⟩ := runGain_sound S0 S1 T0 T1 (some (mkRunC p S0 S1 T0 T1))
          (Or.inr ⟨p, hp, rfl⟩) len ivs _ rest g' hok' h
        refine ⟨(iv, min 1 (((imax (evalE (mkRunC p S0 S1 T0 T1) iv.w6l iv.w4l iv.w30l)
          (evalE (mkRunC p S0 S1 T0 T1) iv.w6h iv.w4h iv.w30h) : Int) : ℝ) / ONE)) :: L,
          by simp [h1], ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ivBound_poly S0 S1 T0 T1 iv hiv hTR p hp
          · exact h2 x hx
        · rw [h3]; push_cast; rw [ivGain_eq]; simp; ring

lemma LibT.get_posOK : ∀ (lib : LibT) (j : ℕ) (p : Poly), lib.allPos = true → lib.get j = some p → p.posOK = true
  | .nil, j, p, _, h => by simp [LibT.get] at h
  | .leaf q, j, p, hl, h => by
    simp only [LibT.get] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h; exact hl
  | .node l r, j, p, hl, h => by
    simp only [LibT.allPos, Bool.and_eq_true] at hl
    simp only [LibT.get] at h
    split_ifs at h
    · exact LibT.get_posOK l _ p hl.1 h
    · exact LibT.get_posOK r _ p hl.2 h

/-- Invariant of the run list of a leaf. -/
theorem runsGain_sound (lib : LibT) (hlib : lib.allPos = true) (S0 S1 T0 T1 : Int) :
    ∀ (runs : List (Int × Nat)) (ivs : List Ivl) (g : Int) (rest : List Ivl) (g' : Int),
      (∀ iv ∈ ivs, iv.ok = true) → runsGain lib S0 S1 T0 T1 runs ivs g = some (rest, g') →
      ∃ L : List (Ivl × ℝ), ivs = L.map Prod.fst ++ rest ∧ (∀ x ∈ L, IvBound S0 S1 T0 T1 x.1 x.2) ∧
        (g' : ℝ) = g + (L.map (fun x => (x.1.LL : ℝ) * ONE * (1 - x.2))).sum
  | [], ivs, g, rest, g', _, h => by
    simp only [runsGain, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, by simp, by simp⟩
  | (j, len) :: rs, ivs, g, rest, g', hok, h => by
    have key : ∀ o : Option RunC, (o = none ∨ ∃ p : Poly, p.posOK = true ∧ o = some (mkRunC p S0 S1 T0 T1)) →
        (match runGain o len ivs g with
          | none => none
          | some (ivs', g') => runsGain lib S0 S1 T0 T1 rs ivs' g') = some (rest, g') →
        ∃ L : List (Ivl × ℝ), ivs = L.map Prod.fst ++ rest ∧ (∀ x ∈ L, IvBound S0 S1 T0 T1 x.1 x.2) ∧
          (g' : ℝ) = g + (L.map (fun x => (x.1.LL : ℝ) * ONE * (1 - x.2))).sum := by
      intro o horc h
      cases h1 : runGain o len ivs g with
      | none => rw [h1] at h; simp at h
      | some r =>
        obtain ⟨ivs', g1⟩ := r
        rw [h1] at h
        simp only at h
        obtain ⟨L1, e1, b1, s1⟩ := runGain_sound S0 S1 T0 T1 o horc len ivs g ivs' g1 hok h1
        have hok' : ∀ iv ∈ ivs', iv.ok = true := fun iv hiv => hok iv (by rw [e1]; simp [hiv])
        obtain ⟨L2, e2, b2, s2⟩ := runsGain_sound lib hlib S0 S1 T0 T1 rs ivs' g1 rest g' hok' h
        refine ⟨L1 ++ L2, by rw [e1, e2]; simp, ?_, ?_⟩
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact b1 x hx
          · exact b2 x hx
        · rw [s2, s1]; simp; ring
    rcases j with jn | jn
    · simp only [runsGain] at h
      cases hg : lib.get jn with
      | none => simp [hg] at h
      | some p =>
        simp only [hg, Option.map_some] at h
        exact key _ (Or.inr ⟨p, LibT.get_posOK lib jn p hlib hg, rfl⟩) h
    · simp only [runsGain] at h
      exact key none (Or.inl rfl) h

/-! ### Leaves -/

/-- Closed dyadic square `[i/2^l, (i+1)/2^l] × [k/2^l, (k+1)/2^l]` in the `(P4, P6)`-plane. -/
def InSq (l i k : ℕ) (s t : ℝ) : Prop :=
  (i : ℝ) / 2 ^ l ≤ s ∧ s ≤ ((i : ℝ) + 1) / 2 ^ l ∧ (k : ℝ) / 2 ^ l ≤ t ∧ t ≤ ((k : ℝ) + 1) / 2 ^ l

/-- The region of paper Lemma 3.4 in squared form: `s² ≤ t ≤ s^{3/2}`. -/
def InR (s t : ℝ) : Prop := 0 ≤ s ∧ 0 ≤ t ∧ s ^ 2 ≤ t ∧ t ^ 2 ≤ s ^ 3

lemma two_pow_sub_mul {l m : ℕ} (h : l ≤ m) : (2 : ℝ) ^ (m - l) * 2 ^ l = 2 ^ m := by
  rw [← pow_add, Nat.sub_add_cancel h]

/-- Soundness of one leaf check: per-interval bounds for every unit vector in the square, with the gain inequality. -/
theorem checkLeaf_sound (lib : LibT) (hlib : lib.allPos = true) (ivs : List Ivl) (hivs : ∀ iv ∈ ivs, iv.ok = true)
    (l i k R : ℕ) (runs : List (Int × Nat)) (h : checkLeaf lib ivs l i k R runs = true)
    {n : ℕ} (lam : Fin n → ℝ) (hl : psum lam 2 = 1) (hsq : InSq l i k (psum lam 4) (psum lam 6)) :
    ∃ L : List (Ivl × ℝ), ivs = L.map Prod.fst ∧
      (∀ x ∈ L, x.2 ≤ 1 ∧ ∀ θ ∈ Set.Ioo (thetaOf x.1.TL) (thetaOf x.1.TR),
        Phi (Real.sin θ) (Real.cos θ) lam ≤ x.2) ∧
      (1507965 : ℝ) / 10000000 ≤ (L.map (fun x => (x.1.LL : ℝ) / P64 * (1 - x.2))).sum := by
  unfold checkLeaf at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl30, hR⟩, hrun⟩ := h
  set sh : ℕ := 2 ^ (60 - l)
  set S0 : Int := ((i * sh : ℕ) : Int)
  set S1 : Int := (((i + 1) * sh : ℕ) : Int)
  set T0 : Int := imax ((k * sh : ℕ) : Int) ((i * i * 2 ^ (60 - 2 * l) : ℕ) : Int)
  set T1 : Int := imin (((k + 1) * sh : ℕ) : Int) (R : Int)
  cases hg : runsGain lib S0 S1 T0 T1 runs ivs 0 with
  | none => rw [hg] at hrun; simp at hrun
  | some r =>
    obtain ⟨rest, g⟩ := r
    rw [hg] at hrun
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hrun
    obtain ⟨hrest, hgain⟩ := hrun
    subst hrest
    obtain ⟨L, hL, hb, hs⟩ := runsGain_sound lib hlib S0 S1 T0 T1 runs ivs 0 [] g hivs hg
    refine ⟨L, by simpa using hL, ?_, ?_⟩
    · -- the box contains the power sums of lam
      have hbox : InBox S0 S1 T0 T1 lam := by
        obtain ⟨q1, q2, q3, q4⟩ := hsq
        have hu : (0 : ℝ) < 2 ^ l := by positivity
        have hsh : (sh : ℝ) * 2 ^ l = (P60 : ℝ) := by
          simp only [sh]; push_cast; rw [two_pow_sub_mul (by omega)]; norm_num [P60]
        have hsh2 : ((2 ^ (60 - 2 * l) : ℕ) : ℝ) * (2 ^ l) ^ 2 = (P60 : ℝ) := by
          push_cast; rw [← pow_mul, mul_comm l 2, two_pow_sub_mul (by omega)]; norm_num [P60]
        have hP4 := psum4_sq_le lam
        have hP3 := psum3_sq_le lam
        have hP6 := psum6_sq_le lam
        rw [hl, one_mul] at hP4 hP3
        have hP4n : 0 ≤ psum lam 4 := psum_even_nonneg lam 2
        have hP6n : 0 ≤ psum lam 6 := psum_even_nonneg lam 3
        have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        -- scaled forms of the square
        have a1 : (i : ℝ) * sh ≤ P60 * psum lam 4 := by
          rw [← hsh]; have := (div_le_iff₀ hu).1 q1; nlinarith [Nat.cast_nonneg (α := ℝ) sh]
        have a2 : (P60 : ℝ) * psum lam 4 ≤ ((i : ℝ) + 1) * sh := by
          rw [← hsh]; have := (le_div_iff₀ hu).1 q2; nlinarith [Nat.cast_nonneg (α := ℝ) sh]
        have a3 : (k : ℝ) * sh ≤ P60 * psum lam 6 := by
          rw [← hsh]; have := (div_le_iff₀ hu).1 q3; nlinarith [Nat.cast_nonneg (α := ℝ) sh]
        have a4 : (P60 : ℝ) * psum lam 6 ≤ ((k : ℝ) + 1) * sh := by
          rw [← hsh]; have := (le_div_iff₀ hu).1 q4; nlinarith [Nat.cast_nonneg (α := ℝ) sh]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp only [S0]; push_cast; exact a1
        · simp only [S1]; push_cast; exact a2
        · simp only [T0, imax_eq]; push_cast
          refine max_le a3 ?_
          -- i² 2^(60-2l) ≤ 2^60 P4² ≤ 2^60 P6
          have hi4 : (i : ℝ) ≤ 2 ^ l * psum lam 4 := by have := (div_le_iff₀ hu).1 q1; linarith
          have : (i : ℝ) * i ≤ (2 ^ l) ^ 2 * psum lam 4 ^ 2 := by nlinarith
          have e : (P60 : ℝ) * psum lam 6 = ((2 ^ (60 - 2 * l) : ℕ) : ℝ) * ((2 ^ l) ^ 2 * psum lam 6) := by
            rw [← hsh2]; ring
          rw [e]
          have h2pos : (0 : ℝ) ≤ ((2 ^ (60 - 2 * l) : ℕ) : ℝ) := Nat.cast_nonneg _
          push_cast at h2pos ⊢
          nlinarith [mul_le_mul_of_nonneg_left hP4 (by positivity : (0 : ℝ) ≤ (2 ^ l) ^ 2)]
        · simp only [T1, imin_eq]; push_cast
          refine le_min a4 ?_
          -- (2^60 P6)² ≤ 2^120 P4³ ≤ S1³ / 2^60 ≤ R²
          have hR' : (((i + 1) * sh : ℕ) : ℝ) ^ 3 ≤ (R : ℝ) ^ 2 * P60 := by
            have h1 : ((S1 : ℤ) : ℝ) * S1 * S1 ≤ ((R : ℤ) : ℝ) * (R : ℤ) * (P60 : ℤ) := by exact_mod_cast hR
            have h2 : ((S1 : ℤ) : ℝ) = (((i + 1) * sh : ℕ) : ℝ) := by simp only [S1]; push_cast; ring
            rw [h2] at h1
            have h3 : ((R : ℤ) : ℝ) = (R : ℝ) := by push_cast; ring
            rw [h3] at h1
            nlinarith [h1]
          have hS1 : (P60 : ℝ) * psum lam 4 ≤ (((i + 1) * sh : ℕ) : ℝ) := by push_cast; exact a2
          have hP60 : (0 : ℝ) < P60 := P60_pos
          have key : ((P60 : ℝ) * psum lam 6) ^ 2 * P60 ≤ (R : ℝ) ^ 2 * P60 := by
            calc ((P60 : ℝ) * psum lam 6) ^ 2 * P60 = P60 ^ 3 * psum lam 6 ^ 2 := by ring
              _ ≤ P60 ^ 3 * psum lam 4 ^ 3 := mul_le_mul_of_nonneg_left hP6 (by positivity)
              _ = ((P60 : ℝ) * psum lam 4) ^ 3 := by ring
              _ ≤ (((i + 1) * sh : ℕ) : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hS1 3
              _ ≤ (R : ℝ) ^ 2 * P60 := hR'
          have key2 : ((P60 : ℝ) * psum lam 6) ^ 2 ≤ (R : ℝ) ^ 2 := le_of_mul_le_mul_right key hP60
          exact (sq_le_sq₀ (mul_nonneg P60_pos.le hP6n) (Nat.cast_nonneg R)).1 key2
        · simp only [S1]; push_cast
          have : (P60 : ℝ) * psum lam 3 ^ 2 ≤ P60 * psum lam 4 :=
            mul_le_mul_of_nonneg_left hP3 P60_pos.le
          linarith
      intro x hx
      exact ⟨(hb x hx).1, fun θ hθ => (hb x hx).2 θ hθ n lam hl hbox⟩
    · -- gain inequality
      have hthr := (ile_iff _ _).1 hgain
      rw [THR_eq] at hthr
      have hthr' : (1507965 : ℝ) * P64 * ONE ≤ (g : ℝ) * 10000000 := by exact_mod_cast hthr
      rw [hs] at hthr'
      simp only [Int.cast_zero, zero_add] at hthr'
      have hsum : (L.map (fun x => (x.1.LL : ℝ) * ONE * (1 - x.2))).sum =
          (P64 : ℝ) * ONE * (L.map (fun x => (x.1.LL : ℝ) / P64 * (1 - x.2))).sum := by
        rw [← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left (fun x _ => ?_)
        have : (P64 : ℝ) ≠ 0 := by norm_num [P64]
        field_simp
      rw [hsum] at hthr'
      have hpos : (0 : ℝ) < (P64 : ℝ) * ONE := mul_pos (by norm_num [P64]) ONE_pos
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10000000)]
      nlinarith [hpos]

/-! ### The quadtree -/

theorem tree_sound (lib : LibT) (ivs : List Ivl) :
    ∀ (t : QT) (l i k : ℕ), t.OK lib ivs l i k → ∀ s τ : ℝ, InSq l i k s τ → InR s τ →
      ∃ (l' i' k' R : ℕ) (runs : List (Int × Nat)), checkLeaf lib ivs l' i' k' R runs = true ∧ InSq l' i' k' s τ
  | .out, l, i, k, h, s, τ, hsq, hR => by
    exfalso
    simp only [QT.OK, outsideOK, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨q1, q2, q3, q4⟩ := hsq
    obtain ⟨r1, r2, r3, r4⟩ := hR
    have hu : (0 : ℝ) < 2 ^ l := by positivity
    rcases h with h | h
    · have h' : ((k : ℝ) + 1) * 2 ^ l < (i : ℝ) * i := by exact_mod_cast h
      -- τ ≤ (k+1)/2^l < i²/2^{2l} ≤ s² ≤ τ
      have e1 : τ * 2 ^ l ≤ (k : ℝ) + 1 := (le_div_iff₀ hu).1 q4
      have e2 : (i : ℝ) ≤ s * 2 ^ l := (div_le_iff₀ hu).1 q1
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have : (i : ℝ) * i ≤ (s * 2 ^ l) * (s * 2 ^ l) := mul_le_mul e2 e2 hi0 (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right e1 hu.le, mul_le_mul_of_nonneg_right r3 (by positivity : (0:ℝ) ≤ (2 ^ l) ^ 2)]
    · have h' : ((i : ℝ) + 1) * (i + 1) * (i + 1) < (k : ℝ) * k * 2 ^ l := by exact_mod_cast h
      have e1 : s * 2 ^ l ≤ (i : ℝ) + 1 := (le_div_iff₀ hu).1 q2
      have e2 : (k : ℝ) ≤ τ * 2 ^ l := (div_le_iff₀ hu).1 q3
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hs3 : (s * 2 ^ l) ^ 3 ≤ ((i : ℝ) + 1) ^ 3 := pow_le_pow_left₀ (by positivity) e1 3
      have hk2 : (k : ℝ) * k ≤ (τ * 2 ^ l) ^ 2 := by nlinarith
      -- k² 2^l > (i+1)³ ≥ (s 2^l)³ = s³ 2^{3l} ≥ τ² 2^{3l} ≥ k² 2^l
      have : (τ * 2 ^ l) ^ 2 * 2 ^ l ≤ (s * 2 ^ l) ^ 3 := by
        have := mul_le_mul_of_nonneg_right r4 (by positivity : (0 : ℝ) ≤ (2 ^ l) ^ 3)
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hk2 hu.le]
  | .leaf R runs, l, i, k, h, s, τ, hsq, _ => ⟨l, i, k, R, runs, h, hsq⟩
  | .node a b c d, l, i, k, h, s, τ, hsq, hR => by
    obtain ⟨ha, hb, hc, hd⟩ := h
    obtain ⟨q1, q2, q3, q4⟩ := hsq
    have hu : (0 : ℝ) < 2 ^ (l + 1) := by positivity
    have e : ∀ j : ℕ, (j : ℝ) / 2 ^ l = (2 * j : ℕ) / 2 ^ (l + 1) := fun j => by
      push_cast; rw [pow_succ]; field_simp
    have e' : ∀ j : ℕ, ((j : ℝ) + 1) / 2 ^ l = ((2 * j + 1 : ℕ) + 1) / 2 ^ (l + 1) := fun j => by
      push_cast; rw [pow_succ]; field_simp; ring
    rw [e i] at q1; rw [e' i] at q2; rw [e k] at q3; rw [e' k] at q4
    have mid : ∀ j : ℕ, ((2 * j : ℕ) : ℝ) + 1 = ((2 * j + 1 : ℕ) : ℝ) := fun j => by push_cast; ring
    rcases le_total s ((((2 * i : ℕ) : ℝ) + 1) / 2 ^ (l + 1)) with hs | hs <;>
    rcases le_total τ ((((2 * k : ℕ) : ℝ) + 1) / 2 ^ (l + 1)) with ht | ht
    · exact tree_sound lib ivs a (l + 1) (2 * i) (2 * k) ha s τ ⟨q1, hs, q3, ht⟩ hR
    · exact tree_sound lib ivs b (l + 1) (2 * i) (2 * k + 1) hb s τ
        ⟨q1, hs, by rw [← mid]; exact ht, q4⟩ hR
    · exact tree_sound lib ivs c (l + 1) (2 * i + 1) (2 * k) hc s τ
        ⟨by rw [← mid]; exact hs, q2, q3, ht⟩ hR
    · exact tree_sound lib ivs d (l + 1) (2 * i + 1) (2 * k + 1) hd s τ
        ⟨by rw [← mid]; exact hs, q2, by rw [← mid]; exact ht, q4⟩ hR

/-! ### The whole certificate -/

lemma chain_facts : ∀ (t : Int) (ivs : List Ivl), chainOK t ivs = true →
    (∀ iv ∈ ivs, iv.ok = true) ∧
      (ivs.map (fun iv => thetaOf iv.TR - thetaOf iv.TL)).sum = thetaOf P32 - thetaOf t
  | t, [], h => by
    simp only [chainOK, decide_eq_true_eq] at h
    subst h; simp
  | t, iv :: ivs, h => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨b1, b2⟩ := chain_facts iv.TR ivs h3
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact h2
      · exact b1 x hx
    · simp only [List.map_cons, List.sum_cons, b2, h1]; ring

lemma sum_width_bound : ∀ (L : List (Ivl × ℝ)), (∀ x ∈ L, x.1.ok = true ∧ x.2 ≤ 1) →
    (L.map (fun x => (thetaOf x.1.TR - thetaOf x.1.TL) * x.2)).sum ≤
      (L.map (fun x => thetaOf x.1.TR - thetaOf x.1.TL)).sum -
        (L.map (fun x => (x.1.LL : ℝ) / P64 * (1 - x.2))).sum
  | [], _ => by simp
  | x :: L, h => by
    have hx := h x (List.mem_cons_self ..)
    have ih := sum_width_bound L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hw := x.1.LL_le_width hx.1
    have h1 : 0 ≤ 1 - x.2 := by linarith [hx.2]
    have : (x.1.LL : ℝ) / P64 * (1 - x.2) ≤ (thetaOf x.1.TR - thetaOf x.1.TL) * (1 - x.2) :=
      mul_le_mul_of_nonneg_right hw h1
    simp only [List.map_cons, List.sum_cons]
    nlinarith

/-- The certificate gives, for every unit vector `λ` in every dimension, per-interval bounds `U_i ≤ 1` of
`E|S_θ|` on the open θ-intervals of the partition `ivs`, with `∑_i |I_i| U_i ≤ 71/50` (paper Proposition 4.1). -/
theorem cert_sound (lib : LibT) (hlib : lib.allPos = true) (ivs : List Ivl) (hpart : partOK ivs = true)
    (t : QT) (ht : t.OK lib ivs 0 0 0) {n : ℕ} (lam : Fin n → ℝ) (hl : psum lam 2 = 1) :
    ∃ L : List (Ivl × ℝ), ivs = L.map Prod.fst ∧
      (∀ x ∈ L, x.2 ≤ 1 ∧ ∀ θ ∈ Set.Ioo (thetaOf x.1.TL) (thetaOf x.1.TR),
        Phi (Real.sin θ) (Real.cos θ) lam ≤ x.2) ∧
      (L.map (fun x => (thetaOf x.1.TR - thetaOf x.1.TL) * x.2)).sum ≤ 71 / 50 := by
  simp only [partOK, Bool.and_eq_true, decide_eq_true_eq] at hpart
  obtain ⟨-, hchain⟩ := hpart
  obtain ⟨hivs, hsum⟩ := chain_facts 0 ivs hchain
  rw [thetaOf_P32, thetaOf_zero, sub_zero] at hsum
  -- the power sums of λ lie in R ∩ [0,1]²
  have hP4 := psum4_sq_le lam
  have hP6 := psum6_sq_le lam
  rw [hl, one_mul] at hP4
  have hP4n : 0 ≤ psum lam 4 := psum_even_nonneg lam 2
  have hP6n : 0 ≤ psum lam 6 := psum_even_nonneg lam 3
  have hP41 : psum lam 4 ≤ 1 := psum4_le_one lam hl
  have hP61 : psum lam 6 ≤ 1 := by
    have : psum lam 6 ^ 2 ≤ 1 := hP6.trans (pow_le_one₀ hP4n hP41)
    nlinarith
  have hsq : InSq 0 0 0 (psum lam 4) (psum lam 6) := by simp [InSq]; exact ⟨hP4n, hP41, hP6n, hP61⟩
  have hR : InR (psum lam 4) (psum lam 6) := ⟨hP4n, hP6n, hP4, hP6⟩
  obtain ⟨l', i', k', R, runs, hleaf, hsq'⟩ := tree_sound lib ivs t 0 0 0 ht _ _ hsq hR
  obtain ⟨L, hL, hb, hg⟩ := checkLeaf_sound lib hlib ivs hivs l' i' k' R runs hleaf lam hl hsq'
  refine ⟨L, hL, hb, ?_⟩
  have hok : ∀ x ∈ L, x.1.ok = true ∧ x.2 ≤ 1 := fun x hx =>
    ⟨hivs x.1 (by rw [hL]; exact List.mem_map_of_mem hx), (hb x hx).1⟩
  have h1 := sum_width_bound L hok
  have h2 : (L.map (fun x => thetaOf x.1.TR - thetaOf x.1.TL)).sum = Real.pi / 2 := by
    rw [← hsum, hL, List.map_map]; rfl
  rw [h2] at h1
  have hpi := Real.pi_lt_d6
  linarith

end Poincare11a
