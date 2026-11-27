import FormalConjectures.ErdosProblems.«660»

namespace OMA660

open Finset

/-- Core inequality. Chain points `P = (p, hP)`, `Q = (q, hQ)`, `S = (s, hS)` lie (in this order)
on a concave chain from `a = (0, 0)` to `b = (D, 0)`, with `|Qb| ≤ D`. If `P` is not higher than
`S`, then `|QS| < |PS|`. -/
theorem core_ineq (p q s hP hQ hS D : ℝ) (hp : 0 ≤ p) (hpq : p < q) (hqs : q < s)
    (hP0 : 0 ≤ hP) (hQ0 : 0 < hQ) (hPS : hP ≤ hS)
    (h1 : (hQ - hP) * (s - p) > (hS - hP) * (q - p))
    (h2 : hS * (D - q) > hQ * (D - s))
    (h3 : hP * q ≥ hQ * p)
    (h4 : (D - q) ^ 2 + hQ ^ 2 ≤ D ^ 2) :
    (s - q) ^ 2 + (hQ - hS) ^ 2 < (s - p) ^ 2 + (hS - hP) ^ 2 := by
  have hq : 0 < q := lt_of_le_of_lt hp hpq
  have hsp : 0 < s - p := by linarith
  have hqp : 0 < q - p := by linarith
  have hQP : hP < hQ := by
    by_contra hcon
    push Not at hcon
    have : (hQ - hP) * (s - p) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hsp.le
    have : 0 ≤ (hS - hP) * (q - p) := mul_nonneg (by linarith) hqp.le
    linarith
  rcases le_or_gt hQ hS with hQS | hQS
  · -- Q is not higher than S
    have e1 : (hQ - hS) ^ 2 < (hS - hP) ^ 2 := by nlinarith
    have e2 : (s - q) ^ 2 < (s - p) ^ 2 := by nlinarith
    linarith
  · -- Q is higher than S
    have A : hQ ^ 2 ≤ q * (2 * D - q) := by nlinarith
    have A' : hQ ^ 2 * (hQ - hS) ≤ q * (2 * D - q) * (hQ - hS) :=
      mul_le_mul_of_nonneg_right A (by linarith)
    have br : q * (2 * s * hQ - q * hQ - q * hS) - hQ ^ 2 * (hQ - hS) > 0 := by
      have : q * (hS * (D - q)) > q * (hQ * (D - s)) := mul_lt_mul_of_pos_left h2 hq
      nlinarith
    -- (s hQ - q hS)^2 > hQ^2 ((s - q)^2 + (hQ - hS)^2)
    have key1 : (s * hQ - q * hS) ^ 2 > hQ ^ 2 * ((s - q) ^ 2 + (hQ - hS) ^ 2) := by
      have hid : (s * hQ - q * hS) ^ 2 - hQ ^ 2 * ((s - q) ^ 2 + (hQ - hS) ^ 2)
          = (hQ - hS) * (q * (2 * s * hQ - q * hQ - q * hS) - hQ ^ 2 * (hQ - hS)) := by ring
      have : 0 < (hQ - hS) * (q * (2 * s * hQ - q * hQ - q * hS) - hQ ^ 2 * (hQ - hS)) :=
        mul_pos (by linarith) br
      linarith
    -- the point X on PQ at height hS
    set g := (hS - hP) / (hQ - hP) with hg
    have hQPpos : 0 < hQ - hP := by linarith
    have hg0 : 0 ≤ g := div_nonneg (by linarith) hQPpos.le
    have hg1 : g < 1 := (div_lt_one hQPpos).mpr (by linarith)
    have hgdef : g * (hQ - hP) = hS - hP := by rw [hg]; field_simp
    have c1 : (s - p) ^ 2 + (hS - hP) ^ 2 ≥ (s - p - g * (q - p)) ^ 2 := by
      have : (hS - hP) ^ 2 ≥ 0 := sq_nonneg _
      have h5 : 2 * (s - p) ≥ g * (q - p) := by nlinarith
      nlinarith [mul_nonneg hg0 hqp.le]
    -- p + g (q - p) ≤ q hS / hQ, i.e. hQ (p + g (q - p)) ≤ q hS
    have c2 : hQ * (p + g * (q - p)) ≤ q * hS := by
      have h6 : (hQ - hP) * (hQ * (p + g * (q - p)) - q * hS) ≤ 0 := by
        have : (hQ - hP) * (hQ * (p + g * (q - p)) - q * hS)
            = hQ * p * (hQ - hP) + hQ * (q - p) * (hS - hP) - q * hS * (hQ - hP) := by
          rw [← hgdef]; ring
        rw [this]
        have e : hQ * p * (hQ - hP) + hQ * (q - p) * (hS - hP) - q * hS * (hQ - hP)
            = (hQ - hS) * (hQ * p - q * hP) := by ring
        rw [e]
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      by_contra hcon
      push Not at hcon
      have : 0 < (hQ - hP) * (hQ * (p + g * (q - p)) - q * hS) := mul_pos hQPpos (by linarith)
      linarith
    have c3 : 0 ≤ s * hQ - q * hS := by
      have e1 := mul_lt_mul_of_pos_right hqs hQ0
      have e2 := mul_le_mul_of_nonneg_left hQS.le hq.le
      linarith
    -- (s - p - g (q - p)) hQ ≥ s hQ - q hS ≥ 0
    have c4 : hQ * (s - p - g * (q - p)) ≥ s * hQ - q * hS := by
      have e : hQ * (s - p - g * (q - p)) = s * hQ - hQ * (p + g * (q - p)) := by ring
      linarith
    have c5 : hQ ^ 2 * (s - p - g * (q - p)) ^ 2 ≥ (s * hQ - q * hS) ^ 2 := by
      have := mul_le_mul c4 c4 c3 (by linarith)
      have e1 : hQ * (s - p - g * (q - p)) * (hQ * (s - p - g * (q - p)))
          = hQ ^ 2 * (s - p - g * (q - p)) ^ 2 := by ring
      have e2 : (s * hQ - q * hS) * (s * hQ - q * hS) = (s * hQ - q * hS) ^ 2 := by ring
      linarith
    have c6 : hQ ^ 2 * ((s - p) ^ 2 + (hS - hP) ^ 2) > hQ ^ 2 * ((s - q) ^ 2 + (hQ - hS) ^ 2) := by
      have := mul_le_mul_of_nonneg_left c1 (sq_nonneg hQ)
      linarith
    exact lt_of_mul_lt_mul_left (by linarith) (sq_nonneg hQ)


abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- squared distance in coordinates -/
def sq (x y : Pt) : ℝ := (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2

lemma dist_sq_eq (x y : Pt) : dist x y ^ 2 = sq x y := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [sq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

lemma dist_eq_sqrt (x y : Pt) : dist x y = Real.sqrt (sq x y) := by
  rw [← dist_sq_eq, Real.sqrt_sq dist_nonneg]

lemma sq_nonneg' (x y : Pt) : 0 ≤ sq x y := by unfold sq; positivity

lemma sq_comm (x y : Pt) : sq x y = sq y x := by unfold sq; ring

lemma eq_of_sq_eq_zero {x y : Pt} (h : sq x y = 0) : x = y := by
  have h0 : (x 0 - y 0) ^ 2 = 0 := by unfold sq at h; nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
  have h1 : (x 1 - y 1) ^ 2 = 0 := by unfold sq at h; nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
  ext i
  fin_cases i
  · simpa [sub_eq_zero] using h0
  · simpa [sub_eq_zero] using h1

/-- along-coordinate (scaled by |ab|) -/
def T (a b x : Pt) : ℝ := (x 0 - a 0) * (b 0 - a 0) + (x 1 - a 1) * (b 1 - a 1)
/-- height-coordinate (scaled by |ab|) -/
def H (a b x : Pt) : ℝ := (b 0 - a 0) * (x 1 - a 1) - (b 1 - a 1) * (x 0 - a 0)

lemma key_id (a b x y : Pt) :
    sq a b * sq x y = (T a b x - T a b y) ^ 2 + (H a b x - H a b y) ^ 2 := by
  unfold sq T H; ring

lemma T_a (a b : Pt) : T a b a = 0 := by unfold T; ring
lemma H_a (a b : Pt) : H a b a = 0 := by unfold H; ring
lemma T_b (a b : Pt) : T a b b = sq a b := by unfold T sq; ring
lemma H_b (a b : Pt) : H a b b = 0 := by unfold H; ring

lemma H_swap (a b x : Pt) : H b a x = - H a b x := by unfold H; ring

lemma T_comb (a b u v : Pt) (c : ℝ) : T a b (u + c • (v - u)) = T a b u + c * (T a b v - T a b u) := by
  unfold T; simp; ring
lemma H_comb (a b u v : Pt) (c : ℝ) : H a b (u + c • (v - u)) = H a b u + c * (H a b v - H a b u) := by
  unfold H; simp; ring

lemma eq_of_TH {a b x y : Pt} (hK : 0 < sq a b) (hT : T a b x = T a b y) (hH : H a b x = H a b y) :
    x = y := by
  apply eq_of_sq_eq_zero
  have := key_id a b x y
  rw [hT, hH] at this
  have h2 : sq a b * sq x y = 0 := by rw [this]; ring
  rcases mul_eq_zero.mp h2 with h | h
  · linarith
  · exact h

/-- A point `y` with positive height lying weakly below a point `w` of the hull of `S \ {y}` at the
same `T`-coordinate is itself in that hull (it lies on the vertical segment from the base `ab`). -/
lemma mem_hull_of_below {S : Set Pt} {a b y w : Pt} (hK : 0 < sq a b) (ha : a ∈ S) (hb : b ∈ S)
    (hya : y ≠ a) (hyb : y ≠ b) (hw : w ∈ convexHull ℝ (S \ {y}))
    (hTw : T a b w = T a b y) (hHy : 0 < H a b y) (hHw : H a b y ≤ H a b w)
    (hT0 : 0 ≤ T a b y) (hTK : T a b y ≤ sq a b) :
    y ∈ convexHull ℝ (S \ {y}) := by
  set μ := T a b y / sq a b with hμ
  set B : Pt := a + μ • (b - a) with hB
  have hμ0 : 0 ≤ μ := div_nonneg hT0 hK.le
  have hμ1 : μ ≤ 1 := (div_le_one hK).mpr hTK
  have hBmem : B ∈ convexHull ℝ (S \ {y}) := by
    have hab : segment ℝ a b ⊆ convexHull ℝ (S \ {y}) :=
      (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ ⟨ha, hya.symm⟩)
        (subset_convexHull ℝ _ ⟨hb, hyb.symm⟩)
    apply hab
    rw [segment_eq_image']
    exact ⟨μ, ⟨hμ0, hμ1⟩, rfl⟩
  have hTB : T a b B = T a b y := by
    rw [hB, T_comb, T_a, T_b, hμ]; field_simp; ring
  have hHB : H a b B = 0 := by rw [hB, H_comb, H_a, H_b]; ring
  set ν := H a b y / H a b w with hν
  have hHw0 : 0 < H a b w := lt_of_lt_of_le hHy hHw
  have hν0 : 0 ≤ ν := div_nonneg hHy.le hHw0.le
  have hν1 : ν ≤ 1 := (div_le_one hHw0).mpr hHw
  have hy : y = B + ν • (w - B) := by
    apply eq_of_TH hK
    · rw [T_comb, hTB, hTw]; ring
    · rw [H_comb, hHB, hν]; field_simp; ring
  have hseg : segment ℝ B w ⊆ convexHull ℝ (S \ {y}) :=
    (convex_convexHull ℝ _).segment_subset hBmem hw
  have hmem : B + ν • (w - B) ∈ convexHull ℝ (S \ {y}) := by
    apply hseg
    rw [segment_eq_image']
    exact ⟨ν, ⟨hν0, hν1⟩, rfl⟩
  convert hmem using 1


section Setup

variable {S : Finset Pt} {a b : Pt}

lemma notMem_hull (hconv : ConvexIndependent ℝ ((↑) : ↥(S : Set Pt) → Pt)) {x : Pt} (hx : x ∈ S) :
    x ∉ convexHull ℝ ((S : Set Pt) \ {x}) :=
  (convexIndependent_set_iff_notMem_convexHull_sdiff.mp hconv) x hx

variable (hconv : ConvexIndependent ℝ ((↑) : ↥(S : Set Pt) → Pt)) (ha : a ∈ S) (hb : b ∈ S)
  (hK : 0 < sq a b) (hmax : ∀ x ∈ S, ∀ y ∈ S, sq x y ≤ sq a b)
include hconv ha hb hK hmax

lemma lens_a {x : Pt} (hx : x ∈ S) : T a b x ^ 2 + H a b x ^ 2 ≤ sq a b ^ 2 := by
  have h := key_id a b a x
  rw [T_a, H_a] at h
  have := mul_le_mul_of_nonneg_left (hmax a ha x hx) hK.le
  nlinarith

lemma lens_b {x : Pt} (hx : x ∈ S) : (sq a b - T a b x) ^ 2 + H a b x ^ 2 ≤ sq a b ^ 2 := by
  have h := key_id a b b x
  rw [T_b, H_b] at h
  have := mul_le_mul_of_nonneg_left (hmax b hb x hx) hK.le
  nlinarith

lemma T_nonneg {x : Pt} (hx : x ∈ S) : 0 ≤ T a b x := by
  have := lens_b hconv ha hb hK hmax hx
  nlinarith [sq_nonneg (H a b x)]

lemma T_le {x : Pt} (hx : x ∈ S) : T a b x ≤ sq a b := by
  have := lens_a hconv ha hb hK hmax hx
  nlinarith [sq_nonneg (H a b x)]

lemma T_pos_of_H {x : Pt} (hx : x ∈ S) (hH : H a b x ≠ 0) : 0 < T a b x := by
  have := lens_b hconv ha hb hK hmax hx
  have h2 : 0 < H a b x ^ 2 := by positivity
  nlinarith

lemma T_lt_of_H {x : Pt} (hx : x ∈ S) (hH : H a b x ≠ 0) : T a b x < sq a b := by
  have := lens_a hconv ha hb hK hmax hx
  have h2 : 0 < H a b x ^ 2 := by positivity
  nlinarith

lemma H_zero {x : Pt} (hx : x ∈ S) (hH : H a b x = 0) : x = a ∨ x = b := by
  have h0 := T_nonneg hconv ha hb hK hmax hx
  have h1 := T_le hconv ha hb hK hmax hx
  rcases eq_or_lt_of_le h0 with h | h
  · left; exact eq_of_TH hK (by rw [T_a]; linarith) (by rw [H_a, hH])
  rcases eq_or_lt_of_le h1 with h' | h'
  · right; exact eq_of_TH hK (by rw [T_b, h']) (by rw [H_b, hH])
  exfalso
  have hxa : x ≠ a := by rintro rfl; rw [T_a] at h; exact lt_irrefl _ h
  have hxb : x ≠ b := by rintro rfl; rw [T_b] at h'; exact lt_irrefl _ h'
  apply notMem_hull hconv hx
  set μ := T a b x / sq a b with hμ
  have hseg : segment ℝ a b ⊆ convexHull ℝ ((S : Set Pt) \ {x}) :=
    (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ ⟨Finset.mem_coe.mpr ha, hxa.symm⟩)
      (subset_convexHull ℝ _ ⟨Finset.mem_coe.mpr hb, hxb.symm⟩)
  have hmem : a + μ • (b - a) ∈ convexHull ℝ ((S : Set Pt) \ {x}) := by
    apply hseg
    rw [segment_eq_image']
    exact ⟨μ, ⟨div_nonneg h0 hK.le, (div_le_one hK).mpr h1⟩, rfl⟩
  have hxe : x = a + μ • (b - a) := by
    apply eq_of_TH hK
    · rw [T_comb, T_a, T_b, hμ]; field_simp; ring
    · rw [H_comb, H_a, H_b, hH]; ring
  convert hmem using 1

lemma T_inj_pos {x y : Pt} (hx : x ∈ S) (hy : y ∈ S) (hHx : 0 < H a b x) (hHy : 0 < H a b y)
    (hT : T a b x = T a b y) : x = y := by
  by_contra hxy
  have hxa : x ≠ a := by rintro rfl; rw [H_a] at hHx; exact lt_irrefl _ hHx
  have hxb : x ≠ b := by rintro rfl; rw [H_b] at hHx; exact lt_irrefl _ hHx
  have hya : y ≠ a := by rintro rfl; rw [H_a] at hHy; exact lt_irrefl _ hHy
  have hyb : y ≠ b := by rintro rfl; rw [H_b] at hHy; exact lt_irrefl _ hHy
  rcases le_total (H a b x) (H a b y) with h | h
  · apply notMem_hull hconv hx
    exact mem_hull_of_below hK (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hxa hxb
      (subset_convexHull ℝ _ ⟨Finset.mem_coe.mpr hy, Ne.symm hxy⟩) hT.symm hHx h
      (T_nonneg hconv ha hb hK hmax hx) (T_le hconv ha hb hK hmax hx)
  · apply notMem_hull hconv hy
    exact mem_hull_of_below hK (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hya hyb
      (subset_convexHull ℝ _ ⟨Finset.mem_coe.mpr hx, hxy⟩) hT hHy h
      (T_nonneg hconv ha hb hK hmax hy) (T_le hconv ha hb hK hmax hy)

/-- strict concavity of the upper chain -/
lemma concave {x y z : Pt} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hHx : 0 ≤ H a b x) (hHy : 0 < H a b y) (hHz : 0 ≤ H a b z)
    (hxy : T a b x < T a b y) (hyz : T a b y < T a b z) :
    (H a b y - H a b x) * (T a b z - T a b x) > (H a b z - H a b x) * (T a b y - T a b x) := by
  by_contra hcon
  push Not at hcon
  have hya : y ≠ a := by rintro rfl; rw [H_a] at hHy; exact lt_irrefl _ hHy
  have hyb : y ≠ b := by rintro rfl; rw [H_b] at hHy; exact lt_irrefl _ hHy
  have hxy' : x ≠ y := by rintro rfl; exact lt_irrefl _ hxy
  have hzy : z ≠ y := by rintro rfl; exact lt_irrefl _ hyz
  have hTzx : 0 < T a b z - T a b x := by linarith
  set lam := (T a b y - T a b x) / (T a b z - T a b x) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hTzx.le
  have hlam1 : lam ≤ 1 := (div_le_one hTzx).mpr (by linarith)
  set w : Pt := x + lam • (z - x) with hw
  have hwmem : w ∈ convexHull ℝ ((S : Set Pt) \ {y}) := by
    have hseg : segment ℝ x z ⊆ convexHull ℝ ((S : Set Pt) \ {y}) :=
      (convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ ⟨Finset.mem_coe.mpr hx, hxy'⟩)
        (subset_convexHull ℝ _ ⟨Finset.mem_coe.mpr hz, hzy⟩)
    apply hseg
    rw [segment_eq_image']
    exact ⟨lam, ⟨hlam0, hlam1⟩, rfl⟩
  have hTw : T a b w = T a b y := by
    rw [hw, T_comb, hlam]; field_simp; ring
  have hHw : H a b y ≤ H a b w := by
    have h1 : H a b y - H a b x ≤ lam * (H a b z - H a b x) := by
      rw [hlam, div_mul_eq_mul_div, le_div_iff₀ hTzx]
      have := hcon
      rw [mul_comm (H a b z - H a b x)] at this
      linarith
    rw [hw, H_comb]
    linarith
  exact notMem_hull hconv hy (mem_hull_of_below hK (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)
    hya hyb hwmem hTw hHy hHw (T_nonneg hconv ha hb hK hmax hy) (T_le hconv ha hb hK hmax hy))

lemma H_ca_id (a b c x : Pt) : sq a b * H c a x = H a b c * T a b x - T a b c * H a b x := by
  unfold sq H T; ring

lemma C_card :
    (S.filter (fun x => 0 ≤ H a b x)).card = (S.filter (fun x => 0 < H a b x)).card + 2 := by
  have hab : a ≠ b := by
    rintro rfl; unfold sq at hK; simp at hK
  have hC : S.filter (fun x => 0 ≤ H a b x) = insert a (insert b (S.filter (fun x => 0 < H a b x))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, h0⟩
      rcases eq_or_lt_of_le h0 with h | h
      · rcases H_zero hconv ha hb hK hmax hx h.symm with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨hx, h⟩)
    · rintro (rfl | rfl | ⟨hx, h⟩)
      · exact ⟨ha, by rw [H_a]⟩
      · exact ⟨hb, by rw [H_b]⟩
      · exact ⟨hx, h.le⟩
  rw [hC, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
  · simp [H_b]
  · simp only [Finset.mem_insert, Finset.mem_filter, H_a, lt_irrefl, and_false, or_false]
    exact hab

lemma T_injOn_C : Set.InjOn (T a b) (S.filter (fun x => 0 ≤ H a b x) : Set Pt) := by
  intro x hx y hy hT
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
  rcases eq_or_lt_of_le hx.2 with hx0 | hx0 <;> rcases eq_or_lt_of_le hy.2 with hy0 | hy0
  · rcases H_zero hconv ha hb hK hmax hx.1 hx0.symm with rfl | rfl <;>
      rcases H_zero hconv ha hb hK hmax hy.1 hy0.symm with h | h <;>
      first | exact h.symm | (subst h; simp [T_a, T_b] at hT; linarith)
  · exfalso
    have h1 := T_pos_of_H hconv ha hb hK hmax hy.1 hy0.ne'
    have h2 := T_lt_of_H hconv ha hb hK hmax hy.1 hy0.ne'
    rcases H_zero hconv ha hb hK hmax hx.1 hx0.symm with rfl | rfl
    · rw [T_a] at hT; linarith
    · rw [T_b] at hT; linarith
  · exfalso
    have h1 := T_pos_of_H hconv ha hb hK hmax hx.1 hx0.ne'
    have h2 := T_lt_of_H hconv ha hb hK hmax hx.1 hx0.ne'
    rcases H_zero hconv ha hb hK hmax hy.1 hy0.symm with rfl | rfl
    · rw [T_a] at hT; linarith
    · rw [T_b] at hT; linarith
  · exact T_inj_pos hconv ha hb hK hmax hx.1 hy.1 hx0 hy0 hT

lemma enum_exists : ∃ pt : ℕ → Pt,
    (∀ i, i < (S.filter (fun x => 0 < H a b x)).card + 2 → pt i ∈ S ∧ 0 ≤ H a b (pt i)) ∧
    (∀ i j, i < j → j < (S.filter (fun x => 0 < H a b x)).card + 2 →
      T a b (pt i) < T a b (pt j)) ∧
    pt 0 = a ∧ pt ((S.filter (fun x => 0 < H a b x)).card + 1) = b := by
  set m := (S.filter (fun x => 0 < H a b x)).card with hm
  set C := S.filter (fun x => 0 ≤ H a b x) with hCdef
  have hcard : (C.image (T a b)).card = m + 2 := by
    rw [Finset.card_image_of_injOn (T_injOn_C hconv ha hb hK hmax)]
    exact C_card hconv ha hb hK hmax
  set o := (C.image (T a b)).orderEmbOfFin hcard with ho
  have hex : ∀ i : Fin (m + 2), ∃ x ∈ C, T a b x = o i := fun i =>
    Finset.mem_image.mp (Finset.orderEmbOfFin_mem _ hcard i)
  let pt : ℕ → Pt := fun i => if h : i < m + 2 then Classical.choose (hex ⟨i, h⟩) else a
  have hpt : ∀ i (h : i < m + 2), pt i ∈ C ∧ T a b (pt i) = o ⟨i, h⟩ := by
    intro i h
    simp only [pt, dif_pos h]
    exact Classical.choose_spec (hex ⟨i, h⟩)
  have haC : a ∈ C := Finset.mem_filter.mpr ⟨ha, by rw [H_a]⟩
  have hbC : b ∈ C := Finset.mem_filter.mpr ⟨hb, by rw [H_b]⟩
  have hrange : ∀ x ∈ C, ∃ i : Fin (m + 2), o i = T a b x := by
    intro x hx
    have : T a b x ∈ Set.range o := by
      rw [ho, Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx)
    exact this
  refine ⟨pt, ?_, ?_, ?_, ?_⟩
  · intro i h
    exact Finset.mem_filter.mp (hpt i h).1
  · intro i j hij hj
    rw [(hpt i (by omega)).2, (hpt j hj).2]
    exact o.strictMono (by simp [Fin.lt_def]; omega)
  · -- pt 0 = a
    have h0 := hpt 0 (by omega)
    obtain ⟨k, hk⟩ := hrange a haC
    have hle : o ⟨0, by omega⟩ ≤ o k := o.monotone (by simp [Fin.le_def])
    have hT0 : T a b (pt 0) ≤ 0 := by rw [h0.2]; rw [hk, T_a] at hle; exact hle
    have hTnn := T_nonneg hconv ha hb hK hmax (Finset.mem_filter.mp h0.1).1
    exact T_injOn_C hconv ha hb hK hmax h0.1 haC (by rw [T_a]; linarith)
  · have h1 := hpt (m + 1) (by omega)
    obtain ⟨k, hk⟩ := hrange b hbC
    have hle : o k ≤ o ⟨m + 1, by omega⟩ := o.monotone (by simp [Fin.le_def]; omega)
    have hT1 : sq a b ≤ T a b (pt (m + 1)) := by rw [h1.2]; rw [hk, T_b] at hle; exact hle
    have hTle := T_le hconv ha hb hK hmax (Finset.mem_filter.mp h1.1).1
    exact T_injOn_C hconv ha hb hK hmax h1.1 hbC (by rw [T_b]; linarith)

section Window

variable (pt : ℕ → Pt) (m : ℕ)
  (hmem : ∀ i, i < m + 2 → pt i ∈ S ∧ 0 ≤ H a b (pt i))
  (hmono : ∀ i j, i < j → j < m + 2 → T a b (pt i) < T a b (pt j))
  (h0 : pt 0 = a) (h1 : pt (m + 1) = b)
include hmem hmono h0 h1

lemma H_pos_inner {k : ℕ} (hk0 : 0 < k) (hk1 : k < m + 1) : 0 < H a b (pt k) := by
  have hk := hmem k (by omega)
  rcases eq_or_lt_of_le hk.2 with h | h
  · exfalso
    have hlo := hmono 0 k hk0 (by omega)
    have hhi := hmono k (m + 1) hk1 (by omega)
    rw [h0, T_a] at hlo
    rw [h1, T_b] at hhi
    rcases H_zero hconv ha hb hK hmax hk.1 h.symm with e | e
    · rw [e, T_a] at hlo; exact lt_irrefl _ hlo
    · rw [e, T_b] at hhi; exact lt_irrefl _ hhi
  · exact h

lemma window {i j : ℕ} (hj : 1 ≤ j) (hij : i + j + 1 ≤ m + 1) (hfull : ¬ (i = 0 ∧ i + j + 1 = m + 1)) :
    sq (pt i) (pt (i + j)) < sq (pt i) (pt (i + j + 1)) ∨
      sq (pt (i + 1)) (pt (i + j + 1)) < sq (pt i) (pt (i + j + 1)) := by
  have mP := hmem i (by omega)
  have mQ := hmem (i + 1) (by omega)
  have mR := hmem (i + j) (by omega)
  have mS := hmem (i + j + 1) (by omega)
  have hQpos : 0 < H a b (pt (i + 1)) :=
    H_pos_inner hconv ha hb hK hmax pt m hmem hmono h0 h1 (by omega) (by omega)
  have hRpos : 0 < H a b (pt (i + j)) :=
    H_pos_inner hconv ha hb hK hmax pt m hmem hmono h0 h1 (by omega) (by omega)
  have tPQ := hmono i (i + 1) (by omega) (by omega)
  have tQS := hmono (i + 1) (i + j + 1) (by omega) (by omega)
  have tPR := hmono i (i + j) (by omega) (by omega)
  have tRS := hmono (i + j) (i + j + 1) (by omega) (by omega)
  have hKpos := hK
  set K := sq a b with hKdef
  set P := pt i
  set Q := pt (i + 1)
  set R := pt (i + j)
  set S' := pt (i + j + 1)
  have hTa : T a b a = 0 := T_a a b
  have hHa : H a b a = 0 := H_a a b
  have hTb : T a b b = K := T_b a b
  have hHb : H a b b = 0 := H_b a b
  have kPS := key_id a b P S'
  have kQS := key_id a b Q S'
  have kPR := key_id a b P R
  rcases le_or_gt (H a b P) (H a b S') with hcase | hcase
  · right
    -- S' is not b
    have hSb : i + j + 1 < m + 1 := by
      rcases lt_or_eq_of_le hij with h | h
      · exact h
      · exfalso
        have hSeq : S' = b := by simp only [S']; rw [h]; exact h1
        have hHP0 : H a b P = 0 := le_antisymm (by rw [hSeq, hHb] at hcase; exact hcase) mP.2
        rcases H_zero hconv ha hb hK hmax mP.1 hHP0 with e | e
        · have hi0 : i = 0 := by
            by_contra hi
            have := hmono 0 i (by omega) (by omega)
            rw [h0] at this
            simp only [P] at e
            rw [e] at this
            exact lt_irrefl _ this
          exact hfull ⟨hi0, h⟩
        · have := hmono i (m + 1) (by omega) (by omega)
          simp only [P] at e
          rw [e, h1] at this
          exact lt_irrefl _ this
    have hSpos : 0 < H a b S' :=
      H_pos_inner hconv ha hb hK hmax pt m hmem hmono h0 h1 (by omega) hSb
    have c1 := concave hconv ha hb hK hmax mP.1 mQ.1 mS.1 mP.2 hQpos mS.2 tPQ tQS
    have c2 := concave hconv ha hb hK hmax mQ.1 mS.1 hb mQ.2 hSpos (by rw [hHb]) tQS
      (by rw [hTb]; exact T_lt_of_H hconv ha hb hK hmax mS.1 hSpos.ne')
    rw [hTb, hHb] at c2
    have h2 : H a b S' * (K - T a b Q) > H a b Q * (K - T a b S') := by
      have e : H a b S' * (K - T a b Q) - H a b Q * (K - T a b S')
          = (H a b S' - H a b Q) * (K - T a b Q) - (0 - H a b Q) * (T a b S' - T a b Q) := by ring
      linarith
    have h3 : H a b P * T a b Q ≥ H a b Q * T a b P := by
      by_cases hi : i = 0
      · have hPa : P = a := by simp only [P]; rw [hi]; exact h0
        rw [hPa, hHa, hTa]; ring_nf; exact le_refl _
      · have hPpos : 0 < H a b P :=
          H_pos_inner hconv ha hb hK hmax pt m hmem hmono h0 h1 (by omega) (by omega)
        have c3 := concave hconv ha hb hK hmax ha mP.1 mQ.1 (by rw [hHa]) hPpos mQ.2
          (by rw [hTa]; exact T_pos_of_H hconv ha hb hK hmax mP.1 hPpos.ne') tPQ
        rw [hTa, hHa] at c3
        nlinarith
    have h4 := lens_b hconv ha hb hK hmax mQ.1
    have core := core_ineq (T a b P) (T a b Q) (T a b S') (H a b P) (H a b Q) (H a b S') K
      (T_nonneg hconv ha hb hK hmax mP.1) tPQ tQS mP.2 hQpos hcase c1 h2 h3 h4
    have : K * sq Q S' < K * sq P S' := by
      rw [kQS, kPS]; nlinarith [core]
    exact lt_of_mul_lt_mul_left this hKpos.le
  · left
    have hPpos : 0 < H a b P := lt_of_le_of_lt mS.2 hcase
    have hi : i ≠ 0 := by
      rintro hi
      have hPa : P = a := by simp only [P]; rw [hi]; exact h0
      rw [hPa, hHa] at hPpos; exact lt_irrefl _ hPpos
    have c1 := concave hconv ha hb hK hmax mP.1 mR.1 mS.1 mP.2 hRpos mS.2 tPR tRS
    have c2 := concave hconv ha hb hK hmax ha mP.1 mR.1 (by rw [hHa]) hPpos mR.2
      (by rw [hTa]; exact T_pos_of_H hconv ha hb hK hmax mP.1 hPpos.ne') tPR
    rw [hTa, hHa] at c2
    have h3 : H a b S' * (K - T a b R) ≥ H a b R * (K - T a b S') := by
      rcases eq_or_lt_of_le mS.2 with hS0 | hS0
      · rcases H_zero hconv ha hb hK hmax mS.1 hS0.symm with e | e
        · exfalso
          have := hmono 0 (i + j + 1) (by omega) (by omega)
          rw [h0] at this; simp only [S'] at e; rw [e] at this; exact lt_irrefl _ this
        · simp only [S'] at e ⊢; rw [e, hHb, hTb]; ring_nf; exact le_refl _
      · have c3 := concave hconv ha hb hK hmax mR.1 mS.1 hb mR.2 hS0 (by rw [hHb]) tRS
          (by rw [hTb]; exact T_lt_of_H hconv ha hb hK hmax mS.1 hS0.ne')
        rw [hTb, hHb] at c3
        have e : H a b S' * (K - T a b R) - H a b R * (K - T a b S')
            = (H a b S' - H a b R) * (K - T a b R) - (0 - H a b R) * (T a b S' - T a b R) := by ring
        linarith
    have h4 := lens_a hconv ha hb hK hmax mR.1
    have core := core_ineq (K - T a b S') (K - T a b R) (K - T a b P) (H a b S') (H a b R) (H a b P) K
      (by linarith [T_le hconv ha hb hK hmax mS.1]) (by linarith) (by linarith) mS.2 hRpos hcase.le
      (by
        have e : (H a b R - H a b S') * ((K - T a b P) - (K - T a b S'))
            - (H a b P - H a b S') * ((K - T a b R) - (K - T a b S'))
            = (H a b R - H a b P) * (T a b S' - T a b P) - (H a b S' - H a b P) * (T a b R - T a b P) := by ring
        linarith)
      (by
        have e : H a b P * (K - (K - T a b R)) - H a b R * (K - (K - T a b P))
            = (H a b P - 0) * (T a b R - 0) - (H a b R - 0) * (T a b P - 0) := by ring
        linarith)
      h3
      (by have e : (K - (K - T a b R)) ^ 2 = T a b R ^ 2 := by ring
          rw [e]; exact h4)
    have : K * sq P R < K * sq P S' := by
      rw [kPR, kPS]; nlinarith [core]
    exact lt_of_mul_lt_mul_left this hKpos.le

end Window

omit hconv ha hb hK hmax in
lemma mem_distanceSet_of {x y : Pt} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    dist x y ∈ distanceSet S := by
  unfold distanceSet
  exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩

theorem chain_count :
    (S.filter (fun x => 0 < H a b x)).card ≤ distinctDistances S ∧
      ((S.filter (fun x => 0 < H a b x)).card + 1 ≤ distinctDistances S ∨
        ∃ c ∈ S, 0 < H a b c ∧ sq a c = sq a b) := by
  obtain ⟨pt, hmem, hmono, h0, h1⟩ := enum_exists hconv ha hb hK hmax
  set m := (S.filter (fun x => 0 < H a b x)).card with hm
  have hne : ∀ i j, i < j → j < m + 2 → pt i ≠ pt j := by
    intro i j hij hj he
    have := hmono i j hij hj
    rw [he] at this; exact lt_irrefl _ this
  have hab : a ≠ b := by rintro rfl; unfold sq at hK; simp at hK
  let μ : ℕ → ℝ := fun j => if h : j ≤ m + 1 then
      (Finset.range (m + 2 - j)).inf' ⟨0, by simp; omega⟩ (fun i => sq (pt i) (pt (i + j))) else 0
  have M1 : ∀ j i, j ≤ m + 1 → i + j ≤ m + 1 → μ j ≤ sq (pt i) (pt (i + j)) := by
    intro j i hj hij
    simp only [μ, dif_pos hj]
    exact Finset.inf'_le _ (Finset.mem_range.mpr (by omega))
  have M2 : ∀ j, j ≤ m + 1 → ∃ i, i + j ≤ m + 1 ∧ μ j = sq (pt i) (pt (i + j)) := by
    intro j hj
    simp only [μ, dif_pos hj]
    obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (m + 2 - j))
      ⟨0, by simp; omega⟩ (fun i => sq (pt i) (pt (i + j)))
    exact ⟨i, by simp at hi; omega, he⟩
  have step : ∀ j, 1 ≤ j → j + 1 ≤ m → μ j < μ (j + 1) := by
    intro j hj hjm
    obtain ⟨i, hi, he⟩ := M2 (j + 1) (by omega)
    have hw := window hconv ha hb hK hmax pt m hmem hmono h0 h1 (i := i) (j := j) hj (by omega)
      (by omega)
    rw [he, show i + (j + 1) = i + j + 1 by omega]
    rcases hw with hw | hw
    · exact lt_of_le_of_lt (M1 j i (by omega) (by omega)) hw
    · have := M1 j (i + 1) (by omega) (by omega)
      rw [show i + 1 + j = i + j + 1 by omega] at this
      exact lt_of_le_of_lt this hw
  have mono : ∀ j k, 1 ≤ j → j < k → k ≤ m → μ j < μ k := by
    intro j k hj hjk hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with h | h
      · exact lt_trans (ih h (by omega)) (step k (by omega) hk)
      · rw [← h]; exact step j hj (by omega)
  have μnn : ∀ j, j ≤ m + 1 → 0 ≤ μ j := by
    intro j hj
    obtain ⟨i, -, he⟩ := M2 j hj
    rw [he]; exact sq_nonneg' _ _
  have μmem : ∀ j, 1 ≤ j → j ≤ m + 1 → Real.sqrt (μ j) ∈ distanceSet S := by
    intro j hj1 hj
    obtain ⟨i, hi, he⟩ := M2 j hj
    rw [he, ← dist_eq_sqrt]
    exact mem_distanceSet_of (hmem i (by omega)).1 (hmem (i + j) (by omega)).1
      (hne i (i + j) (by omega) (by omega))
  set V := (Finset.Icc 1 m).image (fun j => Real.sqrt (μ j)) with hV
  have hVcard : V.card = m := by
    rw [hV, Finset.card_image_of_injOn]
    · simp
    · intro j hj k hk hjk
      simp only [Finset.coe_Icc, Set.mem_Icc] at hj hk
      simp only at hjk
      have e : μ j = μ k := by
        rwa [Real.sqrt_inj (μnn j (by omega)) (μnn k (by omega))] at hjk
      by_contra hne'
      rcases lt_or_gt_of_ne hne' with h | h
      · exact absurd e (ne_of_lt (mono j k hj.1 h hk.2))
      · exact absurd e (ne_of_gt (mono k j hk.1 h hj.2))
  have hVsub : V ⊆ distanceSet S := by
    intro v hv
    rw [hV, Finset.mem_image] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    simp only [Finset.mem_Icc] at hj
    exact μmem j hj.1 (by omega)
  have hcardle : m ≤ distinctDistances S := by
    unfold distinctDistances
    rw [← hVcard]
    exact Finset.card_le_card hVsub
  refine ⟨hcardle, ?_⟩
  by_cases hm0 : m = 0
  · left
    unfold distinctDistances
    rw [hm0]
    exact Finset.card_pos.mpr ⟨_, mem_distanceSet_of ha hb hab⟩
  by_cases hlt : μ m < sq a b
  · left
    have hdab : dist a b ∉ V := by
      intro hin
      rw [hV, Finset.mem_image] at hin
      obtain ⟨j, hj, he⟩ := hin
      simp only [Finset.mem_Icc] at hj
      have hle : μ j ≤ μ m := by
        rcases eq_or_lt_of_le hj.2 with h | h
        · rw [h]
        · exact (mono j m hj.1 h le_rfl).le
      rw [dist_eq_sqrt] at he
      have := Real.sqrt_lt_sqrt (μnn j (by omega)) (lt_of_le_of_lt hle hlt)
      rw [he] at this; exact lt_irrefl _ this
    unfold distinctDistances
    have : (insert (dist a b) V).card = m + 1 := by
      rw [Finset.card_insert_of_notMem hdab, hVcard]
    rw [← this]
    apply Finset.card_le_card
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact mem_distanceSet_of ha hb hab
    · exact hVsub hv
  · right
    push Not at hlt
    have e1 := M1 m 0 (by omega) (by omega)
    rw [Nat.zero_add, h0] at e1
    have e2 := hmax a ha (pt m) (hmem m (by omega)).1
    exact ⟨pt m, (hmem m (by omega)).1,
      H_pos_inner hconv ha hb hK hmax pt m hmem hmono h0 h1 (by omega) (by omega), by linarith⟩

end Setup

theorem main (n : ℕ) (P : Finset Pt) (hcard : P.card = n)
    (hconv : ConvexIndependent ℝ ((↑) : ↥(P : Set Pt) → Pt)) : n / 2 ≤ distinctDistances P := by
  by_cases hn : P.card < 2
  · omega
  push Not at hn
  have hne : P.offDiag.Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
    exact ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩⟩
  obtain ⟨p0, hp0, hmax0⟩ := P.offDiag.exists_max_image (fun p => sq p.1 p.2) hne
  set Kmax := sq p0.1 p0.2 with hKmax
  set diam := P.offDiag.filter (fun p => sq p.1 p.2 = Kmax) with hdiam
  have hdne : diam.Nonempty := ⟨p0, Finset.mem_filter.mpr ⟨hp0, rfl⟩⟩
  obtain ⟨⟨a, b⟩, habm, hbest⟩ :=
    diam.exists_max_image (fun p => (P.filter (fun x => 0 < H p.1 p.2 x)).card) hdne
  obtain ⟨habo, habK⟩ := Finset.mem_filter.mp habm
  obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp habo
  simp only at ha hb hab habK hbest
  have hmax : ∀ x ∈ P, ∀ y ∈ P, sq x y ≤ sq a b := by
    intro x hx y hy
    by_cases hxy : x = y
    · rw [hxy]; unfold sq; simp only [sub_self]; norm_num; exact sq_nonneg' a b
    · rw [habK]; exact hmax0 (x, y) (Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩)
  have hK : 0 < sq a b := by
    rcases eq_or_lt_of_le (sq_nonneg' a b) with h | h
    · exact absurd (eq_of_sq_eq_zero h.symm) hab
    · exact h
  set m := (P.filter (fun x => 0 < H a b x)).card with hm
  set mR := (P.filter (fun x => H a b x < 0)).card with hmR
  have hsplit : P.card = m + mR + 2 := by
    have h1 := C_card hconv ha hb hK hmax
    have h2 := Finset.card_filter_add_card_filter_not (s := P) (p := fun x => 0 ≤ H a b x)
    have h3 : P.filter (fun x => ¬ 0 ≤ H a b x) = P.filter (fun x => H a b x < 0) := by
      ext x; simp [not_le]
    rw [h3] at h2
    rw [← hmR, ← hm] at *
    omega
  have hRle : mR ≤ m := by
    have hba : (b, a) ∈ diam := Finset.mem_filter.mpr
      ⟨Finset.mem_offDiag.mpr ⟨hb, ha, Ne.symm hab⟩, by simp only; rw [sq_comm, habK]⟩
    have := hbest (b, a) hba
    simp only at this
    have e : P.filter (fun x => 0 < H b a x) = P.filter (fun x => H a b x < 0) := by
      ext x; simp only [Finset.mem_filter]; rw [H_swap, neg_pos]
    rw [e] at this
    exact this
  obtain ⟨hc1, hc2⟩ := chain_count hconv ha hb hK hmax
  rcases hc2 with h | ⟨c, hc, hHc, hac⟩
  · omega
  · have hca : c ≠ a := by rintro rfl; rw [H_a] at hHc; exact lt_irrefl _ hHc
    have hcam : (c, a) ∈ diam := Finset.mem_filter.mpr
      ⟨Finset.mem_offDiag.mpr ⟨hc, ha, hca⟩, by simp only; rw [sq_comm, hac, habK]⟩
    have hb' := hbest (c, a) hcam
    simp only at hb'
    have hTc := T_pos_of_H hconv ha hb hK hmax hc hHc.ne'
    have hsub : insert b (P.filter (fun x => H a b x < 0)) ⊆ P.filter (fun x => 0 < H c a x) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · refine Finset.mem_filter.mpr ⟨hb, ?_⟩
        have e : sq a x * H c a x = H a x c * T a x x - T a x c * H a x x := by
          unfold sq H T; ring
        rw [T_b, H_b] at e
        have : 0 < sq a x * H c a x := by rw [e]; nlinarith
        exact pos_of_mul_pos_right this hK.le
      · obtain ⟨hxP, hHx⟩ := Finset.mem_filter.mp hx
        refine Finset.mem_filter.mpr ⟨hxP, ?_⟩
        have e : sq a b * H c a x = H a b c * T a b x - T a b c * H a b x := by
          unfold sq H T; ring
        have hTx := T_nonneg hconv ha hb hK hmax hxP
        have : 0 < sq a b * H c a x := by rw [e]; nlinarith
        exact pos_of_mul_pos_right this hK.le
    have hbn : b ∉ P.filter (fun x => H a b x < 0) := by simp [H_b]
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hbn] at this
    omega

end OMA660

theorem OMA.solution : type_of% @Erdos660.erdos_660.variants.altman_planar := by
  intro n P hcard hconv _haff
  exact OMA660.main n P hcard hconv
