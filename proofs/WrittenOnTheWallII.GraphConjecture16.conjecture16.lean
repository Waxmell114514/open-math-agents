import FormalConjectures.WrittenOnTheWallII.GraphConjecture16

-- Problem: Written on the Wall II - Conjecture 16
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/GraphConjecture16.lean:45 (declaration WrittenOnTheWallII.GraphConjecture16.conjecture16)
-- Credit: @Waxmell114514 (the owner of the agent is credited as the solver)
--
-- Proof outline.
-- (C) Contracting the closed neighbourhood N[y] of a vertex y to a single vertex lowers the
--     radius by at most one (lift_walk, far_contr).
-- (E) An induced bipartite set of the contraction containing the contracted vertex expands to
--     an induced bipartite set of G containing y and any independent set A of neighbours of y,
--     gaining |A| vertices (expand).
-- (F) Every connected graph has, through any prescribed vertex, an induced bipartite subgraph
--     with at least 2 * radius vertices, by strong induction on the number of vertices using
--     (C) and (E) (bigF).
-- Main: contract N[v] for a vertex v maximising the independence number l(v) of its
-- neighbourhood, apply (F) to the contraction (radius at least rad - 1) and expand with a
-- maximum independent set of N(v): b(G) >= 2 (rad - 1) + max l(v).

namespace OMA16

open SimpleGraph Finset Classical

section Core

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `x` lies in the closed neighbourhood of `y`. -/
def inK (G : SimpleGraph V) (y x : V) : Prop := x = y ∨ G.Adj y x

/-- Vertices of the graph obtained by contracting the closed neighbourhood of `y`;
`none` is the contracted vertex. -/
abbrev CV (G : SimpleGraph V) (y : V) := Option {x : V // ¬ inK G y x}

def cAdj (G : SimpleGraph V) (y : V) : CV G y → CV G y → Prop
  | some a, some b => G.Adj a.1 b.1
  | none, some b => ∃ k, G.Adj y k ∧ G.Adj k b.1
  | some a, none => ∃ k, G.Adj y k ∧ G.Adj k a.1
  | none, none => False

/-- The contraction of the closed neighbourhood of `y`. -/
def contr (G : SimpleGraph V) (y : V) : SimpleGraph (CV G y) where
  Adj := cAdj G y
  symm := ⟨by
    intro u v h
    rcases u with _ | a <;> rcases v with _ | b <;> simp only [cAdj] at h ⊢
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by
    intro u h
    rcases u with _ | a <;> simp only [cAdj] at h
    exact G.irrefl h⟩

def rep (G : SimpleGraph V) (y : V) : CV G y → V
  | none => y
  | some a => a.1

noncomputable def proj (G : SimpleGraph V) (y : V) (x : V) : CV G y :=
  if h : inK G y x then none else some ⟨x, h⟩

lemma proj_rep (G : SimpleGraph V) (y : V) (w : CV G y) : proj G y (rep G y w) = w := by
  rcases w with _ | a
  · show proj G y y = none
    unfold proj
    exact dif_pos (show inK G y y from Or.inl rfl)
  · simp [proj, rep, a.2]

lemma adj_proj (G : SimpleGraph V) (y : V) {u v : V} (h : G.Adj u v) :
    proj G y u = proj G y v ∨ (contr G y).Adj (proj G y u) (proj G y v) := by
  by_cases hu : inK G y u <;> by_cases hv : inK G y v
  · left; simp [proj, hu, hv]
  · right
    simp only [proj, hu, hv, dif_pos, dif_neg, not_false_eq_true]
    show ∃ k, G.Adj y k ∧ G.Adj k v
    rcases hu with rfl | hyu
    · exact absurd (Or.inr h) hv
    · exact ⟨u, hyu, h⟩
  · right
    simp only [proj, hu, hv, dif_pos, dif_neg, not_false_eq_true]
    show ∃ k, G.Adj y k ∧ G.Adj k u
    rcases hv with rfl | hyv
    · exact absurd (Or.inr h.symm) hu
    · exact ⟨v, hyv, h.symm⟩
  · right
    simp only [proj, hu, hv, dif_neg, not_false_eq_true]
    exact h

lemma reach_proj (G : SimpleGraph V) (y : V) {u v : V} (p : G.Walk u v) :
    (contr G y).Reachable (proj G y u) (proj G y v) := by
  induction p with
  | nil => exact Reachable.refl _
  | cons h q ih =>
    rcases adj_proj G y h with he | ha
    · rw [he]; exact ih
    · exact ha.reachable.trans ih

lemma contr_connected (G : SimpleGraph V) (y : V) (hG : G.Connected) :
    (contr G y).Connected := by
  have : Nonempty (CV G y) := ⟨none⟩
  refine Connected.mk ?_
  intro u v
  obtain ⟨p⟩ := hG.preconnected (rep G y u) (rep G y v)
  have := reach_proj G y p
  rwa [proj_rep, proj_rep] at this

lemma dist_le_one_of_adj {W : Type*} {H : SimpleGraph W} {a b : W} (h : H.Adj a b) :
    H.dist a b ≤ 1 := by
  simpa using SimpleGraph.dist_le (Walk.cons h Walk.nil)

lemma dist_le_two {W : Type*} {H : SimpleGraph W} {a k b : W} (h1 : H.Adj a k) (h2 : H.Adj k b) :
    H.dist a b ≤ 2 := by
  simpa using SimpleGraph.dist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))

/-- Lifting walks of the contraction back to `G`. -/
lemma lift_walk (G : SimpleGraph V) (y : V) (hG : G.Connected) {u v : CV G y}
    (p : (contr G y).Walk u v) :
    G.dist (rep G y u) (rep G y v) + (if u = none then 1 else 0) + (if v = none then 1 else 0)
      ≤ p.length + 2 * p.support.count none := by
  induction p with
  | nil =>
    rename_i u
    rcases u with _ | a <;> simp [rep]
  | cons h q ih =>
    rename_i u w v
    have htri := hG.dist_triangle (u := rep G y u) (v := rep G y w) (w := rep G y v)
    rcases u with _ | a <;> rcases w with _ | b
    · exact absurd h (by simp [contr, cAdj])
    · obtain ⟨k, hk1, hk2⟩ := (show ∃ k, G.Adj y k ∧ G.Adj k b.1 from h)
      have h2 : G.dist y b.1 ≤ 2 := dist_le_two hk1 hk2
      simp only [rep, Walk.length_cons, Walk.support_cons, List.count_cons_self] at ih htri h2 ⊢
      simp only [reduceCtorEq, if_false, if_true] at ih ⊢
      split_ifs at ih ⊢ <;> omega
    · obtain ⟨k, hk1, hk2⟩ := (show ∃ k, G.Adj y k ∧ G.Adj k a.1 from h)
      have h2 : G.dist a.1 y ≤ 2 := by
        rw [SimpleGraph.dist_comm]; exact dist_le_two hk1 hk2
      simp only [rep, Walk.length_cons, Walk.support_cons, List.count_cons] at ih htri h2 ⊢
      simp only [reduceCtorEq, if_false, if_true, beq_iff_eq] at ih ⊢
      split_ifs at ih ⊢ <;> omega
    · have h1 : G.dist a.1 b.1 ≤ 1 := dist_le_one_of_adj (show G.Adj a.1 b.1 from h)
      simp only [rep, Walk.length_cons, Walk.support_cons, List.count_cons] at ih htri h1 ⊢
      simp only [reduceCtorEq, if_false, beq_iff_eq] at ih ⊢
      split_ifs at ih ⊢ <;> omega

/-- Every vertex has a vertex at distance at least `ρ`. -/
def HasFar {W : Type*} (H : SimpleGraph W) (ρ : ℕ) : Prop := ∀ u, ∃ z, ρ ≤ H.dist u z

lemma exists_short_path {W : Type*} [DecidableEq W] {H : SimpleGraph W} (hH : H.Connected) (u v : W) :
    ∃ p : H.Walk u v, p.IsPath ∧ p.length = H.dist u v := by
  obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist u v
  refine ⟨p.bypass, p.bypass_isPath, ?_⟩
  have h1 := p.length_bypass_le_length
  have h2 := SimpleGraph.dist_le p.bypass
  omega

lemma count_le_one_of_path {W : Type*} [BEq W] [LawfulBEq W] {H : SimpleGraph W} {u v : W}
    {p : H.Walk u v} (hp : p.IsPath) (x : W) : p.support.count x ≤ 1 :=
  List.nodup_iff_count_le_one.mp hp.support_nodup x

/-- Contracting a closed neighbourhood lowers the radius by at most one. -/
lemma far_contr (G : SimpleGraph V) (y : V) (hG : G.Connected) {ρ : ℕ} (hρ : HasFar G ρ) :
    HasFar (contr G y) (ρ - 1) := by
  have hG' := contr_connected G y hG
  intro u
  by_contra hcon
  push Not at hcon
  have hρ2 : 2 ≤ ρ := by
    have := hcon u
    omega
  rcases u with _ | w
  · obtain ⟨z, hz⟩ := hρ y
    have hzK : ¬ inK G y z := by
      rintro (rfl | hyz)
      · simp at hz; omega
      · have := dist_le_one_of_adj hyz; omega
    obtain ⟨p, hp, hpl⟩ := exists_short_path hG' none (some ⟨z, hzK⟩)
    have hl := lift_walk G y hG p
    have hc := count_le_one_of_path hp none
    have := hcon (some ⟨z, hzK⟩)
    simp only [rep, if_true, reduceCtorEq, if_false] at hl
    omega
  · -- a neighbour `c` of `w` on a shortest path to `y`
    have hwK := w.2
    obtain ⟨q0, hq⟩ := hG.exists_walk_length_eq_dist w.1 y
    have hwy : w.1 ≠ y := fun h => hwK (Or.inl h)
    obtain ⟨c, hwc, q', rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hwy q0
    · have hcy : G.dist c y ≤ q'.length := SimpleGraph.dist_le q'
      simp only [Walk.length_cons] at hq
      -- distance from `w` to the contracted vertex
      obtain ⟨p0, hp0, hp0l⟩ := exists_short_path hG' (some w) none
      have hl0 := lift_walk G y hG p0
      have hc0 := count_le_one_of_path hp0 none
      have h0 := hcon none
      simp only [rep, if_true, reduceCtorEq, if_false] at hl0
      obtain ⟨z, hz⟩ := hρ c
      by_cases hzK : inK G y z
      · have hyz : G.dist y z ≤ 1 := by
          rcases hzK with rfl | h
          · simp
          · exact dist_le_one_of_adj h
        have := hG.dist_triangle (u := c) (v := y) (w := z)
        omega
      · obtain ⟨p, hp, hpl⟩ := exists_short_path hG' (some w) (some ⟨z, hzK⟩)
        have hzd := hcon (some ⟨z, hzK⟩)
        have hcw : G.dist c w.1 ≤ 1 := dist_le_one_of_adj hwc.symm
        by_cases hmem : none ∈ p.support
        · have hpre := lift_walk G y hG (p.takeUntil none hmem)
          have hsuf := lift_walk G y hG (p.dropUntil none hmem)
          have hcpre := count_le_one_of_path (hp.takeUntil hmem) none
          have hcsuf := count_le_one_of_path (hp.dropUntil hmem) none
          have hlen : (p.takeUntil none hmem).length + (p.dropUntil none hmem).length = p.length := by
            rw [← Walk.length_append, Walk.take_spec]
          simp only [rep, if_true, reduceCtorEq, if_false] at hpre hsuf
          have := hG.dist_triangle (u := c) (v := y) (w := z)
          omega
        · have hl := lift_walk G y hG p
          have hcnt : p.support.count none = 0 := List.count_eq_zero.mpr hmem
          simp only [rep, reduceCtorEq, if_false] at hl
          have := hG.dist_triangle (u := c) (v := w.1) (w := z)
          omega

/-- A finset of vertices inducing a bipartite subgraph. -/
def IsBip {W : Type*} (H : SimpleGraph W) (S : Finset W) : Prop :=
  ∃ c : W → Fin 2, ∀ u ∈ S, ∀ v ∈ S, H.Adj u v → c u ≠ c v

/-- Expanding the contracted vertex into `y` together with an independent set of neighbours. -/
lemma expand (G : SimpleGraph V) (y : V) (A : Finset V) (hA : ∀ a ∈ A, G.Adj y a)
    (hI : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b) (S' : Finset (CV G y)) (hn : none ∈ S')
    (hb : IsBip (contr G y) S') :
    ∃ S : Finset V, insert y A ⊆ S ∧ IsBip G S ∧ S'.card + A.card ≤ S.card := by
  obtain ⟨c', hc'⟩ := hb
  let T : Finset V := S'.eraseNone.map (Function.Embedding.subtype _)
  have hT : ∀ t ∈ T, ¬ inK G y t := by
    intro t ht
    simp only [T, Finset.mem_map, Function.Embedding.coe_subtype] at ht
    obtain ⟨a, -, rfl⟩ := ht
    exact a.2
  have hTmem : ∀ t (h : ¬ inK G y t), t ∈ T ↔ some ⟨t, h⟩ ∈ S' := by
    intro t h
    simp only [T, Finset.mem_map, Function.Embedding.coe_subtype, Finset.mem_eraseNone]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro ht; exact ⟨⟨t, h⟩, ht, rfl⟩
  have hyA : y ∉ A := fun h => G.irrefl (hA y h)
  have hKA : ∀ x ∈ insert y A, inK G y x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (hA x hx)
  have hdisj : Disjoint T (insert y A) := by
    rw [Finset.disjoint_left]
    intro x hxT hxA
    exact hT x hxT (hKA x hxA)
  refine ⟨T ∪ insert y A, Finset.subset_union_right, ?_, ?_⟩
  · let d := c' none
    refine ⟨fun v => if h : inK G y v then (if v = y then d + 1 else d) else c' (some ⟨v, h⟩), ?_⟩
    have hdd : d + 1 ≠ d := by
      generalize d = e
      revert e
      decide
    have hinS : ∀ x ∈ T ∪ insert y A, inK G y x → x ∈ insert y A := by
      intro x hx hxK
      rcases Finset.mem_union.mp hx with h | h
      · exact absurd hxK (hT x h)
      · exact h
    have key : ∀ u v (hv' : ¬ inK G y v), v ∈ T ∪ insert y A → G.Adj u v → inK G y u →
        (if u = y then d + 1 else d) ≠ c' (some ⟨v, hv'⟩) := by
      intro u v hv' hv huv hu'
      have huy : u ≠ y := by
        rintro rfl
        exact hv' (Or.inr huv)
      have hyu : G.Adj y u := by
        rcases hu' with h | h
        · exact absurd h huy
        · exact h
      rw [if_neg huy]
      have hvS : some ⟨v, hv'⟩ ∈ S' := by
        rcases Finset.mem_union.mp hv with h | h
        · exact (hTmem v hv').mp h
        · exact absurd (hKA v h) hv'
      have hadj : (contr G y).Adj none (some ⟨v, hv'⟩) := ⟨u, hyu, huv⟩
      exact hc' none hn _ hvS hadj
    intro u hu v hv huv
    by_cases hu' : inK G y u <;> by_cases hv' : inK G y v
    · simp only [dif_pos hu', dif_pos hv']
      have hu2 := hinS u hu hu'
      have hv2 := hinS v hv hv'
      rcases Finset.mem_insert.mp hu2 with huy | huA <;>
        rcases Finset.mem_insert.mp hv2 with hvy | hvA
      · rw [huy, hvy] at huv; exact absurd huv G.irrefl
      · have hvy : v ≠ y := fun h => hyA (h ▸ hvA)
        rw [if_pos huy, if_neg hvy]; exact hdd
      · have huy : u ≠ y := fun h => hyA (h ▸ huA)
        rw [if_neg huy, if_pos hvy]; exact hdd.symm
      · exact absurd huv (hI u huA v hvA)
    · simp only [dif_pos hu', dif_neg hv']
      exact key u v hv' hv huv hu'
    · simp only [dif_neg hu', dif_pos hv']
      exact (key v u hu' hu huv.symm hv').symm
    · simp only [dif_neg hu', dif_neg hv']
      have huS : some ⟨u, hu'⟩ ∈ S' := by
        rcases Finset.mem_union.mp hu with h | h
        · exact (hTmem u hu').mp h
        · exact absurd (hKA u h) hu'
      have hvS : some ⟨v, hv'⟩ ∈ S' := by
        rcases Finset.mem_union.mp hv with h | h
        · exact (hTmem v hv').mp h
        · exact absurd (hKA v h) hv'
      exact hc' _ huS _ hvS huv
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_insert_of_notMem hyA]
    have hTc : T.card = S'.card - 1 := by
      simp only [T, Finset.card_map]
      exact Finset.card_eraseNone_of_mem hn
    have : 1 ≤ S'.card := Finset.card_pos.mpr ⟨none, hn⟩
    omega

lemma card_contr_lt (G : SimpleGraph V) (y a : V) (hya : G.Adj y a) :
    Fintype.card (CV G y) < Fintype.card V := by
  have h1 : Fintype.card (CV G y) = Fintype.card {x // ¬ inK G y x} + 1 := Fintype.card_option
  have h2 : Fintype.card {x // ¬ inK G y x} = (univ.filter (fun x => ¬ inK G y x)).card :=
    Fintype.card_subtype _
  have h3 := Finset.card_filter_add_card_filter_not (s := (univ : Finset V))
    (p := fun x => inK G y x)
  have h4 : 2 ≤ (univ.filter (fun x => inK G y x)).card := by
    have hsub : ({y, a} : Finset V) ⊆ univ.filter (fun x => inK G y x) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (hz ▸ hya)
    have hne : y ≠ a := G.ne_of_adj hya
    calc 2 = ({y, a} : Finset V).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub
  rw [Finset.card_univ] at h3
  omega

end Core

universe u

lemma walk_closed {W : Type*} {H : SimpleGraph W} {P : W → Prop} {u v : W} (p : H.Walk u v)
    (hu : P u) (hstep : ∀ a b, P a → H.Adj a b → P b) : P v := by
  induction p with
  | nil => exact hu
  | cons h q ih => exact ih (hstep _ _ hu h)

/-- Every vertex lies in an induced bipartite subgraph with at least twice the radius vertices. -/
theorem bigF (n : ℕ) : ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
    Fintype.card W = n → H.Connected → ∀ ρ, HasFar H ρ →
      ∀ x : W, ∃ S : Finset W, x ∈ S ∧ IsBip H S ∧ 2 * ρ ≤ S.card := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W _ _ H hn hH ρ hρ x
  have step : ∀ y a b, H.Adj y a → H.Adj y b → a ≠ b → ¬ H.Adj a b →
      x ∈ (insert y {a, b} : Finset W) → ∃ S : Finset W, x ∈ S ∧ IsBip H S ∧ 2 * ρ ≤ S.card := by
    intro y a b hya hyb hab hnab hx
    have hcard : Fintype.card (CV H y) < n := hn ▸ card_contr_lt H y a hya
    obtain ⟨S', hS'n, hS'b, hS'c⟩ := ih _ hcard (CV H y) (contr H y) rfl
      (contr_connected H y hH) (ρ - 1) (far_contr H y hH hρ) none
    have hA : ∀ c ∈ ({a, b} : Finset W), H.Adj y c := by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with hc | hc <;> subst hc
      · exact hya
      · exact hyb
    have hI : ∀ c ∈ ({a, b} : Finset W), ∀ d ∈ ({a, b} : Finset W), ¬ H.Adj c d := by
      intro c hc d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
      rcases hc with hc | hc <;> rcases hd with hd | hd <;> subst hc <;> subst hd
      · exact H.irrefl
      · exact hnab
      · exact fun h => hnab h.symm
      · exact H.irrefl
    obtain ⟨S, hsub, hSb, hSc⟩ := expand H y {a, b} hA hI S' hS'n hS'b
    refine ⟨S, hsub hx, hSb, ?_⟩
    have : ({a, b} : Finset W).card = 2 := Finset.card_pair hab
    omega
  by_cases hρ0 : ρ = 0
  · refine ⟨{x}, Finset.mem_singleton_self x, ⟨fun _ => 0, ?_⟩, by simp [hρ0]⟩
    intro u hu v hv huv
    rw [Finset.mem_singleton] at hu hv
    subst hu; subst hv
    exact absurd huv H.irrefl
  by_cases h1 : ∃ a b, H.Adj x a ∧ H.Adj x b ∧ a ≠ b ∧ ¬ H.Adj a b
  · obtain ⟨a, b, hxa, hxb, hab, hnab⟩ := h1
    exact step x a b hxa hxb hab hnab (Finset.mem_insert_self _ _)
  by_cases h2 : ∃ y a, H.Adj x y ∧ H.Adj y a ∧ a ≠ x ∧ ¬ H.Adj x a
  · obtain ⟨y, a, hxy, hya, hax, hnxa⟩ := h2
    exact step y x a hxy.symm hya (Ne.symm hax) (fun h => hnxa h) (by simp)
  push Not at h2
  have hall : ∀ z, z = x ∨ H.Adj x z := by
    intro z
    obtain ⟨p⟩ := hH.preconnected x z
    refine walk_closed (P := fun t => t = x ∨ H.Adj x t) p (Or.inl rfl) ?_
    intro a c ha hac
    rcases ha with ha | hxa
    · subst ha; exact Or.inr hac
    · by_cases hc : c = x
      · exact Or.inl hc
      · exact Or.inr (h2 a c hxa hac hc)
  obtain ⟨z, hz⟩ := hρ x
  have hzx : z ≠ x := by
    intro h; subst h; simp at hz; omega
  have hxz : H.Adj x z := (hall z).resolve_left hzx
  have hd : H.dist x z ≤ 1 := dist_le_one_of_adj hxz
  refine ⟨{x, z}, by simp, ⟨fun v => if v = x then 0 else 1, ?_⟩, ?_⟩
  · intro u hu v hv huv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> subst hu <;> subst hv
    · exact absurd huv H.irrefl
    · simp [hzx]
    · simp [hzx]
    · exact absurd huv H.irrefl
  · rw [Finset.card_pair (Ne.symm hzx)]
    omega

end OMA16

open OMA16 SimpleGraph Classical in
theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture16.conjecture16 := by
  intro α _ _ _ G hG
  set maxL := (Finset.univ.image (fun v => G.indepNeighborsCard v)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty) with hmaxL
  set r := G.radius.toNat with hr
  have hmem : maxL ∈ Finset.univ.image (fun v => indepNeighborsCard G v) := Finset.max'_mem _ _
  obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hmem
  obtain ⟨s, hs⟩ := (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum
  let A : Finset α := s.map (Function.Embedding.subtype _)
  have hAcard : A.card = maxL := by
    rw [Finset.card_map, hs.card_eq, ← hv]
    rfl
  have hA : ∀ a ∈ A, G.Adj v a := by
    intro a ha
    simp only [A, Finset.mem_map, Function.Embedding.coe_subtype] at ha
    obtain ⟨⟨a', ha'⟩, -, rfl⟩ := ha
    exact ha'
  have hI : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b := by
    intro a ha b hb hab
    simp only [A, Finset.mem_map, Function.Embedding.coe_subtype] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    by_cases heq : a' = b'
    · subst heq
      exact G.irrefl hab
    · exact hs.isIndepSet (Finset.mem_coe.mpr ha') (Finset.mem_coe.mpr hb') heq hab
  have hfar : HasFar G r := by
    intro u
    obtain ⟨z, hz⟩ := G.exists_edist_eq_eccent_of_finite u
    refine ⟨z, ?_⟩
    have hle : G.radius ≤ G.eccent u := G.radius_le_eccent
    have hne : G.edist u z ≠ ⊤ := SimpleGraph.edist_ne_top_iff_reachable.mpr (hG.preconnected u z)
    show G.radius.toNat ≤ (G.edist u z).toNat
    rw [hz] at hne ⊢
    exact ENat.toNat_le_toNat hle hne
  obtain ⟨S', hS'n, hS'b, hS'c⟩ := bigF _ (CV G v) (contr G v) rfl (contr_connected G v hG)
    (r - 1) (far_contr G v hG hfar) none
  obtain ⟨S, -, hSb, hSc⟩ := expand G v A hA hI S' hS'n hS'b
  have hb : (S.card : ℝ) ≤ G.b := by
    have hle : S.card ≤ G.largestInducedBipartiteSubgraphSize := by
      unfold largestInducedBipartiteSubgraphSize
      apply le_csSup
      · refine ⟨Fintype.card α, ?_⟩
        rintro n ⟨t, -, rfl⟩
        exact t.card_le_univ
      · exact ⟨S, (induce_isBipartite_iff_exists_coloring G S).mpr hSb, rfl⟩
    show (S.card : ℝ) ≤ (G.largestInducedBipartiteSubgraphSize : ℝ)
    exact_mod_cast hle
  have hcard : 2 * (r - 1) + maxL ≤ S.card := by omega
  have hreal : 2 * ((r : ℝ) - 1) + (maxL : ℝ) ≤ (S.card : ℝ) := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · have h1 : (maxL : ℝ) ≤ S.card := by exact_mod_cast (show maxL ≤ S.card by omega)
      rw [h0]
      push_cast
      linarith
    · have h1 : ((2 * (r - 1) + maxL : ℕ) : ℝ) = 2 * ((r : ℝ) - 1) + maxL := by
        push_cast [Nat.cast_sub hpos]
        ring
      rw [← h1]
      exact_mod_cast hcard
  linarith
