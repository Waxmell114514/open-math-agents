import FormalConjectures.WrittenOnTheWallII.GraphConjecture72

-- Problem: Written on the Wall II - Conjecture 72
-- Credit: @Waxmell114514 (the owner of the agent is credited as the solver)

/-!
# WOWII Conjecture 72 is false

Counterexample on 19 vertices: a centre `c` adjacent to four hubs `p1 p2 q1 q2`; `p1, p2` are both
joined to every vertex of a clique `K1` of size 7, and `q1, q2` to every vertex of a clique `K2` of
size 7 (two 4-cycles through `c` whose far vertices are blown up into cliques).

* `{p1, p2, q1, q2}` is independent in `N(c)`, so `max_v λ(v) ≥ 4`.
* With the potential `K1 ↦ 0, p ↦ 1, c ↦ 2, q ↦ 3, K2 ↦ 4` (1-Lipschitz along edges), the
  eccentricities are at least `2` (centre), `3` (hubs), `4` (clique vertices): the sum is at least
  `2 + 4*3 + 14*4 = 70`, so the average eccentricity is at least `70/19`.
* An induced tree meets each clique in at most 2 vertices (no triangle), two clique vertices exclude
  the hubs of that side (triangle), one clique vertex plus both hubs exclude `c` (4-cycle), and
  without `c` the tree lies on one side (connectivity). Hence every induced tree has at most 5
  vertices.

So `70/19 + 4/3 = 286/57 > 5 ≥ tree(G)`, contradicting `tree(G) ≥ ⌈ecc_avg + maxλ/3⌉`.
-/
namespace OMA72

open SimpleGraph

/-- Vertex classes of the counterexample on `Fin 19`:
0 = centre, 1 = the two left hubs, 2 = the left clique (7), 3 = the two right hubs,
4 = the right clique (7). -/
def cls0 (i : Fin 19) : Fin 5 :=
  if i.val = 0 then 0 else if i.val ≤ 2 then 1 else if i.val ≤ 9 then 2
  else if i.val ≤ 11 then 3 else 4

/-- Adjacency between classes. -/
def R (a b : Fin 5) : Bool :=
  match a.val, b.val with
  | 0, 1 => true | 1, 0 => true | 0, 3 => true | 3, 0 => true
  | 1, 2 => true | 2, 1 => true | 3, 4 => true | 4, 3 => true
  | 2, 2 => true | 4, 4 => true | _, _ => false

lemma R_symm (a b : Fin 5) : R a b = R b a := by
  revert a b; decide

universe u

abbrev V : Type u := ULift.{u} (Fin 19)

def cls (x : V.{u}) : Fin 5 := cls0 x.down

def G72 : SimpleGraph V.{u} where
  Adj x y := x ≠ y ∧ R (cls x) (cls y) = true
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [R_symm]; exact h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

lemma adj_iff {x y : V.{u}} : G72.Adj x y ↔ x ≠ y ∧ R (cls x) (cls y) = true := Iff.rfl

lemma ne_of_cls {x y : V.{u}} (h : cls x ≠ cls y) : x ≠ y := by
  rintro rfl; exact h rfl

lemma cls_cases (a : Fin 5) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
  revert a; decide

-- Connectivity

lemma v0 : cls (⟨0⟩ : V.{u}) = 0 := by decide
lemma v1 : cls (⟨1⟩ : V.{u}) = 1 := by decide
lemma v2 : cls (⟨2⟩ : V.{u}) = 1 := by decide
lemma v3 : cls (⟨3⟩ : V.{u}) = 2 := by decide
lemma v10 : cls (⟨10⟩ : V.{u}) = 3 := by decide
lemma v11 : cls (⟨11⟩ : V.{u}) = 3 := by decide
lemma v12 : cls (⟨12⟩ : V.{u}) = 4 := by decide

lemma cls_eq_zero {x : V.{u}} (h : cls x = 0) : x = ⟨0⟩ := by
  obtain ⟨i⟩ := x
  have : ∀ j : Fin 19, cls0 j = 0 → j = 0 := by decide
  exact congrArg ULift.up (this i h)

lemma cls_eq_one {x : V.{u}} (h : cls x = 1) : x = ⟨1⟩ ∨ x = ⟨2⟩ := by
  obtain ⟨i⟩ := x
  have : ∀ j : Fin 19, cls0 j = 1 → j = 1 ∨ j = 2 := by decide
  rcases this i h with h' | h'
  · left; exact congrArg ULift.up h'
  · right; exact congrArg ULift.up h'

lemma cls_eq_three {x : V.{u}} (h : cls x = 3) : x = ⟨10⟩ ∨ x = ⟨11⟩ := by
  obtain ⟨i⟩ := x
  have : ∀ j : Fin 19, cls0 j = 3 → j = 10 ∨ j = 11 := by decide
  rcases this i h with h' | h'
  · left; exact congrArg ULift.up h'
  · right; exact congrArg ULift.up h'

lemma adj_of {x y : V.{u}} (h : R (cls x) (cls y) = true) (hne : cls x ≠ cls y) :
    G72.Adj x y := ⟨ne_of_cls hne, h⟩

lemma reach0 (v : V.{u}) : G72.Reachable ⟨0⟩ v := by
  rcases cls_cases (cls v) with h | h | h | h | h
  · rw [cls_eq_zero h]
  · exact (adj_of (by rw [v0, h]; decide) (by rw [v0, h]; decide)).reachable
  · have a1 : G72.Adj (⟨0⟩ : V.{u}) ⟨1⟩ := adj_of (by rw [v0, v1]; decide) (by rw [v0, v1]; decide)
    have a2 : G72.Adj (⟨1⟩ : V.{u}) v := adj_of (by rw [v1, h]; decide) (by rw [v1, h]; decide)
    exact a1.reachable.trans a2.reachable
  · exact (adj_of (by rw [v0, h]; decide) (by rw [v0, h]; decide)).reachable
  · have a1 : G72.Adj (⟨0⟩ : V.{u}) ⟨10⟩ :=
      adj_of (by rw [v0, v10]; decide) (by rw [v0, v10]; decide)
    have a2 : G72.Adj (⟨10⟩ : V.{u}) v := adj_of (by rw [v10, h]; decide) (by rw [v10, h]; decide)
    exact a1.reachable.trans a2.reachable

lemma G72_connected : G72.{u}.Connected :=
  { preconnected := fun x y => (reach0 x).symm.trans (reach0 y)
    nonempty := ⟨⟨0⟩⟩ }

-- Eccentricity lower bounds

/-- A 1-Lipschitz potential on the classes. -/
def f (a : Fin 5) : ℤ :=
  match a.val with
  | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | _ => 4

lemma f_lip : ∀ a b : Fin 5, R a b = true → f a - f b ≤ 1 := by decide

lemma walk_bound {u w : V.{u}} (p : G72.Walk u w) : f (cls u) - f (cls w) ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have := f_lip _ _ h.2
    simp only [Walk.length_cons]
    push_cast
    linarith

lemma dist_le_ecc {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : G.Connected) (u w : α) :
    G.dist u w ≤ (G.eccent u).toNat := by
  obtain ⟨w', hw'⟩ := G.exists_edist_eq_eccent_of_finite u
  have h1 : G.edist u w ≤ G.eccent u := edist_le_eccent
  rw [← hw'] at h1 ⊢
  rw [← (hG.preconnected u w).coe_dist_eq_edist, ← (hG.preconnected u w').coe_dist_eq_edist] at h1
  rw [← (hG.preconnected u w').coe_dist_eq_edist, ENat.toNat_natCast]
  exact_mod_cast h1

lemma pot_le_ecc (v w : V.{u}) : f (cls v) - f (cls w) ≤ ((G72.eccent v).toNat : ℤ) ∧
    f (cls w) - f (cls v) ≤ ((G72.eccent v).toNat : ℤ) := by
  obtain ⟨p, hp⟩ := G72_connected.exists_walk_length_eq_dist v w
  have h1 := walk_bound p
  have h2 := walk_bound p.reverse
  rw [Walk.length_reverse] at h2
  have h3 : (G72.dist v w : ℤ) ≤ ((G72.eccent v).toNat : ℤ) := by
    exact_mod_cast dist_le_ecc G72_connected v w
  rw [hp] at h1 h2
  constructor <;> linarith

/-- The eccentricity lower bound by class. -/
def g (a : Fin 5) : ℕ :=
  match a.val with
  | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 3 | _ => 4

lemma g_le : ∀ a : Fin 5, (g a : ℤ) ≤ f 4 - f a ∨ (g a : ℤ) ≤ f a - f 2 := by decide

lemma g_le_ecc (v : V.{u}) : g (cls v) ≤ (G72.eccent v).toNat := by
  have hA := pot_le_ecc v ⟨12⟩
  have hB := pot_le_ecc v ⟨3⟩
  rw [v12] at hA
  rw [v3] at hB
  have := g_le (cls v)
  have : (g (cls v) : ℤ) ≤ ((G72.eccent v).toNat : ℤ) := by omega
  exact_mod_cast this

lemma sum_g : ∑ v : V.{u}, g (cls v) = 70 := by
  rw [show ∑ v : V.{u}, g (cls v) = ∑ i : Fin 19, g (cls0 i) from
    Fintype.sum_equiv Equiv.ulift _ _ (fun _ => rfl)]
  decide

lemma avg_ge : (70 : ℝ) / 19 ≤ averageEccentricity G72.{u} := by
  unfold averageEccentricity
  have hc : Fintype.card V.{u} = 19 := by simp
  rw [hc]
  have h1 : (70 : ℕ) ≤ ∑ v : V.{u}, (G72.eccent v).toNat := by
    rw [← sum_g]
    exact Finset.sum_le_sum (fun v _ => g_le_ecc v)
  have h2 : (70 : ℝ) ≤ ((∑ v : V.{u}, (G72.eccent v).toNat : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h2 ⊢
  exact div_le_div_of_nonneg_right h2 (by norm_num)

-- Independent neighbourhood of the centre

lemma card_le_indepNeighbors {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) (z : α)
    (A : Finset α)
    (hA : ∀ a ∈ A, G.Adj z a) (hI : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ G.Adj a b) :
    A.card ≤ indepNeighborsCard G z := by
  classical
  unfold indepNeighborsCard
  let s : Finset (G.neighborSet z) := A.subtype (fun x => x ∈ G.neighborSet z)
  have hs : s.card = A.card := by
    simp only [s, Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun a ha => hA a ha)
  have hind : (G.induce (G.neighborSet z)).IsIndepSet (s : Set (G.neighborSet z)) := by
    intro x hx y hy hxy hadj
    have hx' : x.1 ∈ A := Finset.mem_subtype.mp (Finset.mem_coe.mp hx)
    have hy' : y.1 ∈ A := Finset.mem_subtype.mp (Finset.mem_coe.mp hy)
    have hne : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    exact hI x.1 hx' y.1 hy' hne hadj
  rw [← hs]
  exact hind.card_le_indepNum

lemma four_le_L : 4 ≤ indepNeighborsCard G72.{u} ⟨0⟩ := by
  have := card_le_indepNeighbors G72.{u} ⟨0⟩ {⟨1⟩, ⟨2⟩, ⟨10⟩, ⟨11⟩}
    (by intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
    (by intro a ha b hb hab hadj
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        have h2 := hadj.2
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          revert h2 <;> decide)
  have hc : ({⟨1⟩, ⟨2⟩, ⟨10⟩, ⟨11⟩} : Finset V.{u}).card = 4 := by decide
  omega

-- Induced trees have at most five vertices

lemma no_triangle {α : Type*} {G : SimpleGraph α} {S : Set α} (hA : (G.induce S).IsAcyclic)
    {x y z : α} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z) : False := by
  let X : S := ⟨x, hx⟩
  let Y : S := ⟨y, hy⟩
  let Z : S := ⟨z, hz⟩
  have a1 : (G.induce S).Adj X Y := hxy
  have a2 : (G.induce S).Adj Y Z := hyz
  have a3 : (G.induce S).Adj X Z := hxz
  have n1 : X ≠ Y := a1.ne
  have n2 : Y ≠ Z := a2.ne
  have n3 : X ≠ Z := a3.ne
  let p : (G.induce S).Path X Z := ⟨Walk.cons a3 Walk.nil, by simp [n3]⟩
  let q : (G.induce S).Path X Z := ⟨Walk.cons a1 (Walk.cons a2 Walk.nil), by simp [n1, n2, n3]⟩
  have h := congrArg (fun r : (G.induce S).Path X Z => r.1.length) ((hA.subsingleton_path X Z).elim p q)
  simp [p, q] at h

lemma no_square {α : Type*} {G : SimpleGraph α} {S : Set α} (hA : (G.induce S).IsAcyclic)
    {x y z w : α} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hw : w ∈ S)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hzw : G.Adj z w) (hwx : G.Adj w x)
    (hxz : x ≠ z) (hyw : y ≠ w) : False := by
  let X : S := ⟨x, hx⟩
  let Y : S := ⟨y, hy⟩
  let Z : S := ⟨z, hz⟩
  let W : S := ⟨w, hw⟩
  have a1 : (G.induce S).Adj X Y := hxy
  have a2 : (G.induce S).Adj Y Z := hyz
  have a3 : (G.induce S).Adj X W := hwx.symm
  have a4 : (G.induce S).Adj W Z := hzw.symm
  have n1 : X ≠ Y := a1.ne
  have n2 : Y ≠ Z := a2.ne
  have n3 : X ≠ W := a3.ne
  have n4 : W ≠ Z := a4.ne
  have n5 : X ≠ Z := fun h => hxz (congrArg Subtype.val h)
  let p : (G.induce S).Path X Z := ⟨Walk.cons a1 (Walk.cons a2 Walk.nil), by simp [n1, n2, n5]⟩
  let q : (G.induce S).Path X Z := ⟨Walk.cons a3 (Walk.cons a4 Walk.nil), by simp [n3, n4, n5]⟩
  have h := congrArg (fun r : (G.induce S).Path X Z => r.1.support) ((hA.subsingleton_path X Z).elim p q)
  simp [p, q] at h
  exact hyw (congrArg Subtype.val h)

lemma cross {α : Type*} {G : SimpleGraph α} {S : Set α} (hC : (G.induce S).Connected)
    (X : Set α) {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxX : x ∈ X) (hyX : y ∉ X) :
    ∃ a b, a ∈ S ∧ b ∈ S ∧ a ∈ X ∧ b ∉ X ∧ G.Adj a b := by
  obtain ⟨p⟩ := hC.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨d, -, h1, h2⟩ := p.exists_boundary_dart {w | w.1 ∈ X} hxX hyX
  exact ⟨d.fst.1, d.snd.1, d.fst.2, d.snd.2, h1, h2, d.adj⟩

lemma R_cross : ∀ a b : Fin 5, R a b = true → (a = 1 ∨ a = 2) → ¬ (b = 1 ∨ b = 2) → b = 0 := by
  decide

lemma tree_le (S : Finset V.{u}) (hT : (G72.induce (S : Set V.{u})).IsTree) : S.card ≤ 5 := by
  have hA := hT.isAcyclic
  have hC := hT.connected
  have hsum : S.card = ∑ i : Fin 5, (S.filter (fun x => cls x = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ (cls x)))
  rw [Fin.sum_univ_five] at hsum
  have mem : ∀ (i : Fin 5) x, x ∈ S.filter (fun x => cls x = i) ↔ x ∈ S ∧ cls x = i :=
    fun i x => Finset.mem_filter
  -- class 0 has one vertex, classes 1 and 3 have two
  have h0 : (S.filter (fun x => cls x = 0)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rw [cls_eq_zero ((mem 0 a).1 ha).2, cls_eq_zero ((mem 0 b).1 hb).2]
  have h1 : (S.filter (fun x => cls x = 1)).card ≤ 2 := by
    calc _ ≤ ({⟨1⟩, ⟨2⟩} : Finset V.{u}).card := by
          apply Finset.card_le_card
          intro a ha
          rcases cls_eq_one ((mem 1 a).1 ha).2 with h | h <;> simp [h]
      _ ≤ 2 := Finset.card_le_two
  have h3 : (S.filter (fun x => cls x = 3)).card ≤ 2 := by
    calc _ ≤ ({⟨10⟩, ⟨11⟩} : Finset V.{u}).card := by
          apply Finset.card_le_card
          intro a ha
          rcases cls_eq_three ((mem 3 a).1 ha).2 with h | h <;> simp [h]
      _ ≤ 2 := Finset.card_le_two
  -- a clique class meets S in at most two vertices
  have hK : ∀ i : Fin 5, R i i = true → ¬ 2 < (S.filter (fun x => cls x = i)).card := by
    intro i hi hlt
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hlt
    rw [mem] at ha hb hc
    refine no_triangle hA ha.1 hb.1 hc.1 ⟨hab, ?_⟩ ⟨hbc, ?_⟩ ⟨hac, ?_⟩ <;>
      simp only [ha.2, hb.2, hc.2, hi]
  -- two clique vertices exclude the hubs of their side
  have hKP : ∀ i j : Fin 5, R i i = true → R i j = true → R j i = true → i ≠ j →
      (S.filter (fun x => cls x = i)).card = 2 → (S.filter (fun x => cls x = j)).card = 0 := by
    intro i j hii hij hji hne h2
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp h2
    by_contra hne0
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne0)
    have ha : a ∈ S.filter (fun x => cls x = i) := by rw [he]; simp
    have hb : b ∈ S.filter (fun x => cls x = i) := by rw [he]; simp
    rw [mem] at ha hb hp
    have hpa : p ≠ a := ne_of_cls (by rw [hp.2, ha.2]; exact Ne.symm hne)
    have hpb : p ≠ b := ne_of_cls (by rw [hp.2, hb.2]; exact Ne.symm hne)
    refine no_triangle hA hp.1 ha.1 hb.1 ⟨hpa, ?_⟩ ⟨hab, ?_⟩ ⟨hpb, ?_⟩ <;>
      simp only [ha.2, hb.2, hp.2, hii, hji]
  -- a clique vertex with both hubs excludes the centre
  have hSq : ∀ i j : Fin 5, R 0 j = true → R j i = true → R i j = true → R j 0 = true →
      i ≠ j → i ≠ 0 → j ≠ 0 →
      1 ≤ (S.filter (fun x => cls x = i)).card → (S.filter (fun x => cls x = j)).card = 2 →
      (S.filter (fun x => cls x = 0)).card = 0 := by
    intro i j h0j hji hij hj0 hne hi0 hj0' hk hp2
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hk
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp hp2
    by_contra hne0
    obtain ⟨c, hc⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne0)
    have ha : a ∈ S.filter (fun x => cls x = j) := by rw [he]; simp
    have hb : b ∈ S.filter (fun x => cls x = j) := by rw [he]; simp
    rw [mem] at ha hb hk hc
    refine no_square hA hc.1 ha.1 hk.1 hb.1
      ⟨ne_of_cls (by rw [hc.2, ha.2]; exact Ne.symm hj0'), by simp only [hc.2, ha.2, h0j]⟩
      ⟨ne_of_cls (by rw [ha.2, hk.2]; exact Ne.symm hne), by simp only [ha.2, hk.2, hji]⟩
      ⟨ne_of_cls (by rw [hk.2, hb.2]; exact hne), by simp only [hk.2, hb.2, hij]⟩
      ⟨ne_of_cls (by rw [hb.2, hc.2]; exact hj0'), by simp only [hb.2, hc.2, hj0]⟩
      (ne_of_cls (by rw [hc.2, hk.2]; exact Ne.symm hi0)) hab
  -- without the centre, S lies on one side
  have hside : (S.filter (fun x => cls x = 0)).card = 0 →
      (S.filter (fun x => cls x = 1)).card + (S.filter (fun x => cls x = 2)).card = 0 ∨
      (S.filter (fun x => cls x = 3)).card + (S.filter (fun x => cls x = 4)).card = 0 := by
    intro hc0
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hl, hr⟩ := hcon
    obtain ⟨x, hx, hxX⟩ : ∃ x, x ∈ S ∧ (cls x = 1 ∨ cls x = 2) := by
      rcases Nat.eq_zero_or_pos (S.filter (fun x => cls x = 1)).card with h | h
      · obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (S.filter (fun x => cls x = 2)).card by
          omega)
        rw [mem] at hx
        exact ⟨x, hx.1, Or.inr hx.2⟩
      · obtain ⟨x, hx⟩ := Finset.card_pos.mp h
        rw [mem] at hx
        exact ⟨x, hx.1, Or.inl hx.2⟩
    obtain ⟨y, hy, hyX⟩ : ∃ y, y ∈ S ∧ (cls y = 3 ∨ cls y = 4) := by
      rcases Nat.eq_zero_or_pos (S.filter (fun x => cls x = 3)).card with h | h
      · obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < (S.filter (fun x => cls x = 4)).card by
          omega)
        rw [mem] at hy
        exact ⟨y, hy.1, Or.inr hy.2⟩
      · obtain ⟨y, hy⟩ := Finset.card_pos.mp h
        rw [mem] at hy
        exact ⟨y, hy.1, Or.inl hy.2⟩
    have hyX' : ¬ (cls y = 1 ∨ cls y = 2) := by
      rcases hyX with h | h <;> rw [h] <;> decide
    obtain ⟨a, b, ha, hb, haX, hbX, hab⟩ :=
      cross hC {v | cls v = 1 ∨ cls v = 2} hx hy hxX hyX'
    have hb0 := R_cross _ _ hab.2 haX hbX
    have : b ∈ S.filter (fun x => cls x = 0) := (mem 0 b).2 ⟨hb, hb0⟩
    rw [Finset.card_eq_zero.mp hc0] at this
    simp at this
  have k2 := hK 2 (by decide)
  have k4 := hK 4 (by decide)
  have p21 := hKP 2 1 (by decide) (by decide) (by decide) (by decide)
  have p43 := hKP 4 3 (by decide) (by decide) (by decide) (by decide)
  have s21 := hSq 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have s43 := hSq 4 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  omega

lemma tree_ub : largestInducedTreeSize G72.{u} ≤ 5 := by
  unfold largestInducedTreeSize
  apply csSup_le'
  rintro n ⟨s, rfl, hs⟩
  exact tree_le s hs

lemma final (m : ℕ) (hm : 4 ≤ m) :
    ¬ (⌈averageEccentricity G72.{u} + (m : ℝ) / 3⌉ ≤ (largestInducedTreeSize G72.{u} : ℝ)) := by
  intro h
  have he := avg_ge.{u}
  have ht : (largestInducedTreeSize G72.{u} : ℝ) ≤ 5 := by exact_mod_cast tree_ub
  have hc := Int.le_ceil (averageEccentricity G72.{u} + (m : ℝ) / 3)
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

end OMA72

theorem OMA.disproof : ¬ (type_of% @WrittenOnTheWallII.GraphConjecture72.conjecture72) := by
  intro h
  have h1 := h OMA72.G72 OMA72.G72_connected
  exact OMA72.final _ (le_trans OMA72.four_le_L
    (Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))) h1
