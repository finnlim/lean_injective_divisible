import group_theory.subgroup
import algebra
import tactic
open function

-- Injective abelian group
class is_inj_abgp (G : Type) [add_comm_group G] : Prop :=
  (inj_extd : ∀ (H K : Type) [add_comm_group H] [add_comm_group K]
  (i : H →+ K) 
  (h_subHK : injective i), (∀f : H →+ G, ∃f_extd : K →+ G, (∀h : H, f_extd (i h) = f h)))

-- Divisible abelian group
class is_div_abgp (G : Type) [add_comm_group G] : Prop :=
  (nat_div : ∀ (n : ℤ) (g : G) (n_nonzero : n ≠ 0), ∃ (h : G), n •ℤ h = g)
  -- •ℤ is the ℤ-scalar mult.

-- Injective abelian group is divisible.
theorem inj_is_div_abgp (G : Type) [add_comm_group G] : is_inj_abgp G → is_div_abgp G :=
begin
  /-
  Outline:
    Construct a morphism f: ℤ → G given by g-mult.
    Construct a morphism i: ℤ → ℤ given by n-mult.
    Apply these to the injectivity hypothesis
    Let the image of 1 be g0
    Since n*1 = n, n*g0 = g.
  -/

  -- Setup 
  intro G_is_inj,
  refine ⟨_⟩, -- Elaborate the goal
  intros n g n_nonzero,

  -- Define two functions f and i
  set f: ℤ →+ G := {to_fun := λ n, n •ℤ g,
    map_zero' := by simp,
    map_add' := by exact add_gsmul g} with fdef,
  set i: ℤ →+ ℤ := {to_fun := λ m, m •ℤ n,
    map_zero' := by simp,
    map_add' := by exact add_gsmul n} with idef,

  -- i is injective (Clean this section)
  have i_inj : injective i :=
    begin
      rw function.injective,
      intros a b h_iaib,
      rw idef at h_iaib,
      simp at h_iaib,
      cases h_iaib, exact h_iaib, tauto,
    end,

  -- Feed our earlier constructions into the assumption that G is injective
  cases G_is_inj,
  specialize G_is_inj ℤ ℤ i i_inj f,
  cases G_is_inj with f_extd G_is_inj_h,
  specialize G_is_inj_h 1,

  -- Start with f 1 = g and change this to n •ℤ ⇑f_extd 1 = g
  have h_f1_is_g : f 1 = g, by apply one_gsmul g,
  rw h_f1_is_g at G_is_inj_h,
  rw (by simp : i 1 = n) at G_is_inj_h,
  rw ← (by simp : n •ℤ 1 = n) at G_is_inj_h,
  rw ← (by exact (add_monoid_hom.map_gsmul f_extd 1 n).symm 
    : n •ℤ (f_extd 1) = f_extd (n •ℤ 1))
    at G_is_inj_h,
  
  -- Use f_extd 1 and finish
  use (f_extd 1), exact G_is_inj_h,
end

/-
Takes the data of H ⊆ K and f: H → G
and asks for an intermediate H ⊆ H1 ⊆ K such that 
f_extd: H1 → G is a lift of f: H → G.
-/
structure extd_abhom 
{H K G : Type} [add_comm_group H] [add_comm_group K] [add_comm_group G]
(i0 : H →+ K) (i0_inj: injective i0) (f : H →+ G) := 
  (H1: Type)
  [h_H1: add_comm_group H1]
  (i1 : H →+ H1)
  (i2 : H1 →+ K)
  (i1_inj: injective i1)
  (i2_inj: injective i2)
  (h_comm_HH1K : i2 ∘ i1 = i0) -- commuting inclusions
  (f_extd : H1 →+ G)
  (h_lift: f_extd ∘ i1 = f) -- f_extd is a lift of f

-- Declare that H1 in an extd_abhom is an add_comm_group.
instance {H K G : Type} [add_comm_group H] [add_comm_group K] [add_comm_group G] (i0 : H →+ K) (i0_inj: injective i0) (f : H →+ G)
{f_ex : extd_abhom i0 i0_inj f} : add_comm_group f_ex.H1 := f_ex.h_H1

/-
Partial order on extd_abhom
Each time we need to sandwich between H,K and fix the target G.
-/
def ord_extd_abhom
{H K G : Type} [add_comm_group H] [add_comm_group K] [add_comm_group G]
{i0 : H →+ K} {i0_inj: injective i0} {f : H →+ G}
: (extd_abhom i0 i0_inj f) → (extd_abhom i0 i0_inj f) → Prop := 
begin
  intros hom1 hom2,
  exact (∃j : hom1.H1 →+ hom2.H1, 
  ∃j_inj : injective j, -- hom.H1 ⊆ hom2.H1
  (hom2.i2 ∘ j = hom1.i2) ∧ -- comm. of inclusion
  (hom2.f_extd ∘ j = hom1.f_extd)), -- comm. of lifts
end


def ord_extd_abhom_trans {H K G : Type} [add_comm_group H] [add_comm_group K] [add_comm_group G]
(i0 : H →+ K) (i0_inj: injective i0) (f : H →+ G)
{f1 f2 f3 : extd_abhom i0 i0_inj f} : ord_extd_abhom f1 f2 → ord_extd_abhom f2 f3 → ord_extd_abhom f1 f3 :=
begin
  sorry,
end

-- To check that the above setup works correctly.
-- def ii : ℤ →+ ℤ := { to_fun := id,
--   map_zero' := by tauto,
--   map_add' := by tauto}
-- #check set (extd_abhom ii (by tauto) ii)


/-
(h : ∀ (c : set α), zorn.chain r c → (∃ (ub : α), ∀ (a : α), a ∈ c → r a ub)) (trans : ∀ {a b c : α}, r a b → r b c → r a c) 
-/



-- Divisble abelian group is injective.
theorem div_is_inj_abgp (G : Type) [add_comm_group G] : is_div_abgp G → is_inj_abgp G :=
begin
  /-
  Outline:
    Find maximally extendible H0 such that H ⊆ H0 ⊆ K
    This is done using Zorn's lemma.
    Proof by contradiction; if H0 = K, we are done. So suppose otherwise.
    If H0 ⊆ K and not the same, then ∃ k ∈ K, k ∉ H0
    Either (ℤ ⬝ k) ∩ H = {0} or not
    If empty intersection, map anywhere
    If nonempty intersection, n ⬝ k ∈ H, nonzero. 
    Let g = f (n ⬝ k)
    find g0 such that n ⬝ g0 = g by div_abgp G
    Define an extension f1 : (H ∨ ⟨k⟩) → G by mapping k to g0
    Show well-definedness (?)
    Contradiction to maximality.
  -/

  /-
   def zorn.chain {α : Type u} (r : α → α → Prop) (c : set α) : Prop

   theorem zorn.exists_maximal_of_chains_bounded {α : Type u} {r : α → α → Prop} (h : ∀ (c : set α), zorn.chain r c → (∃ (ub : α), ∀ (a : α), a ∈ c → r a ub)) (trans : ∀ {a b c : α}, r a b → r b c → r a c) :
   ∃ (m : α), ∀ (a : α), r m a → r a m

   simply need to define a set α and a relation r (partial order)...
  -/

  intro divG,
  refine ⟨_⟩,
  intros H K i hk hK wer usw, -- For any H ⊆ K, f: H → G,
  resetI, -- telling that H, K are groups, from local context to type class
  -- zorn.exists_maximal_of_chains_bounded
  -- zorn.max_chain

  -- set of all extd_moprhs...
  -- set α is α → Prop
  -- extd_morph : set (H1 -> G)
  

  -- let extd_morphs : (H1 : Type) [add_comm_group H1] ()
  

  sorry,
end



-- An abelian group is injective iff divisible.
theorem inj_iff_div_abgp (G : Type) [add_comm_group G] : is_inj_abgp G ↔ is_div_abgp G :=
begin
  split, exact inj_is_div_abgp G, exact div_is_inj_abgp G,
end


/-
Dump


/-
  extd_abgp_hom i1 i2 f f_extd is true when
  H H1 K G are abelian groups
  H ⊆ H1 ⊆ K (i1, i2 are the inclusion hom.)
  f: H → G, f_extd H1 → G, f_extd restricts to f at H.
-/
class extd_abgp_hom 
{H H1 K G : Type} [add_comm_group H] [add_comm_group H1] [add_comm_group K] [add_comm_group G] 
(i1 : H →+ H1) (i2 : H1 →+ K) (f : H →+ G) (f_extd : H1 →+ G) : Prop := 
  (h_extd_hom: ∀h : H, f_extd (i1 h) = f h)
  (i1_inj : injective i1)
  (i2_inj : injective i2)

#check extd_abgp_hom -> extd_abgp_hom -> Prop

/-
  partial_order_extd_abgp_hom i1_1 i2_1 i1_2 i2_2 is true when
  H H1 H2 K G are abelian groups
  H ⊆ H1 ⊆ K, H ⊆ H2 ⊆ K
  we have extensions f_extd1 : H1 → G, f_extd2 : H2 → G of f
  f_extd2 is an extension of f_extd1
-/
def partial_order_extd_abgp_hom {H H1 H2 K G : Type} [add_comm_group H] [add_comm_group H1] [add_comm_group H2] [add_comm_group K] [add_comm_group G]
(i1_1 : H →+ H1) (i2_1 : H1 →+ K) 
(i1_2 : H →+ H2) (i2_2 : H2 →+ K) 
(f : H →+ G) (f_extd1 : H1 →+ G) (f_extd2 : H2 →+ G) 
[extd_abgp_hom i1_1 i2_1 f f_extd1]
[extd_abgp_hom i1_2 i2_2 f f_extd2]
: Prop := 
  (∃j : H1 →+ H2, extd_abgp_hom j i2_2 f_extd1 f_extd2)
-/


/-
  partial_order_extd_abgp_hom i1_1 i2_1 i1_2 i2_2 is true when
  H H1 H2 K G are abelian groups
  H ⊆ H1 ⊆ K, H ⊆ H2 ⊆ K
  we have extensions f_extd1 : H1 → G, f_extd2 : H2 → G of f
  f_extd2 is an extension of f_extd1
-/

-- instance {G : mygroup} : add_comm_group G.G := G.hG

-- (∃j : H1 →+ H2, extd_abgp_hom j i2_2 f_extd1 f_extd2)

/-
def partial_order_extd_abgp_hom {H H1 H2 K G : Type} [add_comm_group H] [add_comm_group H1] [add_comm_group H2] [add_comm_group K] [add_comm_group G]
(i1_1 : H →+ H1) (i2_1 : H1 →+ K) 
(i1_2 : H →+ H2) (i2_2 : H2 →+ K) 
(f : H →+ G) (f_extd1 : H1 →+ G) (f_extd2 : H2 →+ G) 
[extd_abgp_hom i1_1 i2_1 f f_extd1]
[extd_abgp_hom i1_2 i2_2 f f_extd2]
: Prop := 
  (∃j : H1 →+ H2, extd_abgp_hom j i2_2 f_extd1 f_extd2)
#check extd_abgp_hom
-/