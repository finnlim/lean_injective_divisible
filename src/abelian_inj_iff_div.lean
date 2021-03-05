import group_theory.subgroup
import algebra
import tactic
import logic.function.basic
import order.zorn
import data.set.disjointed
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
  exact (∃j : hom1.H1 →+ hom2.H1, ∃j_inj : injective j, -- hom.H1 ⊆ hom2.H1
  (hom2.i2 ∘ j = hom1.i2) ∧ -- comm. of inclusion
  (j ∘ hom1.i1 = hom2.i1) ∧ -- comm. of inclusion
  (hom2.f_extd ∘ j = hom1.f_extd)), -- comm. of lifts
end


def ord_extd_abhom_trans {H K G : Type} [add_comm_group H] [add_comm_group K] [add_comm_group G]
(i0 : H →+ K) (i0_inj: injective i0) (f : H →+ G) {f1 f2 f3 : extd_abhom i0 i0_inj f}
: 
ord_extd_abhom f1 f2 → ord_extd_abhom f2 f3 → ord_extd_abhom f1 f3 :=
begin
  -- intros f1 f2 f3,
  intros ex_f1f2 ex_f2f3,

  -- Notations
  set H1 := f1.H1,
  set H2 := f2.H1,
  set H3 := f3.H1,

  let i11 := f1.i1, let i11_inj := f1.i1_inj,
  let i21 := f2.i1, let i21_inj := f2.i1_inj,
  let i31 := f3.i1, let i31_inj := f3.i1_inj,

  let i12 := f1.i2, let i12_inj := f1.i2_inj,
  let i22 := f2.i2, let i22_inj := f2.i2_inj,
  let i32 := f3.i2, let i32_inj := f3.i2_inj,

  rcases ex_f1f2 with ⟨j1, j1_inj, i12_comm, i12_comm2, ex12_comm⟩,
  rcases ex_f2f3 with ⟨j2, j2_inj, i23_comm, i23_comm2, ex23_comm⟩,

  -- j3 is to be used.
  let j3 := j2.comp j1, -- composition in add_comm_group morphisms
  have j3_inj : injective j3 := by tauto,

  use j3, use j3_inj,
  split,
  -- Show that i32 ∘ j3 = i12
    calc
    (f3.i2) ∘ j3 = (i32 ∘ j2) ∘ j1 : by refl
    ... = i22 ∘ j1 : by tauto
    ... = i12 : by tauto, -- by exact i12_comm, 
  split,
  -- Show that j3 ∘ i11 = i31
    calc
    j3 ∘ (f1.i1) = (j2 ∘ j1) ∘ i11 : by refl
    ... = j2 ∘ i21 : by tauto
    ... = i31 : by tauto, -- by exact i23_comm2,
  -- Show that extension property is transitive
    calc
    f3.f_extd ∘ j3 = (f3.f_extd ∘ j2) ∘ j1 : by refl
    ... = f2.f_extd ∘ j1 : by tauto
    ... = f1.f_extd : by tauto, -- by exact ex12_comm,
end


-- Every chain of extd_abhom's have an upper bound.
def ord_extd_abhom_upper {H K G : Type} [add_comm_group H] [add_comm_group K] [add_comm_group G] {i0 : H →+ K} {i0_inj: injective i0} {f : H →+ G}
: ∀(chain : set (extd_abhom i0 i0_inj f)), zorn.chain ord_extd_abhom chain 
→ (∃ (ub : extd_abhom i0 i0_inj f), ∀ (a : extd_abhom i0 i0_inj f), a ∈ chain → ord_extd_abhom a ub) :=
begin
  intros chain is_chain,
  rw zorn.chain at is_chain,
  sorry,
end


-- kevin: this is not a thing?
lemma exists_notin_of_ne_top {G : Type} [add_comm_group G] {H : add_subgroup G} (h : H ≠ ⊤) :
∃ x : G, x ∉ H := 
begin
  revert h,
  contrapose!,
  intro h,
  rw eq_top_iff,
  intros y hy,
  apply h,
end

#check add_monoid_hom.mrestrict

@[to_additive]
def monoid_hom.restrict {G K : Type*} [group G] [group K] 
  {f : G →* K} (H : subgroup G) : H →* K := f.comp H.subtype


lemma extd_mor_from_add_subgps {K G : Type} [add_comm_group K] [add_comm_group G] {H1 H2 : add_subgroup K} (f1 : H1 →+ G) (f2 : H2 →+ G) (f_res_agree : f1.mrestrict (H1 ⊓ H2 : add_subgroup H1) = f2.restrict (H1 ⊓ H2 : add_subgroup K) : (∃f_extd : (H1 ⊔ H2 : add_subgroup K) →+ G, f_extd.restrict H1 = f_extd.restrict H2) :=
begin
  sorry,
end


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

  intro divG,
  refine ⟨_⟩,
  intros H K H_is_abgp K_is_abgp i0 i0_inj f, -- For any H ⊆ K, f: H → G,
  resetI, -- telling that H, K are groups, from local context to type class

  -- Zorn's Lemma
  have exist_max_extn : ( ∃ (m : extd_abhom i0 i0_inj f), ∀ (a : extd_abhom i0 i0_inj f), ord_extd_abhom m a → ord_extd_abhom a m ) := 
  zorn.exists_maximal_of_chains_bounded ord_extd_abhom_upper (λ _ _ _ , ord_extd_abhom_trans i0 i0_inj f),
  cases exist_max_extn with max_extn h_max_extn,

  -- Notations
  let max_H1 := max_extn.H1,
  let max_i1 := max_extn.i1,
  let max_i2 := max_extn.i2,
  let max_f := max_extn.f_extd,
  have max_h_H1 := max_extn.h_H1,
  have max_i1_inj := max_extn.i1_inj,
  have max_i2_inj := max_extn.i2_inj,
  have max_f_lift := max_extn.h_lift,

  let max_H1_sub := max_i2.range,

  -- Proof by contradiction on the maximal extension taking up everything
  have max_H1_is_K : max_H1_sub = ⊤,
  -- rw surjective,
  by_contra not_top, -- what if this element k is missing
  have not_top_2 : max_H1_sub ≠ ⊤ := by tauto,
  have not_top_has_elt := exists_notin_of_ne_top not_top_2,
  cases not_top_has_elt with k k_notin_top,

  let max_H1_bigger := max_H1_sub ⊔ (add_subgroup.closure {k}),

  -- Assuming that n.k is in max_H1 for some n > 0
  -- have mult_k_into_maxH1 : (∃n : ℕ, ∃h : max_H1_sub, n •ℕ k = h),
  sorry,
end


-- An abelian group is injective iff divisible.
theorem inj_iff_div_abgp (G : Type) [add_comm_group G] : is_inj_abgp G ↔ is_div_abgp G :=
begin
  split, exact inj_is_div_abgp G, exact div_is_inj_abgp G,
end