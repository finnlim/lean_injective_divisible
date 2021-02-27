import group_theory.subgroup
import algebra
import tactic

open function

-- Injective abelian group
class is_inj_abgp (G : Type) [add_comm_group G] : Prop :=
  (inj_extd : ∀ (H K : Type) [add_comm_group H] [add_comm_group K]
  (i : H →+ K) (h_subHK : injective i), (∀f : H →+ G, ∃f_extd : K →+ G, (∀h : H, f_extd (i h) = f h)))

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
  let i_inj : injective i :=
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
  clear i_inj, -- Clunky proof removed right after usage
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
  intros H K i hk hK wer usw, -- For any H ⊆ K, f: H → G,
  resetI, -- telling that H, K are groups, from local context to type class
  -- zorn.exists_maximal_of_chains_bounded
  -- zorn.max_chain
  

  sorry,
end

-- An abelian group is injective iff divisible.
theorem inj_iff_div_abgp (G : Type) [add_comm_group G] : is_inj_abgp G ↔ is_div_abgp G :=
begin
  split, exact inj_is_div_abgp G, exact div_is_inj_abgp G,
end