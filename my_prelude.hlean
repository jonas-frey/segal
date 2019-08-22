import prop_trunc types.prod types.fin hit.pushout types.fiber

open funext eq trunc is_trunc prod sum pi function 
     is_equiv sigma sigma.ops equiv nat eq equiv

universe variables u v

notation `↑` := eq_of_homotopy   -- type \u
notation `⇑` := eq_of_homotopy2   -- type \u
notation `⤊` := eq_of_homotopy3   -- what to type?



-- backwards transport
definition transport' [subst] [reducible] [unfold 5] 
   {A} (P : A → Type) {x y : A} (p : x = y) (u : P y) : P x 
:= by induction p; exact u

reserve infixl ` ► `:74
reserve infixr ` ◄ `:74
infix  ` ► ` := λ x p, transport _ p x
infixr ` ◄ ` := transport' _

definition pa {A} {B : A → Type} {f g : Π a, B a} (p : f = g) (a : A) 
: f a = g a := by induction p; reflexivity

definition hwhisker_right' {A B C} {g g' : B → C} (H : g ~ g') (f : A → B) 
: g ∘ f ~ g' ∘ f := λa, H (f a)

infix  ` ▻ `:76 := pa -- type \t4
infixr ` ◅ `:76 := ap -- type \t8
infixr ` ◁ `:77 := hwhisker_left -- type \Tw
infix  ` ▷ `:77 := hwhisker_right' -- type \Tw

definition ap_const  {A B} {a a' : A} {b : B} (p : a = a') 
: (λ a, b) ◅ p = rfl := eq.rec rfl p

definition path_lift {A} {B : A → Type} {a a' : A} (p : a = a') (b : B a) 
: b ► p =[p] b := by induction p; constructor

definition path_lift' {A} {B : A → Type} {a a' : A} (p : a = a') (b' : B a') 
: b' =[p] p ◄ b' := by induction p; constructor

definition po_of_eq {A} {B : A → Type} {a: A} {b b' : B a} (p : b = b') 
: b =[refl a] b' := begin induction p, constructor end


-- pathovers of paths are paths between compositions
definition po_path_left {A B} {a a' : A} {b : B} {m : A → B} 
   (p : a = a') (q : m a = b) (q' : m a' = b) : q = m ◅ p ⬝ q' → q =[p] q' 
:= begin induction p, λ r, po_of_eq (r ⬝ !idp_con) end

definition po_path_right {A B} {a a' : A} {b : B} {m : A → B} 
   (p : a = a') (q : b = m a) (q' : b = m a') : q ⬝ m ◅ p = q' → q =[p] q' 
:= begin induction p, λr, po_of_eq r end

definition po_path {A B} {a a' : A} {m n : A → B} 
  (p : a = a') (q : m a = n a) (q' : m a' = n a') : q ⬝ n ◅ p = m ◅ p ⬝ q' → q =[p] q' 
:= begin induction p, intro H, apply po_of_eq,
   calc 
     q = q ⬝     rfl  : con_idp
   ... = q ⬝ n ◅ rfl  : concat q ◅ !ap_idp
   ... = m ◅ rfl ⬝ q' : H
   ... =     rfl ⬝ q' : (λ r, concat r q') ◅ !ap_idp
   ... =           q' : idp_con
   end

definition pathover_of_homotopy {A B} {C : A → B → Type} {a a' : A} 
  (p : a = a')(f : Π b, C a b)(f' : Π b, C a' b) : (Π b, f b =[p] f' b) → f=[p] f'
:= begin intro H,induction p, apply po_of_eq, apply eq_of_homotopy, intro b, 
   apply @eq_of_pathover_idp _ _ a, apply H end

definition nfext0 {A : Type} {B : A → Type} {f g : Π a, B a} (p q : f ~ g)
: (Π a, p  a = q  a) → p = q  := λH, ↑H

definition nfext {A : Type} {B : A → Type} {f g : Π a, B a} (p q : f = g)
:  (Π a, p ▻ a = q ▻ a) → p = q 
:= begin intro H, note z := nfext0 (apd10 p) (apd10 q), 
   assert K : apd10 p = apd10 q → p = q, intro, 
   refine _ ⬝ is_equiv.left_inv apd10 q, symmetry,
   refine _ ⬝ is_equiv.left_inv apd10 p, symmetry,
   exact ap _ a, apply K, clear K, apply z, intro a, apply H
   end

definition aux2 {A} {B : A → Type} {f g : Π a, B a} (H : f ~ g) (a : A) 
:  ↑H ▻ a = H a := right_inv apd10 H ▻ a

definition apap {A B : Type} (f : A → B) {x y : A} {p q : x = y} 
:  p = q → f ◅ p = f ◅ q := begin intro, apply ap (ap f), assumption end

infix ` ◅◅ `:76 := apap -- type \t8

section
  -- flipping equalities between compositions
  variables {A : Type} {a0 a1 a2 : A} 
            {p2 : a0 = a1} {p0 : a1 = a2} {p1 : a0 = a2} 
  definition frri : p2 = p1 ⬝ p0⁻¹ → p2 ⬝ p0 = p1 
  := begin induction p0, exact id end
  definition frli : p0 = p2⁻¹ ⬝ p1 → p2 ⬝ p0 = p1 
  := begin induction p2, λa, !idp_con⬝a⬝!idp_con end
  definition flri :  p1 ⬝ p0⁻¹ = p2 → p1 = p2 ⬝ p0 
  := begin induction p0, exact id end
  definition flli : p2⁻¹ ⬝ p1 = p0 → p1 = p2 ⬝ p0 
  := begin  induction p2, λa, !idp_con⁻¹⬝a⬝!idp_con⁻¹ end
  definition flr : p2 ⬝ p0 = p1 → p2 = p1 ⬝ p0⁻¹ 
  := begin induction p0, exact id end
  definition fll : p2 ⬝ p0 = p1 → p0 = p2⁻¹ ⬝ p1 
  := begin  induction p2, λ a, !idp_con⁻¹⬝a⬝!idp_con⁻¹ end
  definition frr : p1 = p2 ⬝ p0 → p1 ⬝ p0⁻¹ = p2 
  := begin induction p0, exact id end
  definition frl : p1 = p2 ⬝ p0 → p2⁻¹ ⬝ p1 = p0 
  := begin induction p2, λa, !idp_con⬝a⬝!idp_con end
end

definition total_equiv (A : Type) (B C : A → Type) 
  : (∀ a, B a ≃ C a) → sigma B ≃ sigma C
  := begin
    intro ef, fapply equiv.MK, 
    { intro s, induction s with a b, exact dpair a (ef a b)},
    { intro s, induction s with a c, exact dpair a ((ef a)⁻¹ c)},
    { intro p, induction p, refine dpair _ ◅ _, apply right_inv},
    { intro p, induction p, refine dpair _ ◅ _, apply left_inv},
  end

namespace trunc
  definition true : Prop.{0} := Prop.mk unit (is_trunc_succ unit -2)

  definition and : Prop.{u} → Prop.{v} → Prop.{max u v} 
    := λ p q, Prop.mk (p × q) !is_trunc_prod

  notation A ∧ B    := and A B
end trunc

namespace fin
  definition emb [coercion] {n : ℕ} (i : fin n) : fin (nat.succ n) := 
  begin
  cases i with i p, fconstructor , exact i, apply nat.le_trans, exact p, apply le_succ
  end
end fin

lemma contr_point {A : Type} (b : is_contr A) : A :=
begin
induction b with b, induction b with c ce, exact c,
end

lemma is_equiv_of_contr_fiber {A B : Type} (f : A → B) 
:  (∀ b, is_contr (fiber f b)) → is_equiv f
:= begin
   intro H, fapply adjointify, intro b, exact fiber.point (contr_point (H b)), intro b, 
   exact fiber.point_eq (contr_point (H b)), intro a, note z := H (f a), 
   assert K : is_prop (fiber f (f a)), apply is_trunc_succ, 
   assert L : contr_point (H (f a)) = fiber.mk a rfl,
   apply is_prop.elim, apply eq.ap fiber.point L
   end

definition eq_of_feq {A B : Type} (f : A → B) [H : is_equiv f] {a a' : A} 
  : f a = f a' → a = a' := (eq_equiv_fn_eq_of_is_equiv f a a')⁻¹ᶠ

definition precompose [unfold_full] {A B} C (f : A → B) 
: (B → C) → (A → C) := λ h, h ∘ f

definition postcompose [unfold_full] A {B C} (g : B → C) 
: (A → B) → (A → C) := λ h, g ∘ h

definition is_equiv_precompose_of_is_equiv [instance] {A B C} 
  (f : A → B) [H : is_equiv f] : is_equiv (precompose C f)
:=  is_equiv.rec_on H $ λ g linv rinv adj, adjointify _ 
    (precompose C g) (λ h, ↑(h ◁ rinv)) (λ k, ↑(k ◁ linv))

definition is_equiv_postcompose_of_is_equiv [instance] {A B C}
  (f : B → C) [H : is_equiv f] : is_equiv (postcompose A f)
:= is_equiv.rec_on H $ λ g linv rinv adj, adjointify 
  (λh, f ∘ h) (λk, g ∘ k) (λh, ↑(linv ▷ h)) (λk, ↑(rinv ▷ k))

definition equiv_functionals_of_equiv {A B C} 
: (A ≃ B) → (A → C) ≃ (B → C) := λ e, equiv.mk (precompose C e⁻¹ᶠ) _

definition equiv_families_of_equiv {A B C} : 
(B ≃ C) → (A → B) ≃ (A → C) := λ e, equiv.mk (postcompose A e) _
