import hit.pushout hit.trunc arity my_prelude prop_join 
       ifin vector types.sigma

open trunc is_trunc nat pi prod function is_equiv ifin pushout equiv 
     eq vector sigma prod.ops trunc sigma.ops bool

universe u

definition tpower : Type.{0} → ℕ → Type.{0} 
  := begin intros A n, induction n with n R, exact unit, exact A × R 
     end

definition proj {A : Type.{0}} {n : ℕ} (i : ifin n) : tpower A n → A
  := begin induction i with n' n' i' p, exact pr1, exact p ∘ pr2 end

definition is_trunc_tpower [instance] n A i [H : is_trunc i A] 
  :  is_trunc i (tpower A n)
  := begin induction n, apply is_trunc_of_is_contr, 
           apply is_contr_unit, apply is_trunc_prod, apply v_0 end

notation `tr` x    := trunctype.mk x _ --!is_trunc_pi
notation A ` ^ ` n := tpower A n -- vector A n --ifin n → A
prefix  `#`:100    := nat.succ
notation `~`i      := ifin_of_fin $ mk i dec_star
definition teq [constructor] {n : ℕ₋₂} {A : trunctype (n.+1)} (x y : A)
  :  trunctype n := trunctype.mk (x=y) !is_trunc_eq
infix ` == `:50 := teq
prefix `∨l`:100 := or.intro_left
prefix `∨r`:100 := or.intro_right
infix ` * ` := λ v i, proj i v

axiom I : Set.{0}
axioms (S T : I)
axiom LEQ : I → I → Prop.{0}
infix ` ≼ `:50 := LEQ
axiom REFL  (x     : I) : x ≼ x
axiom TRANS (x y z : I) : x ≼ y → y ≼ z → x ≼ z
axiom ASYM  (x y   : I) : x ≼ y → y ≼ x → x = y
axiom LIN   (x y   : I) : x ≼ y ∨ y ≼ x
axiom SMIN  (x     : I) : S ≼ x
axiom TMAX  (x     : I) : x ≼ T
axiom SNEQT             : S ≠ T

-- enumeration set off by 1
definition delta (n : ℕ) (v : I^#n) : Prop.{0} 
  := tr∀ i, v * emb i ≼ v * ifs i
definition boundary (n : ℕ) (w : I ^#n) : Prop.{0}
  := delta n w ∧ (w*ifz = S ∨ w*maxi = T ∨ ∃ i, w * emb i = w * ifs i)
-- these are the inner horns
definition horn (n : ℕ) (j : ifin n) (w : I^#n) : Prop.{0}
  := delta n w ∧ (w*ifz=S ∨ w*maxi=T ∨ ∃i, i≠j × w * emb i = w * ifs i)
definition spine (n : ℕ) (v : I^#n) : Prop.{0} 
  := delta n v ∧ tr∀ i, v*i = S ∨ v*i = T

definition Δ       (n)     : Set.{0}     := trΣ v, delta n v
definition Λ       (n) (j) : Set.{0}     := trΣ v, horn n j v
definition δΔ      (n)     : Set.{0}     := trΣ v, boundary n v
definition Λ_to_Δ  (n) (j) : Λ n j → Δ n := sigma.total $ λ v, pr1
definition δΔ_to_Δ (n)     : δΔ n → Δ n  := sigma.total $ λ v, pr1

definition segal n j (A : Type) : Type 
  := is_equiv $ precompose A $ Λ_to_Δ n j 

theorem segal_exp_closed n j (A B : Type)
  :  segal n j A → segal n j (B → A)
  := λ H, is_equiv.rec_on H $ λ fill rinv linv adj, adjointify _
       (λ f h b, fill (λ v: Λ n j, f v b) h)
       (λh, ↑(λ v, ↑(λb, rinv (λ v, h v b) ▻ v)))
       (λf, ↑(λ v, ↑(λb, linv (λ v, f v b) ▻ v)))

definition cell {A : Type} {n : ℕ} (b : δΔ n → A) : Type 
  := Σ s : Δ n → A, s ∘ δΔ_to_Δ n = b

-- 1-simplex, 1-horn, 1-spine
definition Δ1 := I
definition δΔ1 := Σ i, S=i ∨ T=i

check @or_pushout

definition blarb : δΔ1 ≃ bool :=
begin 
refine (or_pushout (λi, S==i) (λi, T==i))⁻¹ᵉ ⬝e _,
fapply equiv.MK,
intro a, induction a, exact ff, exact tt,
induction x, induction a_1, exfalso,
exact SNEQT (a_1⬝a_2⁻¹),
intro b, induction b,
apply inl, exact dpair S rfl,
apply inr, exact dpair T rfl,
intro b, induction b, reflexivity,
reflexivity, intro a,
induction a, induction x, induction a_1,
reflexivity, 
induction x, induction a_1, reflexivity,
induction x, induction a_1, 
induction a_2, exfalso, exact SNEQT a_1
end

definition SS {n : ℕ}  : I^n := nat.rec unit.star (λ a, pair S) n
definition TT {n : ℕ}  : I^n := nat.rec unit.star (λ a, pair T) n
definition ISS {n : ℕ} : I → I^#n := λi, (i,SS)
definition rem {n : ℕ} : I^n → I^#n := λv, (T,v)

definition xxyy {A} {n} (f:I→A) (g:I^#n→A) (p : f T = g SS)
  :  Σ h : I^##n→A, (∀i, h(i,@SS (#n)) = f i) × (∀v, h(T,v) = g v)
  := begin 
     induction n, fconstructor, unfold tpower at g,
     end
-- 2-simplex and 2-horn

definition delta2 : I×I → Prop.{0} 
:= λ ij, prod.rec_on ij $ λ i j, i ≼ j
definition horn2 : I×I → Prop.{0} 
:= λ ij, S == ij.1 ∨ T == ij.2
definition horn2_to_delta2 (ij : I × I) : horn2 ij → delta2 ij
:= prod.rec_on ij $ λ i j d, begin induction d with p p, esimp at p,
                                   induction p, apply SMIN, esimp at p,
                                   induction p, apply TMAX end

definition Δ2       : Set.{0} := trΣ ip, delta2 ip 
definition Λ2       : Set.{0} := trΣ ip, horn2 ip
definition Λ2_to_Δ2 : Λ2 → Δ2 := sigma.total horn2_to_delta2
definition d0       : I → Δ2  := λi, dpair (i, T) !TMAX
definition d1       : I → Δ2  := λi, dpair (i, i) !REFL
definition d2       : I → Δ2  := λi, dpair (S, i) !SMIN
definition d0_h     : I → Λ2  := λi, ⟨(i, T), ∨r rfl⟩
definition d2_h     : I → Λ2  := λi, ⟨(S, i), ∨l rfl⟩
definition Δ2_SS    : Δ2      := ⟨(S,S),SMIN S⟩
definition Δ2_ST    : Δ2      := ⟨(S,T),SMIN T⟩
definition Δ2_TT    : Δ2      := ⟨(T,T),TMAX T⟩
definition Λ2_SS    : Λ2      := ⟨(S,S), ∨l rfl⟩
definition Λ2_TT    : Λ2      := ⟨(T,T), ∨r rfl⟩

definition left_slice_equiv {A B : Type} (a0 : A)
:  B ≃ (Σ ab : A×B, a0 = ab.1)
:= begin fapply equiv.MK, 
   {intro b, apply dpair (a0,b), esimp},
   {λdp, dp.1.2}, 
   {intro dp, induction dp with ab p, induction ab with a b, 
    esimp at p, induction p, apply sigma_eq, apply idpatho},
   {intro b, reflexivity} 
 end

definition right_slice_equiv {A B : Type} (b0 : B)
:  A ≃ (Σ ab : A×B, b0 = ab.2)
:= begin fapply equiv.MK, 
   {intro a, apply dpair (a,b0), esimp},
   {λdp, dp.1.1}, 
   {intro dp, induction dp with ab p, induction ab with a b, 
    esimp at p, induction p, apply sigma_eq, apply idpatho},
   {intro a, reflexivity}, 
 end

definition Λ2_pushout_char : pushout (λx:unit, T) (λx:unit, S) ≃ Λ2 
:= begin 
   refine _ ⬝e !or_pushout, fapply pushout.equiv, 
   { symmetry, apply equiv_unit_of_is_contr, 
     fapply is_contr.mk, fconstructor, exact (S, T),
     fconstructor, esimp, esimp, 
     intro, apply sigma_eq, apply is_prop.elimo,
     induction a, induction a with i j, induction a_1 with p q,
     apply prod_eq, exact p, exact q
   },
   { apply left_slice_equiv},
   { apply right_slice_equiv},
   { reflexivity},
   { reflexivity}
end


structure has_composition [class] (A : Type) 
:= (pce : is_equiv $ precompose A Λ2_to_Δ2)

structure icat [class]
:= (carrier : Type) (hc : has_composition carrier)

attribute [coercion] icat.carrier

definition mor {A : Type} (a b : A) : Type 
:= Σ f : I → A, f S = a × f T = b

definition twocell {A : Type} (a b c : A) 
  (f : mor a b) (g : mor b c) (h : mor a c)
  := Σ d : Δ2 → A,

definition id_mor {A : Type} {a : A} : mor a a 
:= dpair (λi, a) (rfl, rfl)

-- modus ponens
definition mp (A : Type) {B : Type} : A → (A → B) → B := λ a f, f a

definition face0 {C : icat} (h : Δ2 → C) : mor (h Δ2_ST) (h Δ2_TT)
:=  ⟨ h ∘ d0
    , ( h ◅ sigma_eq rfl !is_prop.elimo
      , h ◅ sigma_eq rfl !is_prop.elimo
      )
    ⟩

definition face1 {C : icat} (h : Δ2 → C) : mor (h Δ2_SS) (h Δ2_TT)
:=  ⟨ h ∘ d1
    , ( h ◅ sigma_eq rfl !is_prop.elimo
      , h ◅ sigma_eq rfl !is_prop.elimo
      )
    ⟩

definition face2 {C : icat} (h : Δ2 → C) : mor (h Δ2_SS) (h Δ2_ST)
:=  ⟨ h ∘ d2
    , ( h ◅ sigma_eq rfl !is_prop.elimo
      , h ◅ sigma_eq rfl !is_prop.elimo
      )
    ⟩

-- definition comp_fil {C : icat} {a b c : C} (f : mor a b) (g : mor b c)
-- :   Σ h : Δ2 → C, face2 h = f × face1 h = g
-- :=  begin end


definition comp_mor {C : icat} {a b c : C}
:   mor b c → mor a b → mor a c
:=  begin induction C with C H, induction H, 
    induction pce with comp rinv linv, intros g f,
    apply mp (Σ h : Λ2→C, h Λ2_SS = a × h Λ2_TT = c),
    {   induction f with f cdf, induction cdf with cf df, 
        induction g with g cdg, induction cdg with cg dg, 
        induction df, induction cf, induction dg,
        fconstructor,
        {   refine _ ∘ Λ2_pushout_char⁻¹ᶠ, intro po, 
            induction po with i j gl, exact f i, exact g j, exact cg⁻¹
        },{ exact (rfl, rfl)}
    },{ intro hpq, induction hpq with h pq, induction pq with p q,
        exact ⟨ comp h ∘ d1
              , ( comp h ◅ sigma_eq rfl !is_prop.elimo ⬝ rinv h ▻ Λ2_SS ⬝ p
                , comp h ◅ sigma_eq rfl !is_prop.elimo ⬝ rinv h ▻ Λ2_TT ⬝ q
                )
              ⟩
    }
    end

infix ` • `:59 := comp_mor

definition to_mor [coercion] {C : icat} (f : I → C) : mor (f S) (f T)
:=  ⟨f, (rfl, rfl)⟩ 


definition comp_check {C : icat} (h : Δ2 → C) 
:  face0 h • face2 h = face1 h
:= begin  
   
   end

definition left_unit {C : icat} {a b : C} (f : mor a b) 
:   id_mor • f = f
:=  begin 
    
    end

definition hom {A : Type} (a b : A) : Type 
:= Σ f : I → A, f S = a × f T = b

definition matching_pairs (A : Type) : Type 
:= Σ f g : I → A, f T = g S

definition triangles_to_matching_pairs (A : Type)
: (Δ2 → A) → matching_pairs A 
:= begin intros t, fconstructor, exact t ∘ d2, fconstructor, exact t∘ d0,
apply ap t, fapply sigma_eq, esimp, apply is_prop.elimo end

definition has_composition (A : Type) : Type 
:= is_equiv $ triangles_to_matching_pairs A

structure icat [class] (A : Type) := (hc : has_composition A)

definition compose {A : Type} [H : icat A] {a b c : A}
:  hom b c → hom a b → hom a c
:= begin induction H, intros g f, induction hc with C, 
   induction f with f pq, induction pq with pf qf,
   induction g with g pq, induction pq with pg qg, induction pf, induction qf, induction qg,
  assert mapa : matching_pairs A, apply dpair f, apply dpair g, exact pg⁻¹,
   fconstructor, exact C mapa ∘ d1, split, unfold mapa, end

-- faces 
-- false ~ source, true ~ target

open sum sigma function 

definition cube_map {n m : ℕ} (f : ifin m → ifin n + bool) : I^n → I^m
  := begin
     intro v, apply vector_of_ifin_power, intro i, cases f i, exact v*a,
     cases a, exact s, exact t
     end

definition imp_trans {A C : Type} (B : Type) : (A→B) → (B→C) → (A → C)
  := λf g, g ∘ f

definition is_face (n m : ℕ) (f : ifin m → ifin n + bool) 
:  (∀i:ifin n, Σ j:ifin m, f j = inl i) → is_embedding (cube_map f)
:= begin 
   apply @imp_trans 
   (∀i:ifin n, Σ j:ifin m, f j = inl i) (is_embedding (cube_map f))
   (Σ h : ifin n → ifin m, Π i, f (h i) = inl i),      
   intro H,
   fconstructor, exact λx, pr1 (H x), exact λx, pr2 (H x),intro p,
   induction p with h H, apply is_embedding_of_is_injective,
   intro v w, 
   {
     intro p, apply eq_of_feq !vector_equiv_ifin_power, apply ↑, intro i,
     calc v * i = cube_map f v * h i : begin unfold cube_map, rewrite [proj_is_eval, H] end
          ...   = cube_map f w * h i : (λ x, x * (h i)) ◅ p
          ...   = w * i : begin unfold cube_map, rewrite [proj_is_eval, H] end,
   },
end

theorem l10_pb : Λ 1 ifz ≃ pushout (λx : unit, t) (λx : unit, s)
  := begin
     transitivity (Σv:I^2, v * ifz = s ∨ v * maxi = t), 
     { 
       apply total_equiv, intro v,
       fapply is_trunc.equiv_of_is_prop,
       { intro x, induction x with x y, induction y with y y,          
         exact or.intro_left y, induction y, 
         exact or.intro_right a, induction b, induction a with i p, 
         induction p, cases i, exact empty.elim (a rfl), cases a_2
       },
       { unfold horn, intro, induction a,  fconstructor, 
         intro i, cases i, krewrite a, apply smin,
         cases a_1, apply or.intro_left a, fconstructor,
         intro i, cases i, krewrite b, apply tmax,
         cases a, apply or.intro_right, apply or.intro_left b
       },
       { exact _},
       { exact _}
     }, 
     { 
       refine or_pushout (λv:I^2, v*ifz==s) (λ v, v*maxi==t) ⬝e _, 
       fapply pushout.equiv, 
       fapply equiv.MK (λx, unit.star) 
                       (λ x:unit, dpair [s,t] (rfl, rfl))
                       (λx, !is_prop.elim),
       { intro u, fapply sigma_eq, induction u, 
         induction a_1, apply vector_eq, exact a_1⁻¹,esimp,
         exact @vector_eq _ _ [t] (tail a) (a_2⁻¹) !vector0_eq_nil⁻¹, 
         exact !is_prop.elimo
       },
       fapply equiv.MK, intro u, induction u with v p,  exact v * maxi,
       λ i,  dpair [s,i] rfl, 
       intro i, esimp, intro u, induction u with v p,
       fapply sigma_eq, esimp, apply vector_eq, exact p⁻¹, 
       apply vector_eq, exact rfl,
       exact !vector0_eq_nil⬝!vector0_eq_nil⁻¹, apply is_prop.elimo,

       fapply equiv.MK, intro u, induction u with v p, exact v * ifz,
       intro i, apply dpair [i,t], 
       esimp,
       intro i, esimp, intro u, induction u with v p,
       fapply sigma_eq, apply vector_eq, 
       esimp, apply vector_eq,
       exact p⁻¹, exact !vector0_eq_nil⬝!vector0_eq_nil⁻¹, apply is_prop.elimo,
       intro, induction x, induction a_1, exact a_2, 
       intro, induction x,induction a_1, exact a_1
     }
     end

-- definition flip : I^2 → I^2
-- | [i,j] := [j,i]

definition flup : ifin 2 → ifin 2
:= ifin_power_of_vector [maxi, ifz]

definition eflup : ifin 2 ≃ ifin 2
:= begin
fapply equiv.MK, exact flup, exact flup,
intro i, cases i with i, reflexivity, 
cases a, reflexivity, cases a_1,
intro i, cases i with i, reflexivity, 
cases a, reflexivity, cases a_1,
end



definition hypo : I → Δ 1 := 
begin intro i, fconstructor, exact [i,i], unfold delta, esimp, 
intro j, cases j, apply ref, cases a end

definition set_equiv_diag {A : Set} : A ≃ Σ v : A^2, v*ifz = v*(ifs ifz)
:= begin
fapply equiv.MK, λ a, dpair [a,a] begin reflexivity end, 
λ dp, pr1 dp * ifz, intro dp, induction dp with v p, fapply sigma_eq,
fapply vector_eq, esimp, fapply vector_eq, exact p, 
apply !vector0_eq_nil⁻¹
end

open prod prod.ops

definition square_decompose : I^2 ≃ pushout hypo hypo
:= begin
  transitivity (Σ v:I^2, v*ifz ≼ v*maxi ∨ v*maxi≼v*ifz),
  {   transitivity (Σ v:I^2, unit), 
      exact !sigma_unit_right⁻¹ᵉ,
      apply total_equiv,
      λ v, equiv_of_is_prop (λx, !lin) (λx, unit.star) _ _
  },{ refine !or_pushout ⬝e _, 
      symmetry,
      fapply pushout.equiv, 
      {   transitivity (Σv:I^2, v*ifz=v*maxi),
          apply set_equiv_diag,
          apply total_equiv,
          intro v, apply equiv_of_is_prop,
          intro H, rewrite H, exact (!ref, !ref),
          λ u, asym _ _ u.1 u.2, exact _, exact _
      },{ apply total_equiv, intro v, 
          cases v,  cases a_1, cases a_3, unfold delta,
          apply equiv_of_is_prop, 
          intro p, intro w,cases w, exact p, esimp, cases a, cases v, 
          intro, apply a_2, exact _, exact _
      },{ unfold Δ, unfold delta, 
          fapply sigma_equiv_sigma, apply vector_equiv_of_ifin_equiv,
          apply eflup,
          intro v, apply equiv_of_is_prop, intro h i, cases i, apply h,
          cases a, intro h, apply h ifz, exact _, exact _
      },{ intros, esimp,
          induction x with i pp, induction pp with H1 H2, cases i, 
          clear e_1, cases a_1, cases a_3, rename a i, rename a_2 j,
          esimp at H1, esimp at H2, assert H : i = j, apply asym,
          apply H1, apply H2, induction H, fapply sigma_eq, esimp,
          apply is_prop.elimo
      },{ intros, esimp,
          induction x with i pp, induction pp with H1 H2, cases i, 
          clear e_1, cases a_1, cases a_3, rename a i, rename a_2 j,
          esimp at H1, esimp at H2, assert H : i = j, apply asym,
          apply H1, apply H2, induction H, fapply sigma_eq, esimp,
          apply is_prop.elimo
      }
  }
end


definition foo (x : vector nat 3) : unit :=
match x with [a, b, c] := unit.star end

-- theorem bin_enough (A : Type) 
-- : has_composition 1 ifz A → has_composition 2 ifz A := 
-- begin
-- unfold has_composition,
-- intro e,
-- induction e with f rinv linv coh, 
-- fapply adjointify, intros h v,

-- end
