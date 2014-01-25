module Evaluator where

open import Syntax
open import Data.Nat hiding (_<_)
open import Data.Product
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)

mutual 
  Val : Con → Ty → Set
  Val Γ ι    = Nf Γ ι
  Val Γ (σ ⇒ τ) = Σ (∀{Δ} → Ren Γ Δ → Val Δ σ → Val Δ τ) λ f → ∀{Δ Δ'}(ρ : Ren Γ Δ)(ρ' : Ren Δ Δ')(v : Val Δ σ) → renval ρ' (f ρ v) ≅ f (ρ' ∘ ρ) (renval ρ' v)

  renval : ∀{Γ Δ σ} → Ren Γ Δ → Val Γ σ → Val Δ σ
  renval {Γ} {Δ} {ι} α v = renNf α v
  renval {Γ} {Δ} {σ ⇒ τ} α v = (λ {E} β v' → proj₁ v (renComp β α) v') , 
         (λ {Δ₁ Δ' : Con} (ρ : Ren Δ Δ₁) (ρ' : Ren Δ₁ Δ') (v₁ : Val Δ₁ σ) → 
           proof
           renval ρ' (proj₁ v (ρ ∘ α) v₁)
           ≅⟨ proj₂ v {Δ₁} {Δ'} (renComp ρ α) ρ' v₁ ⟩
           proj₁ v (ρ' ∘ ρ ∘ α) (renval ρ' v₁)
           ∎)
  


Σeq : {A : Set} {A' : Set} {B : A → Set} {B' : A' → Set} → {a : A} → {a' : A'} → a ≅ a' → B ≅ B' → {b : B a} → {b' : B' a'} → b ≅ b' → _,_ {B = B} a b ≅ _,_ {B = B'} a' b'
Σeq refl refl refl = refl

ir : ∀{A A' : Set} → {a : A} → {a' : A'} → {p q : a ≅ a'} → p ≅ q
ir {p = refl} {q = refl} = refl

fixedtypes : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''} → {p : a ≅ a'} → {q : a'' ≅ a'''} → a' ≅ a'' → p ≅ q
fixedtypes {p = refl} {q = refl} refl = refl

fixedtypesleft : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''} → {p : a ≅ a'} → {q : a'' ≅ a'''} → a ≅ a'' → p ≅ q
fixedtypesleft {p = refl} {q = refl} refl = refl

fixedtypesright : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''} → {p : a ≅ a'} → {q : a'' ≅ a'''} → a' ≅ a''' → p ≅ q
fixedtypesright {p = refl} {q = refl} refl = refl


renvalcomp : ∀{Γ Δ E σ} → (ρ : Ren Γ Δ) → (ρ' : Ren Δ E) → (v : Val Γ σ) → renval ρ' (renval ρ v) ≅ renval (ρ' ∘ ρ) v 
renvalcomp {Γ} {Δ} {E} {ι} ρ ρ' v = rennfcomp ρ' ρ v
renvalcomp {Γ} {Δ} {E} {σ ⇒ τ} ρ ρ' (f , p) = Σeq refl refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ₁ → ext λ ρ'' → ext λ v₁ → ir)


Env : Con → Con → Set
Env Γ Δ = ∀{σ} → Var Γ σ → Val Δ σ


_<<_ : ∀{Γ Δ} → Env Γ Δ → ∀{σ} → Val Δ σ → Env (Γ < σ) Δ
(γ << v) zero = v
(γ << v) (suc x) = γ x 

-- notice that I have written it with 3 explicit arguments rather than
-- two, this is because Env computes to:

-- ∀{Γ} → (∀{σ} → Var Γ σ → Val σ) → ∀{σ} → Val σ → ∀{σ'} → 
-- Var (Γ < σ) σ' → Val σ'
 
-- which has three explicit arguments.

-- Notice also that the definition of _<<_ looks a bit like lookup ,
-- this is because the new definition of Env is a lookup function in a
-- way, so to define a new longer environment we need to explain how
-- to lockup variables in it.


renval<< : ∀{Γ Δ E σ} → (ρ : Ren Δ E) → (γ : Env Γ Δ) → (v : Val Δ σ) → ∀{τ}(x : Var (Γ < σ) τ) → (renval ρ ∘ (γ << v)) x ≅ ((renval ρ ∘ γ) << renval ρ v) x
renval<< ρ γ v zero = refl
renval<< ρ γ v (suc x) = refl

ifcong : {A : Set}{B : A → Set}{f f' : {a : A} → B a} → _≅_ {_}{ {a : A} → B a } f {_} { {a : A} → B a } f' → (a : A) → f {a} ≅ f' {a}
ifcong refl a = refl


fcong : ∀{A B : Set} → {f f' : A → B} → f ≅ f' → (a : A) → f a ≅ f' a
fcong refl a = refl

mutual
  reify : ∀{Γ} σ → Val Γ σ → Nf Γ σ
  reify ι v = v
  reify (σ ⇒ τ) v = nlam (reify τ (proj₁ v suc (reflect σ (nvar zero))))
  
  reflect : ∀{Γ} σ → Ne Γ σ → Val Γ σ
  reflect ι n = ne n
  reflect (σ ⇒ τ) n = (λ α v → reflect τ (napp (renNe α n) (reify σ v))) , (λ ρ ρ' v → 
    proof
    renval ρ' (reflect τ (napp (renNe ρ n) (reify σ v)))
    ≅⟨ renvalReflect ρ' (napp (renNe ρ n) (reify σ v)) ⟩
    reflect τ (renNe ρ' (napp (renNe ρ n) (reify σ v)))
    ≅⟨ cong (reflect τ) refl ⟩
    reflect τ (napp (renNe ρ' (renNe ρ n)) (renNf ρ' (reify σ v)))
    ≅⟨ cong (reflect τ) (cong₂ napp (rennecomp ρ' ρ n) (reifyRenval ρ' v)) ⟩
    reflect τ (napp (renNe (ρ' ∘ ρ) n) (reify σ (renval ρ' v)))
    ∎)
  
  renvalReflect : ∀{Γ Δ σ}(ρ : Ren Γ Δ)(n : Ne Γ σ) → renval ρ (reflect σ n) ≅ reflect σ (renNe ρ n)
  renvalReflect {Γ} {Δ} {ι} ρ n = refl
  renvalReflect {Γ} {Δ} {σ ⇒ τ} ρ n = Σeq 
    (iext λ _ → ext λ (α : Ren _ _) → ext λ v → proof
      reflect τ (napp (renNe (α ∘ ρ) n) (reify σ v))
      ≅⟨ cong (reflect τ) (cong₂ napp (sym (rennecomp α ρ n)) refl) ⟩ 
      reflect τ (napp (renNe α (renNe ρ n)) (reify σ v))
      ∎) 
    refl
    ((iext λ _ → iext λ _ → ext λ (ρ₁ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v₁ → fixedtypes (proof
      reflect τ (napp (renNe (ρ' ∘ ρ₁ ∘ ρ) n) (reify σ (renval ρ' v₁)))
      ≅⟨ cong (reflect τ) (cong₂ napp (sym (rennecomp ρ' (ρ₁ ∘ ρ) n)) (sym (reifyRenval ρ' v₁))) ⟩
      reflect τ (napp (renNe ρ' (renNe (ρ₁ ∘ ρ) n)) (renNf ρ' (reify σ v₁)))
      ≅⟨ cong (reflect τ) (cong₂ napp refl refl) ⟩
      reflect τ (renNe ρ' (napp (renNe (ρ₁ ∘ ρ) n) (reify σ v₁)))
      ≅⟨ sym (renvalReflect ρ' (napp (renNe (ρ₁ ∘ ρ) n) (reify σ v₁))) ⟩
      renval ρ' (reflect τ (napp (renNe (ρ₁ ∘ ρ) n) (reify σ v₁)))
      ≅⟨ cong ( λ f → renval ρ' (reflect τ (napp f (reify σ v₁)))) (sym (rennecomp ρ₁ ρ n)) ⟩
      renval ρ' (reflect τ (napp (renNe ρ₁ (renNe ρ n)) (reify σ v₁)))
      ∎)))

  reifyRenval : ∀{Γ Δ σ}(ρ : Ren Γ Δ)(n : Val Γ σ) → renNf ρ (reify σ n) ≅ reify σ (renval ρ n)
  reifyRenval {Γ} {Δ} {ι} ρ n = refl
  reifyRenval {Γ} {Δ} {σ ⇒ τ} ρ n = proof
    nlam (renNf (wk ρ) (reify τ (proj₁ n suc (reflect σ (nvar zero)))))
    ≅⟨ cong nlam (reifyRenval (wk ρ) (proj₁ n suc (reflect σ (nvar zero)))) ⟩
    nlam (reify τ (renval (wk ρ) (proj₁ n suc (reflect σ (nvar zero)))))
    ≅⟨ cong nlam (cong (reify τ) (proj₂ n suc (wk ρ) (reflect σ (nvar zero)))) ⟩
    nlam (reify τ (proj₁ n ((wk ρ) ∘ suc) (renval (wk ρ) (reflect σ (nvar zero)))))
    ≅⟨ cong nlam (cong (reify τ) (cong₂ (proj₁ n) refl (renvalReflect (wk ρ) (nvar zero)))) ⟩
    nlam (reify τ (proj₁ n (suc ∘ ρ) (reflect σ (nvar zero))))
    ∎


mutual
  eval : ∀{Γ Δ σ} → Env Γ Δ → Tm Γ σ → Val Δ σ
  eval γ (var x) = γ x
  eval γ (lam t) = (λ α v → eval ((renval α ∘ γ) << v) t) , (λ ρ ρ' v → 
      proof
      renval ρ' (eval ((renval ρ ∘ γ) << v) t)
      ≅⟨ evallem ((renval ρ ∘ γ) << v) ρ' t ⟩
      eval (renval ρ' ∘ ((renval ρ ∘ γ) << v)) t
      ≅⟨ cong (λ (γ : Env _ _) → eval γ t) (iext (λ τ → ext (renval<< ρ' (renval ρ ∘ γ) v))) ⟩
      eval ((renval ρ' ∘ renval ρ ∘ γ) << renval ρ' v) t
      ≅⟨ cong (λ (x : ∀{σ} → Val _ σ → Val _ σ) → eval ((x ∘ γ) << renval ρ' v) t ) (iext λ σ → ext λ v → renvalcomp ρ ρ' v) ⟩
      eval ((renval (ρ' ∘ ρ) ∘ γ) << renval ρ' v) t
      ∎)
  eval γ (app t u) = proj₁ (eval γ t) renId (eval γ u)     
  
  evallem : ∀{Γ Δ Δ₁ σ} → (γ : Env Γ Δ)(ρ : Ren Δ Δ₁)(t : Tm Γ σ) → renval ρ (eval γ t) ≅ eval (renval ρ ∘ γ) t
  evallem γ ρ (var x) = proof renval ρ (γ x) ≡⟨⟩ renval ρ (γ x) ∎
  evallem γ ρ (lam t) = Σeq 
    (iext λ σ → ext λ (α : Ren _ _) → ext λ v → 
      proof 
      eval ((renval (α ∘ ρ) ∘ γ) << v) t
      ≅⟨ cong (λ (x : ∀{σ} → Val _ σ → Val _ σ) → eval ((x ∘ γ) << v) t ) (iext λ _ → ext λ v → sym (renvalcomp ρ α v)) ⟩ 
      eval ((renval α ∘ renval ρ ∘ γ) << v) t
      ∎)
    refl 
    (iext λ Δ₁ → iext λ Δ' → ext λ (ρ₁ : Ren _ _) → ext λ (ρ'' : Ren _ _) → ext λ v₁ → fixedtypes (
      proof
      eval ((renval (ρ'' ∘ ρ₁ ∘ ρ) ∘ γ) << renval ρ'' v₁) t
      ≅⟨ cong (λ (x : ∀{σ} → Val _ σ → Val _ σ) → eval ((x ∘ γ) << renval ρ'' v₁) t ) (iext λ _ → ext λ v → sym (renvalcomp (ρ₁ ∘ ρ) ρ'' v))  ⟩
      eval ((renval ρ'' ∘ renval (ρ₁ ∘ ρ) ∘ γ) << renval ρ'' v₁) t
      ≅⟨ cong (λ (γ : Env _ _) → eval γ t) (iext (λ _ → ext (λ x → sym (renval<< ρ'' (renval (ρ₁ ∘ ρ) ∘ γ) v₁ x )))) ⟩
      eval (renval ρ'' ∘ ((renval (ρ₁ ∘ ρ) ∘ γ) << v₁)) t
      ≅⟨ sym (evallem ((renval (ρ₁ ∘ ρ) ∘ γ) << v₁) ρ'' t) ⟩
      renval ρ'' (eval ((renval (ρ₁ ∘ ρ) ∘ γ) << v₁) t)
      ≅⟨ cong (λ (x : ∀{σ} → Val _ σ → Val _ σ) → renval ρ'' (eval ((x ∘ γ) << v₁) t )) (iext λ _ → ext λ v → sym (renvalcomp ρ ρ₁ v)) ⟩
      renval ρ'' (eval ((renval ρ₁ ∘ renval ρ ∘ γ) << v₁) t)
      ∎))
  evallem {_}{_}{Δ} γ ρ (app t u) = proof
    renval ρ (proj₁ (eval γ t) id (eval γ u))
    ≅⟨ proj₂ (eval γ t) id ρ (eval γ u)  ⟩
    proj₁ (eval γ t) ρ (renval ρ (eval γ u))
    ≅⟨ cong (proj₁ (eval γ t) ρ) (evallem γ ρ u) ⟩
    proj₁ (eval γ t) ρ (eval (renval ρ ∘ γ) u)
    ≅⟨ cong (λ f → f (eval (renval ρ ∘ γ) u)) (fcong (ifcong (cong proj₁ (evallem γ ρ t)) Δ) id)  ⟩
    proj₁ (eval (renval ρ ∘ γ) t) id (eval (renval ρ ∘ γ) u)
    ∎
 

 
wk<< : ∀{Γ Δ E}(α : Ren Γ Δ)(β : Env Δ E){σ}(v : Val E σ) → ∀{ρ}(y : Var(Γ < σ) ρ) → ((β ∘ α) << v) y ≅ ((β << v) ∘ wk α) y
wk<< α β v zero = proof v ≡⟨⟩ v ∎
wk<< α β v (suc y) = proof β (α y) ≡⟨⟩ β (α y) ∎

reneval : ∀{Γ Δ E σ}(α : Ren Γ Δ)(β : Env Δ E)(t : Tm Γ σ) → eval (β ∘ α) t ≅ (eval β ∘ ren α) t
reneval α β (var x) = proof β (α x) ≡⟨⟩ β (α x) ∎
reneval α β (lam t) = Σeq 
  (iext λ Δ' → ext λ (α₁ : Ren _ _) → ext λ v → 
    proof
    eval ((renval α₁ ∘ β ∘ α) << v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext λ _ → ext (wk<< α (renval α₁ ∘ β) v) ) ⟩
    eval (((renval α₁ ∘ β) << v) ∘ wk α) t
    ≅⟨ reneval (wk α) ((renval α₁ ∘ β) << v) t ⟩
    eval ((renval α₁ ∘ β) << v) (ren (wk α) t)
    ∎) 
  refl 
  (iext λ Δ' → iext λ Δ'' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → fixedtypes (
    proof
    eval ((renval (ρ' ∘ ρ) ∘ β ∘ α) << renval ρ' v) t
    ≅⟨ cong (λ (f : ∀{σ} → Val _ σ → Val _ σ) → eval ((f ∘ β ∘ α) << renval ρ' v) t) (iext (λ _ → ext (λ x → sym (renvalcomp ρ ρ' x)))) ⟩
    eval (((renval ρ' ∘ renval ρ) ∘ β ∘ α) << renval ρ' v) t
    ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext λ _ → ext λ x → sym (renval<< ρ' ((renval ρ ∘ β) ∘ α) v x)) ⟩
    eval (renval ρ' ∘ (((renval ρ ∘ β) ∘ α) << v)) t 
    ≅⟨ sym (evallem (((renval ρ ∘ β) ∘ α) << v) ρ' t) ⟩
    renval ρ' (eval (((renval ρ ∘ β) ∘ α) << v) t)
    ≅⟨ cong (λ (f : Env _ _) → renval ρ' (eval f t)) (iext λ _ → ext λ x → wk<< α (renval ρ ∘ β) v x ) ⟩
    renval ρ' (eval (((renval ρ ∘ β) << v) ∘ wk α) t)
    ≅⟨ cong (renval ρ') (reneval (wk α) ((renval ρ ∘ β) << v) t) ⟩
    renval ρ' (eval ((renval ρ ∘ β) << v) (ren (wk α) t))
    ∎))
reneval {_}{_}{E} α β (app t u) = proof
  ((proj₁ (eval (β ∘ α) t)) renId) (eval (β ∘ α) u)
  ≅⟨ cong ((proj₁ (eval (β ∘ α) t)) renId) (reneval α β u) ⟩
  ((proj₁ (eval (β ∘ α) t)) renId) (eval β (ren α u))
  ≅⟨ cong (λ f → f (eval β (ren α u))) (fcong (ifcong (cong proj₁ (reneval α β t)) E) id) ⟩
  (proj₁ (eval β (ren α t)) renId) (eval β (ren α u))           
  ∎


lifteval : ∀{Γ Δ E σ τ}(α : Sub Γ Δ)(β : Env Δ E)(v : Val E σ)(y : Var (Γ < σ) τ) → ((eval β ∘ α) << v) y ≅ (eval (β << v) ∘ lift α) y
lifteval α β v zero = proof v ≡⟨⟩ v ∎
lifteval α β v (suc y) = 
  proof
  eval β (α y) 
  ≅⟨ reneval suc (β << v) (α y) ⟩
  eval (β << v) (ren suc (α y))
  ∎

subeval : ∀{Γ Δ E σ}(α : Sub Γ Δ)(β : Env Δ E)(t : Tm Γ σ) → eval (eval β ∘ α) t ≅ (eval β ∘ sub α) t
subeval α β (var x) = proof eval β (α x) ≡⟨⟩ eval β (α x) ∎
subeval α β (lam t) = Σeq 
  (iext λ Δ' → ext λ (α₁ : Ren _ _) → ext λ v → 
    proof
    eval ((renval α₁ ∘ eval β ∘ α) << v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval (f << v) t) (iext λ _ → ext λ x → evallem β α₁ (α x)) ⟩
    eval ((eval (renval α₁ ∘ β) ∘ α) << v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext (λ _ → ext λ x → lifteval α (renval α₁ ∘ β) v x )) ⟩
    eval (eval ((renval α₁ ∘ β) << v) ∘ lift α) t
    ≅⟨ subeval (lift α) ((renval α₁ ∘ β) << v) t ⟩
    eval ((renval α₁ ∘ β) << v) (sub (lift α) t)
    ∎
  ) 
  refl 
  (iext λ Δ' → iext λ Δ'' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → fixedtypes (
    proof
    eval ((renval (ρ' ∘ ρ) ∘ eval β ∘ α) << renval ρ' v) t 
    ≅⟨ cong (λ (f : ∀{σ} → Val _ σ → Val _ σ) → eval ((f ∘ eval β ∘ α) << renval ρ' v) t) (iext λ _ → ext λ x → sym (renvalcomp ρ ρ' x)) ⟩
    eval ((renval ρ' ∘ renval ρ ∘ eval β ∘ α) << renval ρ' v) t
    ≅⟨ cong (λ (f : Env _ _ ) → eval f t) (iext λ _ → ext λ x → sym (renval<< ρ' (renval ρ ∘ eval β ∘ α) v x)) ⟩
    eval (renval ρ' ∘ (renval ρ ∘ eval β ∘ α) << v) t
    ≅⟨ cong (λ (f : ∀{σ} → Tm _ σ → Val _ σ) → eval (renval ρ' ∘ ((f ∘ α) << v)) t) (iext λ _ → ext λ t → evallem β ρ t ) ⟩
    eval (renval ρ' ∘ (eval (renval ρ ∘ β) ∘ α) << v) t
    ≅⟨ sym (evallem ((eval (renval ρ ∘ β) ∘ α) << v) ρ' t)  ⟩
    renval ρ' (eval ((eval (renval ρ ∘ β) ∘ α) << v) t) 
    ≅⟨ cong (λ (f : Env _ _) → renval ρ' (eval f t)) (iext λ _ → ext λ x → lifteval α (renval ρ ∘ β) v x ) ⟩
    renval ρ' (eval (eval ((renval ρ ∘ β) << v) ∘ lift α) t) 
    ≅⟨ cong (renval ρ') (subeval (lift α) ((renval ρ  ∘ β) << v) t) ⟩
    renval ρ' (eval ((renval ρ ∘ β) << v) (sub (lift α) t))
    ∎))
subeval {_}{_}{E} α β (app t u) = proof
  (proj₁ (eval (eval β ∘ α) t) renId) (eval (eval β ∘ α) u)
  ≅⟨ cong ((proj₁ (eval (eval β ∘ α) t) renId)) (subeval α β u) ⟩
  (proj₁ (eval (eval β ∘ α) t) renId) (eval β (sub α u))
  ≅⟨ cong (λ f → f (eval β (sub α u))) (fcong (ifcong (cong proj₁ (subeval α β t)) E) id) ⟩
  (proj₁ (eval β (sub α t)) renId) (eval β (sub α u))
  ∎

