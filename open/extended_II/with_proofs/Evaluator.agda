module Evaluator where

open import Syntax
open import ReifyReflect

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Function
open import Data.Product


mutual
  eval : ∀{σ Γ Δ} → Env Γ Δ → Tm Γ σ → Val Δ σ
  eval γ (var x) = γ x
  eval {σ ⇒ τ} γ (lam t) = (λ α v → eval ((λ {σ} → renval {σ} α ∘ γ) << v) t) , (λ ρ ρ' v → 
      proof
      renval {τ} ρ' (eval ((λ {σ} → renval {σ} ρ ∘ γ) << v) t)
      ≅⟨ evallem {τ} ((λ {σ'} → renval {σ'} ρ ∘ γ) << v) ρ' t ⟩
      eval (λ {σ} → renval {σ} ρ' ∘ ((λ {σ'} → renval {σ'} ρ ∘ γ) << v)) t
      ≅⟨ cong (λ (x : Env _ _) → eval x t) (iext (λ τ → ext (renval<< ρ' (λ {σ} → renval {σ} ρ ∘ γ) v))) ⟩
      eval ((λ {σ} → renval {σ} ρ' ∘ renval {σ} ρ ∘ γ) << renval {σ} ρ' v) t
      ≅⟨  cong (λ (x : Env _ _) → eval (x << renval {σ} ρ' v) t) (iext (λ a → ext λ y → renvalcomp {a} ρ ρ' (γ y))) ⟩
      eval ((λ {σ} → renval {σ} (ρ' ∘ ρ) ∘ γ) << renval {σ} ρ' v) t
      ∎)
  eval γ (app t u) = proj₁ (eval γ t) renId (eval γ u)     
  eval γ ze = nzero
  eval γ (sc t) = nsuc (eval γ t)
  eval {σ} γ (rec z f n) = nfold {σ} (eval γ z) (eval γ f) (eval γ n)
  eval {σ ∧ τ} γ (a ,, b) = eval {σ} γ a , eval {τ} γ b
  eval γ (fst a) = proj₁ (eval γ a)
  eval γ (snd a) = proj₂ (eval γ a)
  
  evallem : ∀{σ Γ Δ Δ₁} → (γ : Env Γ Δ)(ρ : Ren Δ Δ₁)(t : Tm Γ σ) → renval {σ} ρ (eval γ t) ≅ eval (λ {σ'} → renval {σ'} ρ ∘ γ) t
  evallem {σ} γ ρ (var x) = proof renval {σ} ρ (γ x) ≡⟨⟩ renval {σ} ρ (γ x) ∎
  evallem {σ ⇒ τ}{Γ}{Δ}{Δ₁} γ ρ (lam t) = Σeq 
    (iext λ σ → ext λ (α : Ren _ _) → ext λ v → 
      proof 
      eval ((λ {σ'} → renval {σ'} (α ∘ ρ) ∘ γ) << v) t
      ≅⟨ cong (λ (f : Env _ _) → eval (f << v) t) (iext λ σ₁ → ext λ x → sym (renvalcomp {σ₁} ρ α (γ x)) ) ⟩ 
      eval ((λ {σ'} → renval {σ'} α ∘ renval {σ'} ρ ∘ γ) << v) t
      ∎)
    refl 
    (iext λ Δ₁ → iext λ Δ' → ext λ (ρ₁ : Ren _ _) → ext λ (ρ'' : Ren _ _) → ext λ v₁ → fixedtypes (
      proof
      eval ((λ {σ'} → renval {σ'} (ρ'' ∘ ρ₁ ∘ ρ) ∘ γ) << renval {σ} ρ'' v₁) t
      ≅⟨ cong (λ (x : Env _ _) → eval (x << (renval {σ} ρ'' v₁)) t) (iext λ σ' → ext λ y → sym (renvalcomp {σ'} (ρ₁ ∘ ρ) ρ'' (γ y))) ⟩
      eval ((λ {σ'} → renval {σ'} ρ'' ∘ renval {σ'} (ρ₁ ∘ ρ) ∘ γ) << renval {σ} ρ'' v₁) t
      ≅⟨ cong (λ (γ : Env _ _) → eval γ t) (iext (λ _ → ext (λ x → sym (renval<< ρ'' (λ {σ'} → renval {σ'} (ρ₁ ∘ ρ) ∘ γ) v₁ x )))) ⟩
      eval (λ {σ'} → renval {σ'} ρ'' ∘ ((λ {σ''} → renval {σ''} (ρ₁ ∘ ρ) ∘ γ) << v₁)) t
      ≅⟨ sym (evallem ((λ {σ'} → renval {σ'} (ρ₁ ∘ ρ) ∘ γ) << v₁) ρ'' t) ⟩
      renval {τ} ρ'' (eval ((λ {σ'} → renval {σ'} (ρ₁ ∘ ρ) ∘ γ) << v₁) t)
      ≅⟨ cong (λ (x : Env _ _) → renval {τ} ρ'' (eval (x << v₁) t)) (iext λ σ' → ext λ y → sym (renvalcomp {σ'} ρ ρ₁ (γ y))) ⟩ 
      renval {τ} ρ'' (eval ((λ {σ'} → renval {σ'} ρ₁ ∘ renval {σ'} ρ ∘ γ) << v₁) t)
      ∎))
  evallem {σ}{Γ}{Δ}{Δ₁} γ ρ (app {σ'} t u) = proof
    renval {σ} ρ (proj₁ (eval γ t) id (eval γ u))
    ≅⟨ proj₂ (eval γ t) id ρ (eval γ u)  ⟩
    proj₁ (eval γ t) ρ (renval {σ'} ρ (eval γ u))
    ≅⟨ cong (proj₁ (eval γ t) ρ) (evallem γ ρ u) ⟩ 
    proj₁ (eval γ t) ρ (eval (λ {σ'} → renval {σ'} ρ ∘ γ) u)
    ≅⟨ cong (λ f → f (eval (λ {σ'} → renval {σ'} ρ ∘ γ) u)) (fcong (ifcong (cong proj₁ (evallem γ ρ t)) Δ₁) id) ⟩ 
    proj₁ (eval (λ {σ'} → renval {σ'} ρ ∘ γ) t) id (eval (λ {σ'} → renval {σ'} ρ ∘ γ) u)
    ∎
  evallem γ ρ ze = proof nzero ≡⟨⟩ nzero ∎
  evallem γ ρ (sc n) = proof
    nsuc (renNf ρ (eval γ n)) 
    ≅⟨ cong nsuc (evallem γ ρ n) ⟩
    nsuc (eval (λ {σ} → renval {σ} ρ ∘ γ) n)
    ∎
  evallem {σ} γ ρ (rec z f n) = proof
    renval {σ} ρ (nfold {σ} (eval γ z) (eval γ f) (eval γ n)) 
    ≅⟨ renvalnfold {σ} ρ (eval γ z) (eval γ f) (eval γ n) ⟩
    nfold {σ} (renval {σ} ρ (eval γ z)) (renval {σ ⇒ σ} ρ (eval γ f)) (renval {nat} ρ (eval γ n))
    ≅⟨ cong₃ (nfold {σ}) (evallem γ ρ z) (evallem γ ρ f) (evallem γ ρ n) ⟩
    nfold {σ} (eval (λ {σ'} → renval {σ'} ρ ∘ γ) z) (eval (λ {σ'} → renval {σ'} ρ ∘ γ) f) (eval (λ {σ'} → renval {σ'} ρ ∘ γ) n)
    ∎
  evallem {σ ∧ τ} γ ρ (a ,, b) = proof
    (renval {σ} ρ (eval γ a) , renval {τ} ρ (eval γ b)) 
    ≅⟨ cong₂ _,_ (evallem {σ} γ ρ a) (evallem {τ} γ ρ b) ⟩
    (eval (λ {σ'} → renval {σ'} ρ ∘ γ) a , eval (λ {σ'} → renval {σ'} ρ ∘ γ) b)
    ∎
  evallem {σ} γ ρ (fst a) = proof
    renval {σ} ρ (proj₁ (eval γ a)) 
    ≅⟨ cong proj₁ (evallem γ ρ a) ⟩
    proj₁ (eval (λ {σ'} → renval {σ'} ρ ∘ γ) a)
    ∎
  evallem {σ} γ ρ (snd a) = proof
    renval {σ} ρ (proj₂ (eval γ a)) 
    ≅⟨ cong proj₂ (evallem γ ρ a) ⟩
    proj₂ (eval (λ {σ'} → renval {σ'} ρ ∘ γ) a)
    ∎



idE : ∀{Γ} → Env Γ Γ
idE {ε} ()
idE {Γ < σ} zero = reflect σ (nvar zero)
idE {Γ < σ} (suc {σ = σ'} x) = renval {σ'} suc (idE x)

norm : ∀{Γ σ} → Tm Γ σ → Nf Γ σ
norm t = reify _ (eval idE t)



wk<< : ∀{Γ Δ E}(α : Ren Γ Δ)(β : Env Δ E){σ}(v : Val E σ) → ∀{ρ}(y : Var(Γ < σ) ρ) → ((β ∘ α) << v) y ≅ ((β << v) ∘ wk α) y
wk<< α β v zero = proof v ≡⟨⟩ v ∎
wk<< α β v (suc y) = proof β (α y) ≡⟨⟩ β (α y) ∎


reneval : ∀{σ Γ Δ E}(α : Ren Γ Δ)(β : Env Δ E)(t : Tm Γ σ) → eval (β ∘ α) t ≅ (eval β ∘ ren α) t
reneval α β (var x) = proof β (α x) ≡⟨⟩ β (α x) ∎
reneval {σ ⇒ τ} α β (lam t) = Σeq 
  (iext λ Δ' → ext λ (α₁ : Ren _ _) → ext λ v → 
    proof
    eval ((λ {σ'} → renval {σ'}  α₁ ∘ β ∘ α) << v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext λ _ → ext (wk<< α (λ {σ'} → renval {σ'} α₁ ∘ β) v) ) ⟩
    eval (((λ {σ'} → renval {σ'} α₁ ∘ β) << v) ∘ wk α) t
    ≅⟨ reneval (wk α) ((λ {σ'} → renval {σ'} α₁ ∘ β) << v) t ⟩
    eval ((λ {σ'} → renval {σ'} α₁ ∘ β) << v) (ren (wk α) t)
    ∎) 
  refl 
  (iext λ Δ' → iext λ Δ'' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → fixedtypes (
    proof
    eval ((λ {σ'} → renval {σ'} (ρ' ∘ ρ) ∘ β ∘ α) << renval {σ} ρ' v) t
    ≅⟨ cong (λ (f : Env _ _) → eval (f << renval {σ} ρ' v) t) (iext λ σ₁ → ext λ x → sym (renvalcomp {σ₁} ρ ρ' (β (α x)))) ⟩
    eval ((λ {σ'} → (renval {σ'} ρ' ∘ renval {σ'} ρ) ∘ β ∘ α) << renval {σ} ρ' v) t
    ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext λ _ → ext λ x → sym (renval<< ρ' (λ {σ'} → (renval {σ'} ρ ∘ β) ∘ α) v x)) ⟩
    eval (λ {σ₁} → renval {σ₁} ρ' ∘ ((λ {σ'} → (renval {σ'} ρ ∘ β) ∘ α) << v)) t 
    ≅⟨ sym (evallem ((λ {σ'} → (renval {σ'} ρ ∘ β) ∘ α) << v) ρ' t) ⟩
    renval {τ} ρ' (eval ((λ {σ'} → (renval {σ'} ρ ∘ β) ∘ α) << v) t)
    ≅⟨ cong (λ (f : Env _ _) → renval {τ} ρ' (eval f t)) (iext λ _ → ext λ x → wk<< α (λ {σ'} → renval {σ'} ρ ∘ β) v x ) ⟩
    renval {τ} ρ' (eval (((λ {σ'} → renval {σ'} ρ ∘ β) << v) ∘ wk α) t)
    ≅⟨ cong (renval {τ} ρ') (reneval (wk α) ((λ {σ'} → renval {σ'} ρ ∘ β) << v) t) ⟩
    renval {τ} ρ' (eval ((λ {σ'} → renval {σ'} ρ ∘ β) << v) (ren (wk α) t))
    ∎))
reneval {E = E} α β (app t u) = proof
  ((proj₁ (eval (β ∘ α) t)) renId) (eval (β ∘ α) u)
  ≅⟨ cong ((proj₁ (eval (β ∘ α) t)) renId) (reneval α β u) ⟩
  ((proj₁ (eval (β ∘ α) t)) renId) (eval β (ren α u))
  ≅⟨ cong (λ f → f (eval β (ren α u))) (fcong (ifcong (cong proj₁ (reneval α β t)) E) id) ⟩
  (proj₁ (eval β (ren α t)) renId) (eval β (ren α u))           
  ∎
reneval α β ze = proof nzero ≡⟨⟩ nzero ∎
reneval α β (sc n) = proof
  nsuc (eval (β ∘ α) n) 
  ≅⟨ cong nsuc (reneval α β n) ⟩
  nsuc (eval β (ren α n))
  ∎ 
reneval {σ} α β (rec z f n) = proof
   nfold {σ} (eval (β ∘ α) z) (eval (β ∘ α) f) (eval (β ∘ α) n) 
   ≅⟨ cong₃ (nfold {σ}) (reneval α β z) (reneval α β f) (reneval α β n) ⟩
   nfold {σ} (eval β (ren α z)) (eval β (ren α f)) (eval β (ren α n))
   ∎
reneval α β (a ,, b) = Σeq (reneval α β a) refl (reneval α β b)
reneval α β (fst a) = cong proj₁ (reneval α β a)
reneval α β (snd a) = cong proj₂ (reneval α β a)



lifteval : ∀{Γ Δ E σ τ}(α : Sub Γ Δ)(β : Env Δ E)(v : Val E σ)(y : Var (Γ < σ) τ) → ((eval β ∘ α) << v) y ≅ (eval (β << v) ∘ lift α) y
lifteval α β v zero = proof v ≡⟨⟩ v ∎
lifteval α β v (suc y) = 
  proof
  eval β (α y) 
  ≅⟨ reneval suc (β << v) (α y) ⟩
  eval (β << v) (ren suc (α y))
  ∎


subeval : ∀{σ Γ Δ E}(α : Sub Γ Δ)(β : Env Δ E)(t : Tm Γ σ) → eval (eval β ∘ α) t ≅ (eval β ∘ sub α) t
subeval α β (var x) = proof eval β (α x) ≡⟨⟩ eval β (α x) ∎
subeval {σ ⇒ τ} α β (lam t) = Σeq 
  (iext λ Δ' → ext λ (α₁ : Ren _ _) → ext λ v → 
    proof
    eval ((λ {σ'} → renval {σ'} α₁ ∘ eval β ∘ α) << v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval (f << v) t) (iext λ _ → ext λ x → evallem β α₁ (α x)) ⟩
    eval ((eval (λ {σ'} → renval {σ'} α₁ ∘ β) ∘ α) << v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext (λ _ → ext λ x → lifteval α (λ {σ'} → renval {σ'} α₁ ∘ β) v x )) ⟩
    eval (eval ((λ {σ'} → renval {σ'} α₁ ∘ β) << v) ∘ lift α) t
    ≅⟨ subeval (lift α) ((λ {σ'} → renval {σ'} α₁ ∘ β) << v) t ⟩
    eval ((λ {σ'} → renval {σ'} α₁ ∘ β) << v) (sub (lift α) t)
    ∎
  ) 
  refl 
  (iext λ Δ' → iext λ Δ'' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → fixedtypes (
    proof
    eval ((λ {σ'} → renval {σ'} (ρ' ∘ ρ) ∘ eval β ∘ α) << renval {σ} ρ' v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval (f << renval {σ} ρ' v) t) (iext λ σ₁ → ext λ x → sym (renvalcomp {σ₁} ρ ρ' (eval β (α x)))) ⟩ 
    eval ((λ {σ'} → renval {σ'} ρ' ∘ renval {σ'} ρ ∘ eval β ∘ α) << renval {σ} ρ' v) t
    ≅⟨ cong (λ (f : Env _ _ ) → eval f t) (iext λ _ → ext λ x → sym (renval<< ρ' (λ {σ'} → renval {σ'} ρ ∘ eval β ∘ α) v x)) ⟩
    eval (λ {σ'} → renval {σ'} ρ' ∘ (λ {σ''} → renval {σ''} ρ ∘ eval β ∘ α) << v) t
    ≅⟨ cong (λ (f : ∀{σ} → Tm _ σ → Val _ σ) → eval (λ {σ'} → renval {σ'} ρ' ∘ ((f ∘ α) << v)) t) (iext λ v₁ → ext λ u → evallem β ρ u) ⟩
    eval (λ {σ'} → renval {σ'} ρ' ∘ (eval (λ {σ''} → renval {σ''} ρ ∘ β) ∘ α) << v) t
    ≅⟨ sym (evallem ((eval (λ {σ'} → renval {σ'} ρ ∘ β) ∘ α) << v) ρ' t)  ⟩
    renval {τ} ρ' (eval ((eval (λ {σ'} → renval {σ'} ρ ∘ β) ∘ α) << v) t) 
    ≅⟨ cong (λ (f : Env _ _) → renval {τ} ρ' (eval f t)) (iext λ σ₁ → ext λ x → lifteval α (λ {σ'} → renval {σ'} ρ ∘ β) v x) ⟩ 
    renval {τ} ρ' (eval (eval ((λ {σ'} → renval {σ'} ρ ∘ β) << v) ∘ lift α) t) 
    ≅⟨ cong (renval {τ} ρ') (subeval (lift α) ((λ {σ'} → renval {σ'} ρ ∘ β) << v) t) ⟩
    renval {τ} ρ' (eval ((λ {σ'} → renval {σ'} ρ ∘ β) << v) (sub (lift α) t))
    ∎))
subeval {E = E} α β (app t u) = proof
  (proj₁ (eval (eval β ∘ α) t) renId) (eval (eval β ∘ α) u)
  ≅⟨ cong ((proj₁ (eval (eval β ∘ α) t) renId)) (subeval α β u) ⟩
  (proj₁ (eval (eval β ∘ α) t) renId) (eval β (sub α u))
  ≅⟨ cong (λ f → f (eval β (sub α u))) (fcong (ifcong (cong proj₁ (subeval α β t)) E) id) ⟩
  (proj₁ (eval β (sub α t)) renId) (eval β (sub α u))
  ∎
subeval α β ze = proof nzero ≡⟨⟩ nzero ∎
subeval α β (sc n) = proof 
  nsuc (eval (eval β ∘ α) n) 
  ≅⟨ cong nsuc (subeval α β n) ⟩
  nsuc (eval β (sub α n))
  ∎
subeval {σ} α β (rec z f n) = proof
  nfold {σ} (eval (eval β ∘ α) z) (eval (eval β ∘ α) f) (eval (eval β ∘ α) n)
  ≅⟨ cong₃ (nfold {σ}) (subeval α β z) (subeval α β f) (subeval α β n) ⟩
  nfold {σ} (eval β (sub α z)) (eval β (sub α f)) (eval β (sub α n))
  ∎
subeval α β (a ,, b) = Σeq (subeval α β a) refl (subeval α β b)
subeval α β (fst a) = cong proj₁ (subeval α β a)
subeval α β (snd a) = cong proj₂ (subeval α β a)

