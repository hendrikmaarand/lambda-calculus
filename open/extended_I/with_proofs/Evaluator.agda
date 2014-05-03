module Evaluator where

open import Syntax
open import ReifyReflect

open import Data.Product
open import Data.Sum hiding (map)
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)


mutual
  eval : ∀{Γ Δ σ} → Env Γ Δ → Tm Γ σ → Val Δ σ
  eval γ (var x) = γ x
  eval {σ = σ ⇒ τ} γ (lam t) = (λ α v → eval ((λ {σ} → renval {σ = σ} α ∘ γ) << v) t) , (λ ρ ρ' v → 
      proof
      renval {σ = τ} ρ' (eval ((λ {σ} → renval {σ = σ} ρ ∘ γ) << v) t)
      ≅⟨ evallem {σ = τ} ((λ {σ'} → renval {σ = σ'} ρ ∘ γ) << v) ρ' t ⟩
      eval (λ {σ} → renval {σ = σ} ρ' ∘ ((λ {σ'} → renval {σ = σ'} ρ ∘ γ) << v)) t
      ≅⟨ cong (λ (x : Env _ _) → eval x t) (iext (λ τ → ext (renval<< ρ' (λ {σ} → renval {σ = σ} ρ ∘ γ) v))) ⟩
      eval ((λ {σ} → renval {σ = σ} ρ' ∘ renval {σ = σ} ρ ∘ γ) << renval {σ = σ} ρ' v) t
      ≅⟨  cong (λ (x : Env _ _) → eval (x << renval {σ = σ} ρ' v) t) (iext (λ a → ext λ y → renvalcomp {σ = a} ρ' ρ (γ y))) ⟩
      eval ((λ {σ} → renval {σ = σ} (ρ' ∘ ρ) ∘ γ) << renval {σ = σ} ρ' v) t
      ∎)
  eval γ (app t u) = proj₁ (eval γ t) renId (eval γ u)     
  eval γ ze = nze
  eval γ (su t) = nsu (eval γ t)
  eval {σ = σ} γ (rec z f n) = natfold {σ = σ} (eval γ z) (eval γ f) (eval γ n)
  eval γ nil = nilLV
  eval γ (cons h t) = consLV (eval γ h) (eval γ t)
  eval γ (fold {σ}{τ} z f n) = listfold {σ = σ}{τ = τ} (eval γ z) (eval γ f) (eval γ n)
   
  evallem : ∀{Γ Δ Δ₁ σ} → (γ : Env Γ Δ)(α : Ren Δ Δ₁)(t : Tm Γ σ) → renval {σ = σ} α (eval γ t) ≅ eval (λ {σ'} → renval {σ = σ'} α ∘ γ) t
  evallem {σ = σ} γ ρ (var x) = proof renval {σ = σ} ρ (γ x) ≡⟨⟩ renval {σ = σ} ρ (γ x) ∎
  evallem {σ = σ ⇒ τ} γ ρ (lam t) = Σeq 
    (iext λ σ → ext λ (α : Ren _ _) → ext λ v → 
      proof 
      eval ((λ {σ'} → renval {σ = σ'} (α ∘ ρ) ∘ γ) << v) t
      ≅⟨ cong (λ (f : Env _ _) → eval (f << v) t) (iext λ σ₁ → ext λ x → sym (renvalcomp {σ = σ₁} α ρ (γ x)) ) ⟩ 
      eval ((λ {σ'} → renval {σ = σ'} α ∘ renval {σ = σ'} ρ ∘ γ) << v) t
      ∎)
    refl 
    (iext λ Δ₁ → iext λ Δ' → ext λ (ρ₁ : Ren _ _) → ext λ (ρ'' : Ren _ _) → ext λ v₁ → fixedtypes (
      proof
      eval ((λ {σ'} → renval {σ = σ'} (ρ'' ∘ ρ₁ ∘ ρ) ∘ γ) << renval {σ = σ} ρ'' v₁) t
      ≅⟨ cong (λ (x : Env _ _) → eval (x << (renval {σ = σ} ρ'' v₁)) t) (iext λ σ' → ext λ y → sym (renvalcomp {σ = σ'} ρ'' (ρ₁ ∘ ρ) (γ y))) ⟩
      eval ((λ {σ'} → renval {σ = σ'} ρ'' ∘ renval {σ = σ'} (ρ₁ ∘ ρ) ∘ γ) << renval {σ = σ} ρ'' v₁) t
      ≅⟨ cong (λ (γ : Env _ _) → eval γ t) (iext (λ _ → ext (λ x → sym (renval<< ρ'' (λ {σ'} → renval {σ = σ'} (ρ₁ ∘ ρ) ∘ γ) v₁ x )))) ⟩
      eval (λ {σ'} → renval {σ = σ'} ρ'' ∘ ((λ {σ''} → renval {σ = σ''} (ρ₁ ∘ ρ) ∘ γ) << v₁)) t
      ≅⟨ sym (evallem ((λ {σ'} → renval {σ = σ'} (ρ₁ ∘ ρ) ∘ γ) << v₁) ρ'' t) ⟩
      renval {σ = τ} ρ'' (eval ((λ {σ'} → renval {σ = σ'} (ρ₁ ∘ ρ) ∘ γ) << v₁) t)
      ≅⟨ cong (λ (x : Env _ _) → renval {σ = τ} ρ'' (eval (x << v₁) t)) (iext λ σ' → ext λ y → sym (renvalcomp {σ = σ'} ρ₁ ρ (γ y))) ⟩ 
      renval {σ = τ} ρ'' (eval ((λ {σ'} → renval {σ = σ'} ρ₁ ∘ renval {σ = σ'} ρ ∘ γ) << v₁) t)
      ∎ ))
  evallem {Δ₁ = Δ₁}{σ = σ} γ ρ (app {σ'} t u) = proof
    renval {σ = σ} ρ (proj₁ (eval γ t) id (eval γ u))
    ≅⟨ proj₂ (eval γ t) id ρ (eval γ u)  ⟩
    proj₁ (eval γ t) ρ (renval {σ = σ'} ρ (eval γ u))
    ≅⟨ cong (proj₁ (eval γ t) ρ) (evallem γ ρ u) ⟩ 
    proj₁ (eval γ t) ρ (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) u)
    ≅⟨ cong (λ f → f (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) u)) (fcong (ifcong (cong proj₁ (evallem γ ρ t)) Δ₁) id) ⟩ 
    proj₁ (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) t) id (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) u)
    ∎
  evallem γ ρ ze = proof nze ≡⟨⟩ nze ∎
  evallem γ ρ (su n) = proof
    nsu (renNf ρ (eval γ n)) 
    ≅⟨ cong nsu (evallem γ ρ n) ⟩
    nsu (eval (λ {σ} → renval {σ = σ} ρ ∘ γ) n)
    ∎
  evallem {σ = σ} γ ρ (rec z f n) = proof
    renval {σ = σ} ρ (natfold {σ = σ} (eval γ z) (eval γ f) (eval γ n)) 
    ≅⟨ renvalnatfold {σ = σ} ρ (eval γ z) (eval γ f) (eval γ n) ⟩
    natfold {σ = σ} (renval {σ = σ} ρ (eval γ z)) (renval {σ = σ ⇒ σ} ρ (eval γ f)) (renval {σ = nat} ρ (eval γ n))
    ≅⟨ cong₃ (natfold {σ = σ}) (evallem γ ρ z) (evallem γ ρ f) (evallem γ ρ n) ⟩
    natfold {σ = σ} (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) z) (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) f) (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) n)
    ∎
  evallem γ α nil = refl
  evallem {σ = [ σ ]} γ α (cons t t₁) = cong₂ consLV (evallem γ α t) (evallem γ α t₁)
  evallem {σ = τ} γ α (fold {σ = σ}{τ = ._} z f n) = proof
    renval {σ = τ} α (listfold {τ = τ} (eval γ z) (eval γ f) (eval γ n)) 
    ≅⟨ renvallistfold α (eval γ z) (eval γ f) (eval γ n) ⟩
    listfold {τ = τ} (renval {σ = τ} α (eval γ z)) (renval {σ = σ ⇒ τ ⇒ τ} α (eval γ f)) (renval {σ = [ σ ]} α (eval γ n))
    ≅⟨ cong₃ listfold (evallem γ α z) (evallem γ α f) (evallem γ α n) ⟩
    listfold (eval (λ {σ'} → (renval {σ = σ'} α) ∘ γ) z) (eval (λ {σ'} → (renval {σ = σ'} α) ∘ γ) f) (eval (λ {σ'} → (renval {σ = σ'} α) ∘ γ) n)
    ∎



wk<< : ∀{Γ Δ E}(α : Ren Γ Δ)(β : Env Δ E){σ}(v : Val E σ) → ∀{ρ}(y : Var(Γ < σ) ρ) → ((β ∘ α) << v) y ≅ ((β << v) ∘ wk α) y
wk<< α β v vze = proof v ≡⟨⟩ v ∎
wk<< α β v (vsu y) = proof β (α y) ≡⟨⟩ β (α y) ∎

reneval : ∀{Γ Δ E σ}(α : Ren Γ Δ)(β : Env Δ E)(t : Tm Γ σ) → eval (β ∘ α) t ≅ (eval β ∘ ren α) t
reneval α β (var x) = proof β (α x) ≡⟨⟩ β (α x) ∎
reneval {σ = σ ⇒ τ} α β (lam t) = Σeq 
  (iext (λ Δ' → ext (λ (α₁ : Ren _ _) → ext λ v → 
    proof
    eval ((λ {σ'} → renval {σ = σ'}  α₁ ∘ β ∘ α) << v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext λ _ → ext (wk<< α (λ {σ'} → renval {σ = σ'} α₁ ∘ β) v) ) ⟩
    eval (((λ {σ'} → renval {σ = σ'} α₁ ∘ β) << v) ∘ wk α) t
    ≅⟨ reneval (wk α) ((λ {σ'} → renval {σ = σ'} α₁ ∘ β) << v) t ⟩
    eval ((λ {σ'} → renval {σ = σ'} α₁ ∘ β) << v) (ren (wk α) t)
    ∎ ))) 
  refl 
  (iext λ Δ' → iext λ Δ'' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → fixedtypes (
    proof
    eval ((λ {σ'} → renval {σ = σ'} (ρ' ∘ ρ) ∘ β ∘ α) << renval {σ = σ} ρ' v) t
    ≅⟨ cong (λ (f : Env _ _) → eval (f << renval {σ = σ} ρ' v) t) (iext (λ σ₁ → ext (λ x → sym (renvalcomp {σ = σ₁} ρ' ρ (β (α x))) ))) ⟩
    eval ((λ {σ'} → (renval {σ = σ'} ρ' ∘ renval {σ = σ'} ρ) ∘ β ∘ α) << renval {σ = σ} ρ' v) t
    ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext λ _ → ext λ x → sym (renval<< ρ' (λ {σ'} → (renval {σ = σ'} ρ ∘ β) ∘ α) v x)) ⟩
    eval (λ {σ₁} → renval {σ = σ₁} ρ' ∘ ((λ {σ'} → (renval {σ = σ'} ρ ∘ β) ∘ α) << v)) t 
    ≅⟨ sym (evallem ((λ {σ'} → (renval {σ = σ'} ρ ∘ β) ∘ α) << v) ρ' t) ⟩
    renval {σ = τ} ρ' (eval ((λ {σ'} → (renval {σ = σ'} ρ ∘ β) ∘ α) << v) t)
    ≅⟨ cong (λ (f : Env _ _) → renval {σ = τ} ρ' (eval f t)) (iext λ _ → ext λ x → wk<< α (λ {σ'} → renval {σ = σ'} ρ ∘ β) v x ) ⟩
    renval {σ = τ} ρ' (eval (((λ {σ'} → renval {σ = σ'} ρ ∘ β) << v) ∘ wk α) t)
    ≅⟨ cong (renval {σ = τ} ρ') (reneval (wk α) ((λ {σ'} → renval {σ = σ'} ρ ∘ β) << v) t) ⟩
    renval {σ = τ} ρ' (eval ((λ {σ'} → renval {σ = σ'} ρ ∘ β) << v) (ren (wk α) t))
    ∎))
reneval {E = E} α β (app t u) = proof
  ((proj₁ (eval (β ∘ α) t)) renId) (eval (β ∘ α) u)
  ≅⟨ cong ((proj₁ (eval (β ∘ α) t)) renId) (reneval α β u) ⟩
  ((proj₁ (eval (β ∘ α) t)) renId) (eval β (ren α u))
  ≅⟨ cong (λ f → f (eval β (ren α u))) (fcong (ifcong (cong proj₁ (reneval α β t)) E) id) ⟩
  (proj₁ (eval β (ren α t)) renId) (eval β (ren α u))           
  ∎
reneval α β ze = proof nze ≡⟨⟩ nze ∎
reneval α β (su n) = proof
  nsu (eval (β ∘ α) n) 
  ≅⟨ cong nsu (reneval α β n) ⟩
  nsu (eval β (ren α n))
  ∎ 
reneval {σ = σ} α β (rec z f n) = cong₃ natfold (reneval α β z) (reneval α β f) (reneval α β n)
reneval α β nil = refl
reneval α β (cons h t) = cong₂ consLV (reneval α β h) (reneval α β t)
reneval α β (fold z f l) = cong₃ listfold (reneval α β z) (reneval α β f) (reneval α β l)



lifteval : ∀{Γ Δ E σ τ}(α : Sub Γ Δ)(β : Env Δ E)(v : Val E σ)(y : Var (Γ < σ) τ) → ((eval β ∘ α) << v) y ≅ (eval (β << v) ∘ lift α) y
lifteval α β v vze = proof v ≡⟨⟩ v ∎
lifteval α β v (vsu y) = 
  proof
  eval β (α y) 
  ≅⟨ reneval vsu (β << v) (α y) ⟩
  eval (β << v) (ren vsu (α y))
  ∎

subeval : ∀{Γ Δ E σ}(α : Sub Γ Δ)(β : Env Δ E)(t : Tm Γ σ) → eval (eval β ∘ α) t ≅ (eval β ∘ sub α) t
subeval α β (var x) = proof eval β (α x) ≡⟨⟩ eval β (α x) ∎
subeval {σ = σ ⇒ τ} α β (lam t) = Σeq 
  (iext λ Δ' → ext λ (α₁ : Ren _ _) → ext λ v → 
    proof
    eval ((λ {σ'} → renval {σ = σ'} α₁ ∘ eval β ∘ α) << v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval (f << v) t) (iext λ _ → ext λ x → evallem β α₁ (α x)) ⟩
    eval ((eval (λ {σ'} → renval {σ = σ'} α₁ ∘ β) ∘ α) << v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext (λ _ → ext λ x → lifteval α (λ {σ'} → renval {σ = σ'} α₁ ∘ β) v x )) ⟩
    eval (eval ((λ {σ'} → renval {σ = σ'} α₁ ∘ β) << v) ∘ lift α) t
    ≅⟨ subeval (lift α) ((λ {σ'} → renval {σ = σ'} α₁ ∘ β) << v) t ⟩
    eval ((λ {σ'} → renval {σ = σ'} α₁ ∘ β) << v) (sub (lift α) t)
    ∎
  ) 
  refl 
  (iext λ Δ' → iext λ Δ'' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → fixedtypes (
    proof
    eval ((λ {σ'} → renval {σ = σ'} (ρ' ∘ ρ) ∘ eval β ∘ α) << renval {σ = σ} ρ' v) t 
    ≅⟨ cong (λ (f : Env _ _) → eval (f << renval {σ = σ} ρ' v) t) (iext λ σ₁ → ext λ x → sym (renvalcomp {σ = σ₁} ρ' ρ (eval β (α x)))) ⟩ 
    eval ((λ {σ'} → renval {σ = σ'} ρ' ∘ renval {σ = σ'} ρ ∘ eval β ∘ α) << renval {σ = σ} ρ' v) t
    ≅⟨ cong (λ (f : Env _ _ ) → eval f t) (iext λ _ → ext λ x → sym (renval<< ρ' (λ {σ'} → renval {σ = σ'} ρ ∘ eval β ∘ α) v x)) ⟩
    eval (λ {σ'} → renval {σ = σ'} ρ' ∘ (λ {σ''} → renval {σ = σ''} ρ ∘ eval β ∘ α) << v) t
    ≅⟨ cong (λ (f : ∀{σ} → Tm _ σ → Val _ σ) → eval (λ {σ'} → renval {σ = σ'} ρ' ∘ ((f ∘ α) << v)) t) (iext λ v₁ → ext λ u → evallem β ρ u) ⟩
    eval (λ {σ'} → renval {σ = σ'} ρ' ∘ (eval (λ {σ''} → renval {σ = σ''} ρ ∘ β) ∘ α) << v) t
    ≅⟨ sym (evallem ((eval (λ {σ'} → renval {σ = σ'} ρ ∘ β) ∘ α) << v) ρ' t)  ⟩
    renval {σ = τ} ρ' (eval ((eval (λ {σ'} → renval {σ = σ'} ρ ∘ β) ∘ α) << v) t) 
    ≅⟨ cong (λ (f : Env _ _) → renval {σ = τ} ρ' (eval f t)) (iext λ σ₁ → ext λ x → lifteval α (λ {σ'} → renval {σ = σ'} ρ ∘ β) v x) ⟩ 
    renval {σ = τ} ρ' (eval (eval ((λ {σ'} → renval {σ = σ'} ρ ∘ β) << v) ∘ lift α) t) 
    ≅⟨ cong (renval {σ = τ} ρ') (subeval (lift α) ((λ {σ'} → renval {σ = σ'} ρ ∘ β) << v) t) ⟩
    renval {σ = τ} ρ' (eval ((λ {σ'} → renval {σ = σ'} ρ ∘ β) << v) (sub (lift α) t))
    ∎))
subeval {E = E} α β (app t u) = proof
  (proj₁ (eval (eval β ∘ α) t) renId) (eval (eval β ∘ α) u)
  ≅⟨ cong ((proj₁ (eval (eval β ∘ α) t) renId)) (subeval α β u) ⟩
  (proj₁ (eval (eval β ∘ α) t) renId) (eval β (sub α u))
  ≅⟨ cong (λ f → f (eval β (sub α u))) (fcong (ifcong (cong proj₁ (subeval α β t)) E) id) ⟩
  (proj₁ (eval β (sub α t)) renId) (eval β (sub α u))
  ∎
subeval α β ze = proof nze ≡⟨⟩ nze ∎
subeval α β (su n) = proof 
  nsu (eval (eval β ∘ α) n) 
  ≅⟨ cong nsu (subeval α β n) ⟩
  nsu (eval β (sub α n))
  ∎
subeval {σ = σ} α β (rec z f n) = cong₃ natfold (subeval α β z) (subeval α β f) (subeval α β n)
subeval α β nil = refl
subeval α β (cons h t) = cong₂ consLV (subeval α β h) (subeval α β t)
subeval α β (fold z f n) = cong₃ listfold (subeval α β z) (subeval α β f) (subeval α β n)

