module Evaluator where

open import Syntax
open import NormalForms
open import Values
open import ReifyReflect
open import Folds
open import Utils

open import Data.Product
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Size


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
  eval γ (a ,, b) = (eval γ a) , (eval γ b)
  eval γ (fst t) = proj₁ (eval γ t)
  eval γ (snd t) = proj₂ (eval γ t)
  eval γ ze = nze
  eval γ (su t) = nsu (eval γ t)
  eval {σ = σ} γ (rec z f n) = natfold {σ = σ} (eval γ z) (eval γ f) (eval γ n)
  eval γ (unf x f) = St (eval γ x) (eval γ f)
  eval γ (sh s) = x (eval γ s)
  eval γ (st s) = let s' = eval γ s in St (proj₁ (f s') renId (x s')) (f s')


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
  evallem γ ρ (a ,, b) = cong₂ _,_ (evallem γ ρ a) (evallem γ ρ b)
  evallem γ ρ (fst t) = cong proj₁ (evallem γ ρ t)
  evallem γ ρ (snd t) = cong proj₂ (evallem γ ρ t)
  evallem γ ρ ze = refl
  evallem γ ρ (su t) = cong nsu (evallem γ ρ t)
  evallem {σ = σ} γ ρ (rec z f n) =  proof
    renval {σ = σ} ρ (natfold {σ = σ} (eval γ z) (eval γ f) (eval γ n)) 
    ≅⟨ renvalnatfold {σ = σ} ρ (eval γ z) (eval γ f) (eval γ n) ⟩
    natfold {σ = σ} (renval {σ = σ} ρ (eval γ z)) (renval {σ = σ ⇒ σ} ρ (eval γ f)) (renval {σ = nat} ρ (eval γ n))
    ≅⟨ cong₃ (natfold {σ = σ}) (evallem γ ρ z) (evallem γ ρ f) (evallem γ ρ n) ⟩
    natfold {σ = σ} (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) z) (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) f) (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) n)
    ∎
  evallem γ ρ (unf x f) = SEq (evallem γ ρ x) (evallem γ ρ f)
  evallem γ ρ (sh s) = cong x (evallem γ ρ s)
  evallem {σ = < σ >} γ ρ (st s) = let s' = eval γ s in SEq 
    (proof
      renval {σ = σ} ρ (proj₁ (f (eval γ s)) renId (x (eval γ s))) 
      ≅⟨ proj₂ (f s') renId ρ (x s') ⟩
      proj₁ (f (eval γ s)) (ρ ∘ renId) (renval {σ = σ} ρ (x (eval γ s)))
      ≅⟨ refl ⟩
      proj₁ (f (eval γ s)) ρ (renval {σ = σ} ρ (x (eval γ s)))
      ≅⟨ cong (λ t → proj₁ (f (eval γ s)) ρ t) (cong x (evallem γ ρ s))  ⟩
      proj₁ (f (eval γ s)) ρ (x (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) s))
      ≅⟨ cong (λ t → proj₁ t renId (x (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) s))) (cong f (evallem γ ρ s)) ⟩
      proj₁ (f (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) s)) renId (x (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) s))
      ∎)
    (Σeq (cong proj₁ (cong f (evallem γ ρ s))) 
         refl 
         (iext λ Δ₁ → iext λ Δ' → ext λ (ρ₁ : Ren _ _) → ext λ (ρ'' : Ren _ _) → ext λ v₁ → fixedtypesleft (proof
           renval {σ = σ} ρ'' (proj₁ (f (eval γ s)) (renComp ρ₁ ρ) v₁)
           ≅⟨ cong (λ t → renval {σ = σ} ρ'' (proj₁ t ρ₁ v₁)) (cong f (evallem γ ρ s)) ⟩
           renval {σ = σ} ρ'' (proj₁ (f (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) s)) ρ₁ v₁)
           ∎)))
{-

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
reneval α β (a ,, b) = Σeq (reneval α β a) refl (reneval α β b)
reneval α β (fst t) = cong proj₁ (reneval α β t)
reneval α β (snd t) = cong proj₂ (reneval α β t)
reneval α β (proj n s) = proof
  lookup (eval (β ∘ α) s) n 
  ≅⟨ cong (λ f → lookup f n) (reneval α β s) ⟩
  lookup ((eval β ∘ ren α) s) n
  ≡⟨⟩
  (eval β ∘ ren α) (proj n s)
  ∎
reneval α β (tup f) = cong tabulate (ext (λ n → reneval α β (f n)))


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
subeval α β (a ,, b) = Σeq (subeval α β a) refl (subeval α β b)
subeval α β (fst t)  = cong proj₁ (subeval α β t)
subeval α β (snd t)  = cong proj₂ (subeval α β t)
subeval α β (proj n s)  = cong (λ f → lookup f n) (subeval α β s)
subeval α β (tup f)  = cong tabulate (ext (λ n → subeval α β (f n)))

-}
