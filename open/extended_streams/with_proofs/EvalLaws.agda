module EvalLaws where

open import Syntax
open import NormalForms
open import Values
open import ReifyReflect
open import Folds
open import Utils
open import Evaluator

open import Data.Product
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Size


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
reneval α β (unf x f) = cong₂ St (reneval α β x) (reneval α β f) 
reneval α β (sh s) = cong x (reneval α β s)
reneval α β (st s) = SEq 
   (proof
    proj₁ (f (eval (β ∘ α) s)) renId (x (eval (β ∘ α) s))
    ≅⟨ cong (λ r → proj₁ (f r) renId (x (eval (β ∘ α) s))) (reneval α β s) ⟩
    proj₁ (f ((eval β ∘ ren α) s)) renId (x (eval (β ∘ α) s))
    ≅⟨ cong (λ r → proj₁ (f ((eval β ∘ ren α) s)) renId (x r )) (reneval α β s) ⟩
    proj₁ (f ((eval β ∘ ren α) s)) renId (x ((eval β ∘ ren α) s))
    ∎)
   (Σeq (cong proj₁ (cong f (reneval α β s))) refl (cong (proj₂ ∘ f) (reneval α β s)))



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
subeval α β (unf x f) = SEq (subeval α β x) (subeval α β f)
subeval α β (sh s) = cong x (subeval α β s)
subeval {σ = < σ >} α β (st s) = SEq
  (proof
    proj₁ (f (eval (eval β ∘ α) s)) renId (x (eval (eval β ∘ α) s))
    ≅⟨ cong (λ t → proj₁ (f (eval (eval β ∘ α) s)) renId (x t)) (subeval α β s) ⟩
    proj₁ (f (eval (eval β ∘ α) s)) renId (x ((eval β ∘ sub α) s))
    ≅⟨ cong (λ t → (proj₁ (f t) renId (x ((eval β ∘ sub α) s)))) (subeval α β s) ⟩
    proj₁ (f (eval β (sub α s))) renId (x (eval β (sub α s)))
  ∎)
  (cong f (subeval α β s))

