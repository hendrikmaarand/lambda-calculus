module Norm where

open import Syntax
open import Evaluator

--open import Data.Nat hiding (_<_)
open import Data.Product
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Data.Unit


data _∼_ : ∀{Γ}{σ} → Tm Γ σ → Tm Γ σ → Set where
  refl∼  : ∀{Γ}{σ} → {t : Tm Γ σ} → t ∼ t
  sym∼   : ∀{Γ}{σ} → {t u : Tm Γ σ} → t ∼ u → u ∼ t
  trans∼ : ∀{Γ}{σ} → {t u v : Tm Γ σ} → t ∼ u → u ∼ v → t ∼ v
  beta∼  : ∀{Γ σ τ} → {t : Tm (Γ < σ) τ} → {u : Tm Γ σ} → app (lam t) u ∼ sub (sub<< var u) t
  eta∼   : ∀{Γ σ τ} → {t : Tm Γ (σ ⇒ τ)} → t ∼ lam (app (ren suc t) (var zero))
  congapp∼ : ∀{Γ σ τ} → {t t' : Tm Γ (σ ⇒ τ)} → {u u' : Tm Γ σ} → t ∼ t' → u ∼ u' → app t u ∼ app t' u'
  conglam∼ : ∀{Γ σ τ} → {t t' : Tm (Γ < σ) τ} → t ∼ t' → lam t ∼ lam t'


idE : ∀{Γ} → Env Γ Γ
idE {ε} () 
idE {Γ < σ} zero = reflect σ (nvar zero)
idE {Γ < σ} (suc x) = renval suc (idE x)

--eq-idE : ∀{Γ} → Set
--eq-idE {Γ} = ∀{σ} → idE {Γ} ≅ idE {Γ}

norm : ∀{Γ σ} → Tm Γ σ → Nf Γ σ
norm t = reify _ (eval idE t)

mutual
  embNf : ∀{Γ σ} → Nf Γ σ → Tm Γ σ
  embNf (nlam n) = lam (embNf n)
  embNf (ne x) = embNe x
  
  embNe : ∀{Γ σ} → Ne Γ σ → Tm Γ σ
  embNe (nvar x) = var x
  embNe (napp t u) = app (embNe t) (embNf u)


renvaleval : ∀{Γ Δ E σ} → (γ : Env Δ Γ) → (ρ : Ren Γ E) → (t : Tm Δ σ) → eval (renval ρ ∘ γ) t ≅ renval ρ (eval γ t)
renvaleval γ ρ (var x) = refl
renvaleval γ ρ (lam t) = Σeq 
  (iext λ Δ' → ext λ (α : Ren _ _) → ext λ v → cong (λ (f : Env _ _) → eval (f << v) t) (iext λ σ' → ext λ x → renvalcomp ρ α (γ x))) 
  refl 
  (iext λ Δ → iext λ Δ' → ext λ (ρ₁ : Ren _ _) → ext λ (ρ₂ : Ren _ _) → ext λ v → fixedtypesleft (cong (λ (f : Env _ _) → 
                   renval ρ₂ (eval (f << v) t)) (iext λ σ → ext λ x → renvalcomp ρ ρ₁ (γ x)) ))
renvaleval {Γ}{Δ}{E} γ ρ (app {σ}{τ} t u) = proof
  proj₁ (eval (renval ρ ∘ γ) t) renId (eval (renval ρ ∘ γ) u) 
  ≅⟨ cong (λ f → proj₁ f renId (eval (renval ρ ∘ γ) u)) (renvaleval γ ρ t) ⟩ 
  proj₁ (renval ρ (eval γ t)) renId (eval (renval ρ ∘ γ) u) 
  ≅⟨ refl ⟩
  proj₁ (eval γ t) ρ (eval (renval ρ ∘ γ) u) 
  ≅⟨ cong (proj₁ (eval γ t) ρ) (renvaleval γ ρ u) ⟩
  proj₁ (eval γ t) ρ (renval ρ (eval γ u))
  ≅⟨ sym (proj₂ (eval γ t) renId ρ (eval γ u)) ⟩
  renval ρ (proj₁ (eval γ t) renId (eval γ u))
  ∎

renvalId : ∀{Γ σ} → (v : Val Γ σ) → renval renId v ≅ v
renvalId {Γ} {ι} v = renNfId v
renvalId {Γ} {σ ⇒ τ} v = Σeq (iext λ E → ext λ a → refl) refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ → ext λ ρ' → ext λ v₁ → fixedtypesright refl)

evalsub<< : ∀{Γ Δ σ τ} → (γ : Env Γ Δ) → (u : Tm Γ σ) → (v : Var (Γ < σ) τ) → (γ << eval γ u) v ≅ (eval γ ∘ (sub<< var u)) v
evalsub<< γ u zero = refl
evalsub<< γ u (suc v) = refl


evalSim : ∀{Γ Δ σ} → {t t' : Tm Γ σ} → {γ γ' : Env Γ Δ} → t ∼ t' → _≅_ {A = Env _ _} γ {B = Env _ _} γ' → eval γ t ≅ eval γ' t'
evalSim (refl∼ {t = t}) q = cong (λ (f : Env _ _) → eval f t) q 
evalSim (sym∼ p) q = sym (evalSim p (sym q))
evalSim (trans∼ p p₁) q = trans (evalSim p q) (evalSim p₁ refl)
evalSim {γ = γ}{γ' = γ'} (beta∼ {t = t} {u = u}) q = proof
  eval ((renval renId ∘ γ) << eval γ u) t
  ≅⟨ cong (λ (f : Env _ _) → eval (f << (eval γ u)) t) (iext λ σ' → ext λ x → renvalId (γ x)) ⟩
  eval (γ << eval γ u) t
  ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext λ σ' → ext λ x → evalsub<< γ u x) ⟩
  eval (eval γ ∘ (sub<< var u)) t
  ≅⟨ cong (λ (f : Env _ _) → eval (eval f ∘ (sub<< var u)) t) q ⟩
  eval (eval γ' ∘ (sub<< var u)) t
  ≅⟨ subeval  (sub<< var u) γ' t  ⟩
  eval γ' (sub (sub<< var u) t)
  ∎
evalSim {γ = γ}{γ' = γ'} (eta∼ {t = t}) q = Σeq 
  (iext λ Δ → ext λ (ρ : Ren _ _) → ext λ v → lem Δ ρ v) 
  refl 
  ((iext λ Δ → iext λ Δ' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → fixedtypesleft (cong (renval ρ') (lem Δ ρ v)))) where 
         lem : ∀ Δ (ρ : Ren _ Δ) v → proj₁ (eval γ t) ρ v ≅ proj₁ (eval ((λ {σ} x → renval ρ (γ' x)) << v) (ren (λ {σ} → suc) t)) (λ {σ} x → x) v
         lem Δ ρ v = trans (trans (cong (λ (f : Env _ _) → proj₁ (eval f t) ρ v) q) (sym (cong (λ f → proj₁ f id v) (renvaleval γ' ρ t)))) (cong (λ f → proj₁ f id v) (reneval suc ((λ {σ} x → renval ρ (γ' x)) << v) t))
evalSim (congapp∼ p p₁) (q) = cong₂ (λ f g → proj₁ f renId g) (evalSim p q) (evalSim p₁ q)
evalSim (conglam∼ {t = t}{t' = t'} p) q = Σeq 
  (iext λ Δ → ext λ (α : Ren _ _) → ext λ v → evalSim p (iext λ σ₁ → cong (λ (f : Env _ _) → (renval α ∘ f) << v) q)) 
  refl 
  (iext λ Δ → iext λ Δ' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → 
      fixedtypesleft (cong (renval ρ') (evalSim p (iext λ _ → ext λ x → cong (λ f → ((λ {_} x → renval {σ = _} ρ (f x)) << v) x) q))))





{-mutual
  V⟦_⟧_R_⇓_ : ∀{Γ Δ} σ → (t : Tm Γ σ) → (γ : Env Γ Δ) → (v : Val Δ σ) → Set
  V⟦ ι ⟧ t R γ ⇓ v = embNf (reify ι v) ∼ sub (λ {σ} → embNf ∘ reify σ ∘ γ) t
  V⟦ σ ⇒ τ ⟧ t R γ ⇓ f = ∀{Δ} (ρ : Ren _ Δ) → (u : Tm _ σ) → (v : Val Δ σ) → V⟦ σ ⟧ u R renval ρ ∘ γ ⇓ v →
                                C⟦ τ ⟧ app t u R renval ρ ∘ γ ⇓ proj₁ f ρ v 

  C⟦_⟧_R_⇓_ : ∀{Γ Δ} σ → (t : Tm Γ σ) → (γ : Env Γ Δ) → (v : Val Δ σ) → Set
  C⟦ σ ⟧ t R γ ⇓ v =  V⟦ σ ⟧ t R γ ⇓ v × embNf (reify σ v) ∼ (sub (λ {σ} → embNf ∘ reify σ ∘ γ) t)  
-}



mutual
  _∋_R_ : ∀{Γ} σ → (t : Tm Γ σ) → (v : Val Γ σ) → Set
  ι ∋ t R v = t ∼ embNf (reify ι v)
  (σ ⇒ τ) ∋ t R f = ∀{Δ} → (ρ : Ren _ Δ)(u : Tm Δ σ)(v : Val Δ σ) → σ ∋ u R v → τ ∋ app (ren ρ t) u S proj₁ f ρ v

  _∋_S_ : ∀{Γ} σ → (t : Tm Γ σ) → (v : Val Γ σ) → Set
  σ ∋ t S v = σ ∋ t R v × t ∼ embNf (reify σ v)

_E_ : ∀{Γ Δ} → (ρ : Sub Γ Δ) → (η : Env Γ Δ) → Set
ρ E η = ∀{σ} → (x : Var _ σ) → σ ∋ ρ x S η x



≅to∼ : ∀{Γ σ} → {t t' : Tm Γ σ} → t ≅ t' → t ∼ t'
≅to∼ refl = refl∼


ren∼ : ∀{Γ Δ σ} → {t t' : Tm Γ σ} → {ρ ρ' : Ren Γ Δ} → _≅_ {A = Ren _ _} ρ {B = Ren _ _} ρ' → t ∼ t' → ren ρ t ∼ ren ρ' t'
ren∼ refl refl∼ = refl∼
ren∼ p (sym∼ q) = sym∼ (ren∼ (sym p) q)
ren∼ p (trans∼ q q₁) = trans∼ (ren∼ p q) (ren∼ refl q₁)
ren∼ {ρ = ρ} refl (beta∼ {t = t}{u = u}) = trans∼ (beta∼ {t = ren (wk ρ) t}{u = ren ρ u}) {!!} 
ren∼ p eta∼ = {!!}
ren∼ p (congapp∼ q q₁) = congapp∼ (ren∼ p q) (ren∼ p q₁)
ren∼ p (conglam∼ q) = conglam∼ (ren∼ (cong wk p) q)


R∼ : ∀{Γ σ} → {t t' : Tm Γ σ} → {v : Val Γ σ} → σ ∋ t R v → t ∼ t' → σ ∋ t' R v
R∼ {Γ} {ι} r p = trans∼ (sym∼ p) r
R∼ {Γ} {σ ⇒ τ} r p = λ ρ u v' r' → let a , b = r ρ u v' r' in
  R∼ a (congapp∼ (ren∼ refl p) refl∼) , trans∼ (congapp∼ (sym∼ (ren∼ refl p)) refl∼) b


S∼ : ∀{Γ σ} → (t t' : Tm Γ σ) → (v : Val Γ σ) → σ ∋ t S v → t ∼ t' → σ ∋ t' S v
S∼ {Γ} {ι} t t' v (a , b) p = trans∼ (sym∼ p) a , trans∼ (sym∼ p) b 
S∼ {Γ} {σ ⇒ τ} t t' v (a , b) p = (λ ρ u v' p' → S∼ {σ = τ} (app (ren ρ t) u) (app (ren ρ t') u) (proj₁ v ρ v') (a ρ u v' p') 
                                                     (congapp∼ (ren∼ refl p) refl∼)) , 
                                   trans∼ (sym∼ p) b


lemma : ∀{Γ Δ σ} (t : Tm Γ σ) → (ρ : Sub Γ Δ) → (η : Env Γ Δ) → ρ E η → σ ∋ sub ρ t S (eval η t)
lemma (var x) ρ η e = e x
lemma (lam t) ρ η e = (λ ρ' u v p → {!lemma t!} , {!!}) , 
                                    conglam∼ (≅to∼ {!!})
--proj₁ (lemma t (sub<< (ren ρ' ∘ ρ) u) ((renval ρ' ∘ η) << v) ?) , ?
lemma (app t u) ρ η e = let 
  p   , q   = lemma t ρ η e
  p'  , q'  = lemma u ρ η e
  p'' , q'' = (p id (sub ρ u) (eval η u) p') in
              R∼ p'' (≅to∼ (cong (λ x → app x (sub ρ u)) (renid (sub ρ t)))) ,
              trans∼ (congapp∼ (≅to∼ (sym (renid (sub ρ t)))) refl∼) q''





{-

completeness_lemma : ∀{Γ Δ σ} → (t : Tm Γ σ) → (γ : Env Γ Δ) → C⟦ σ ⟧ t R γ ⇓ (eval γ t)  
completeness_lemma (var x) γ = {!!}
completeness_lemma (lam t) γ = (λ ρ u v p → {!completeness_lemma t ((renval ρ ∘ γ) << v)!}) , {!!}
completeness_lemma (app t u) γ = let
  f , p = completeness_lemma t γ
  v , q = completeness_lemma u γ
  x , y = f renId u (eval γ u) {!!} in
    {!x ,  !}

-}
soundness : ∀{Γ σ} → {t t' : Tm Γ σ} → t ∼ t' → norm t ≅ norm t'
soundness p = cong (reify _) (evalSim p refl)
  
completeness : ∀{Γ σ} → (t : Tm Γ σ) → t ∼ embNf (norm t)
completeness (var x) = {! !}
completeness (lam t) = trans∼ (conglam∼ (completeness t)) {!!}
completeness (app t u) = trans∼ (congapp∼ (completeness t) (completeness u)) (trans∼ beta∼ {!!})

third : ∀{Γ σ} → (t t' : Tm Γ σ) → norm t ≅ norm t' → t ∼ t'
third t t' p = trans∼ (completeness t) (trans∼ (subst (λ x → embNf (norm t) ∼ embNf x) p refl∼) (sym∼ (completeness t')))



