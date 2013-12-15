module Norm where

open import Syntax
open import Evaluator
open import ReifyReflect

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
  congsc∼  : ∀{Γ}   → {t t' : Tm Γ nat} → t ∼ t' → sc t ∼ sc t'

idE : ∀{Γ} → Env Γ Γ
idE {ε} () 
idE {Γ < σ} zero = reflect σ (nvar zero)
idE {Γ < σ} (suc {σ = σ'} x) = renval {σ'} suc (idE x)

norm : ∀{Γ σ} → Tm Γ σ → Nf Γ σ
norm t = reify _ (eval idE t)

mutual
  embNf : ∀{Γ σ} → Nf Γ σ → Tm Γ σ
  embNf (nlam n) = lam (embNf n)
  embNf (ne x) = embNe x
  embNf nzero = ze
  embNf (nsuc n) = sc (embNf n)
  embNf (a ,-, b) = embNf a ,, embNf b
  
  embNe : ∀{Γ σ} → Ne Γ σ → Tm Γ σ
  embNe (nvar x) = var x
  embNe (napp t u) = app (embNe t) (embNf u)
  embNe (nrec z f n) = rec (embNf z) (embNf f) (embNe n)
  embNe (nfst n) = fst (embNe n)
  embNe (nsnd n) = snd (embNe n)


renvaleval : ∀{Γ Δ E σ} → (γ : Env Δ Γ) → (ρ : Ren Γ E) → (t : Tm Δ σ) → eval (λ {σ'} → renval {σ'} ρ ∘ γ) t ≅ renval {σ} ρ (eval γ t)
renvaleval γ ρ (var x) = refl
renvaleval {σ = σ ⇒ τ} γ ρ (lam t) = Σeq 
  (iext λ Δ' → ext λ (α : Ren _ _) → ext λ v → cong (λ (f : Env _ _) → eval (f << v) t) (iext λ σ' → ext λ x → renvalcomp {σ'} ρ α (γ x))) 
  refl 
  (iext λ Δ → iext λ Δ' → ext λ (ρ₁ : Ren _ _) → ext λ (ρ₂ : Ren _ _) → ext λ v → fixedtypesleft (cong (λ (f : Env _ _) → 
                   renval {τ} ρ₂ (eval (f << v) t)) (iext λ σ' → ext λ x → renvalcomp {σ'} ρ ρ₁ (γ x))))
renvaleval {Γ}{Δ}{E} γ ρ (app {σ}{τ} t u) = proof
  proj₁ (eval (λ {σ'} → renval {σ'} ρ ∘ γ) t) renId (eval (λ {σ'} → renval {σ'} ρ ∘ γ) u) 
  ≅⟨ cong (λ f → proj₁ f renId (eval (λ {σ'} → renval {σ'} ρ ∘ γ) u)) (renvaleval γ ρ t) ⟩ 
  proj₁ (renval {σ ⇒ τ} ρ (eval γ t)) renId (eval (λ {σ'} → renval {σ'} ρ ∘ γ) u) 
  ≅⟨ refl ⟩
  proj₁ (eval γ t) ρ (eval (λ {σ'} →  renval {σ'} ρ ∘ γ) u) 
  ≅⟨ cong (proj₁ (eval γ t) ρ) (renvaleval γ ρ u) ⟩
  proj₁ (eval γ t) ρ (renval {σ} ρ (eval γ u))
  ≅⟨ sym (proj₂ (eval γ t) renId ρ (eval γ u)) ⟩
  renval {τ} ρ (proj₁ (eval γ t) renId (eval γ u))
  ∎
renvaleval γ ρ ze = refl
renvaleval γ ρ (sc t) = cong nsuc (renvaleval γ ρ t)
renvaleval {σ = σ} γ ρ (rec z f n) = proof
  nfold (eval (λ {σ'} → renval {σ'} ρ ∘ γ) z) (eval (λ {σ'} → renval {σ'} ρ ∘ γ) f) (eval (λ {σ'} → renval {σ'} ρ ∘ γ) n)
  ≅⟨ cong₃ nfold (renvaleval γ ρ z) (renvaleval γ ρ f) (renvaleval γ ρ n) ⟩
   nfold (renval {σ} ρ (eval γ z)) 
         ((λ {E} β → proj₁ (eval γ f) (β ∘ ρ)) ,
                               (λ {Δ₁} {Δ'} ρ₁ ρ' v₁ → trans (proj₂ (eval γ f) (ρ₁ ∘ ρ) ρ' v₁) refl)) 
         (renNf ρ (eval γ n))
  ≅⟨ sym (renvalnfold ρ (eval γ z) (eval γ f) (eval γ n)) ⟩
  renval {σ} ρ (nfold (eval γ z) (eval γ f) (eval γ n))
  ∎ 
renvaleval γ ρ (a ,, b) = {!!}
renvaleval γ ρ (fst a) = {!!}
renvaleval γ ρ (snd a) = {!!}

{-
renvalId : ∀{Γ σ} → (v : Val Γ σ) → renval renId v ≅ v
renvalId {Γ} {nat} v = renNfId v
renvalId {Γ} {σ ⇒ τ} v = Σeq (iext λ E → ext λ a → refl) refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ → ext λ ρ' → ext λ v₁ → fixedtypesright refl)
renvalId {Γ} {σ ∧ τ} v = {!!}

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
evalSim (congsc∼ p) q = cong nsuc (evalSim p q)



Good : ∀{Γ} σ → Tm Γ σ → Val Γ σ → Set
Good nat t n = ⊤
Good (σ ⇒ τ) t f = ∀ u v → Good σ u v → Good τ (app t u) (proj₁ f id v)
Good (σ ∧ τ) t p = {!!} 

GoodEnv : ∀{Γ Δ} → (γ : Env Γ Δ) → Set
GoodEnv γ = ∀ {σ}(x : Var _ σ) → Good σ (sub (λ {σ} x → embNf (reify σ (γ x))) (var x)) (γ x) 

_G<<_ : ∀{Γ Δ} → {γ : Env Γ Δ} → GoodEnv γ → ∀{σ} → {t : Tm Δ σ}{v : Val Δ σ} → Good σ t v → GoodEnv (γ << v)
(γ G<< v) zero = v
(γ G<< v) (suc x) = γ x 

{-
GoodEnv {ε} ε = ⊤
GoodEnv {Γ < σ} (γ < v) = GoodEnv Γ γ × Good σ v
-}

lem : ∀{Γ σ} → {t u : Tm Γ σ} → t ∼ u → ∀{v} → Good σ t v → Good σ u v
lem {Γ} {nat} p g = g
lem {Γ} {σ ⇒ τ} p g = {!subst!} 
lem {Γ} {σ ∧ τ} p g = {!!}

good : ∀{Γ Δ σ} → (γ : Env Γ Δ) → (gγ : GoodEnv γ) → (t : Tm Γ σ) → Good σ (sub (λ {σ} x → embNf (reify σ (γ x))) t) (eval γ t)
good γ gγ (var x) = gγ x
good γ gγ (lam t) = λ u v gv → lem {t = sub (sub<< (λ {σ} x → embNf (reify σ (γ x))) u) t}{u = app (sub (λ {σ} x → embNf (reify σ (γ x))) (lam t)) u} {!sym∼ beta∼!} {eval (γ << v) t} (good (γ << v) (gγ G<< gv) t)
good γ gγ (app t u) = let 
  gf = good γ gγ t
  gv = good γ gγ u in
  gf (sub (λ {σ} x → embNf (reify σ (γ x))) u) (eval γ u) gv
good γ gγ ze = {!!}
good γ gγ (sc t) = {!!}
good γ gγ (rec t t₁ t₂) = {!!}


soundness : ∀{Γ σ} → {t t' : Tm Γ σ} → t ∼ t' → norm t ≅ norm t'
soundness p = cong (reify _) (evalSim p refl)


completeness : ∀{Γ σ} → (t : Tm Γ σ) → t ∼ embNf (norm t)
completeness (var x) = {!!}
completeness (lam t) = trans∼ (conglam∼ (completeness t)) {!!}
completeness (app t u) = trans∼ (congapp∼ (completeness t) (completeness u)) (trans∼ beta∼ {!!})
completeness ze = refl∼
completeness (sc t) = congsc∼ (completeness t)
completeness (rec z f n) = {!!}

third : ∀{Γ σ} → (t t' : Tm Γ σ) → norm t ≅ norm t' → t ∼ t'
third t t' p = trans∼ (completeness t) (trans∼ (subst (λ x → embNf (norm t) ∼ embNf x) p refl∼) (sym∼ (completeness t')))


-}