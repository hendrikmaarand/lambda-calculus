module Norm where

open import Syntax
open import ReifyReflect
open import Evaluator

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
  eta∼   : ∀{Γ σ τ} → {t : Tm Γ (σ ⇒ τ)} → t ∼ lam (app (ren vsu t) (var vze))
  congapp∼ : ∀{Γ σ τ} → {t t' : Tm Γ (σ ⇒ τ)} → {u u' : Tm Γ σ} → t ∼ t' → u ∼ u' → app t u ∼ app t' u'
  conglam∼ : ∀{Γ σ τ} → {t t' : Tm (Γ < σ) τ} → t ∼ t' → lam t ∼ lam t'
  congsc∼  : ∀{Γ} → {t t' : Tm Γ nat} → t ∼ t' → su t ∼ su t'
  congcons∼ : ∀{Γ σ} → {x x' : Tm Γ σ}{xs xs' : Tm Γ [ σ ]} → x ∼ x' → xs ∼ xs' → cons x xs ∼ cons x' xs'
  congrec∼  : ∀{Γ σ} → {z z' : Tm Γ σ}{f f' : Tm Γ (σ ⇒ σ)}{n n' : Tm Γ nat} → z ∼ z' → f ∼ f' → n ∼ n' → rec z f n ∼ rec z' f' n'
  congreczero∼ : ∀{Γ σ} → (z : Tm Γ σ)(f : Tm Γ (σ ⇒ σ)) → rec z f ze ∼ z
  congrecsc∼ : ∀{Γ σ} → (z : Tm Γ σ)(f : Tm Γ (σ ⇒ σ))(n : Tm Γ nat) → rec z f (su n) ∼ app f (rec z f n)
  congfold∼ : ∀{Γ σ τ} → {z z' : Tm Γ τ}{f f' : Tm Γ (σ ⇒ τ ⇒ τ)}{n n' : Tm Γ [ σ ]} → z ∼ z' → f ∼ f' → n ∼ n' → fold z f n ∼ fold z' f' n'
  congfoldnil∼ : ∀{Γ σ τ} → (z : Tm Γ τ)(f : Tm Γ (σ ⇒ τ ⇒ τ)) → fold z f nil ∼ z
  congfoldcons∼ : ∀{Γ σ τ} → (z : Tm Γ τ)(f : Tm Γ (σ ⇒ τ ⇒ τ))(x : Tm Γ σ)(xs : Tm Γ [ σ ]) → fold z f (cons x xs) ∼ app (app f x) (fold z f xs)

idE : ∀{Γ} → Env Γ Γ
idE {ε} () 
idE {Γ < σ} vze = reflect σ (nvar vze)
idE {Γ < σ} (vsu {σ = σ'} x) = renval {σ = σ'} vsu (idE x)

norm : ∀{Γ σ} → Tm Γ σ → Nf Γ σ
norm t = reify _ (eval idE t)


renvaleval : ∀{Γ Δ E σ} → (γ : Env Δ Γ) → (ρ : Ren Γ E) → (t : Tm Δ σ) → eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) t ≅ renval {σ = σ} ρ (eval γ t)
renvaleval γ ρ (var x) = refl
renvaleval {σ = σ ⇒ τ} γ ρ (lam t) = Σeq 
  (iext λ Δ' → ext λ (α : Ren _ _) → ext λ v → cong (λ (f : Env _ _) → eval (f << v) t) (iext λ σ' → ext λ x → renvalcomp {σ = σ'} α ρ (γ x)))
  refl 
  (iext λ Δ₁ → iext λ Δ₂ → ext λ (ρ₁ : Ren _ _) → ext λ (ρ₂ : Ren _ _) → ext λ v → fixedtypesleft 
        (cong (λ (f : Env _ _) → renval {σ = τ} ρ₂ (eval (f << v) t)) (iext λ σ' → ext λ x → renvalcomp {σ = σ'} ρ₁ ρ (γ x))))
renvaleval {Γ}{Δ}{E} γ ρ (app {σ}{τ} t u) = proof
  proj₁ (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) t) renId (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) u) 
  ≅⟨ cong (λ f → proj₁ f renId (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) u)) (renvaleval γ ρ t) ⟩ 
  proj₁ (renval {σ = σ ⇒ τ} ρ (eval γ t)) renId (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) u) 
  ≅⟨ refl ⟩
  proj₁ (eval γ t) ρ (eval (λ {σ'} →  renval {σ = σ'} ρ ∘ γ) u) 
  ≅⟨ cong (proj₁ (eval γ t) ρ) (renvaleval γ ρ u) ⟩
  proj₁ (eval γ t) ρ (renval {σ = σ} ρ (eval γ u))
  ≅⟨ sym (proj₂ (eval γ t) renId ρ (eval γ u)) ⟩
  renval {σ = τ} ρ (proj₁ (eval γ t) renId (eval γ u))
  ∎
renvaleval γ ρ ze = refl
renvaleval γ ρ (su t) = cong nsu (renvaleval γ ρ t)
renvaleval {σ = σ} γ ρ (rec z f n) = proof
  natfold {σ = σ} (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) z) (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) f) (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) n)
  ≅⟨ cong₃ (natfold {σ = σ}) (renvaleval γ ρ z) (renvaleval γ ρ f) (renvaleval γ ρ n) ⟩
   natfold {σ = σ} (renval {σ = σ} ρ (eval γ z))
         ((λ {E} β → proj₁ (eval γ f) (β ∘ ρ)) ,
                               (λ {Δ₁} {Δ'} ρ₁ ρ' v₁ → trans (proj₂ (eval γ f) (ρ₁ ∘ ρ) ρ' v₁) refl)) 
         (renNf ρ (eval γ n))
  ≅⟨ sym (renvalnatfold {σ = σ} ρ (eval γ z) (eval γ f) (eval γ n)) ⟩
  renval {σ = σ} ρ (natfold {σ = σ} (eval γ z) (eval γ f) (eval γ n))
  ∎
renvaleval γ ρ nil = refl
renvaleval γ ρ (cons h t) = cong₂ consLV (renvaleval γ ρ h) (renvaleval γ ρ t)
renvaleval γ ρ (fold {σ = σ}{τ = τ} z f xs) = proof
  listfold {τ = τ} (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) z) (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) f) (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) xs)
  ≅⟨ cong₃ listfold (renvaleval γ ρ z) (renvaleval γ ρ f) (renvaleval γ ρ xs) ⟩ 
  listfold {σ = σ}{τ = τ} (renval {σ = τ} ρ (eval γ z)) (renval {σ = σ ⇒ τ ⇒ τ} ρ (eval γ f)) (renval {σ = [ σ ]} ρ (eval γ xs))
  ≅⟨ sym (renvallistfold ρ (eval γ z) (eval γ f) (eval γ xs)) ⟩
  renval {σ = τ} ρ (listfold {τ = τ} (eval γ z) (eval γ f) (eval γ xs))
  ∎


renvalId : ∀{Γ σ} → (v : Val Γ σ) → renval {σ = σ} renId v ≅ v
renvalId {Γ} {ι}   v = renNfId v
renvalId {Γ} {nat} v = renNfId v
renvalId {Γ} {σ ⇒ τ} v = Σeq (iext λ E → ext λ a → refl) refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ → ext λ ρ' → ext λ v₁ → fixedtypesright refl)
renvalId {σ = [ σ ]} (neLV x) = cong neLV (renNeId x)
renvalId {σ = [ σ ]} nilLV = refl
renvalId {σ = [ σ ]} (consLV x v) = cong₂ consLV (renvalId {σ = σ} x) (renvalId {σ = [ σ ]} v) 


evalsub<< : ∀{Γ Δ σ τ} → (γ : Env Γ Δ) → (u : Tm Γ σ) → (v : Var (Γ < σ) τ) → (γ << eval γ u) v ≅ (eval γ ∘ (sub<< var u)) v
evalsub<< γ u vze = refl
evalsub<< γ u (vsu v) = refl

evalSim : ∀{Γ Δ σ} → {t t' : Tm Γ σ} → {γ γ' : Env Γ Δ} → t ∼ t' → _≅_ {A = Env _ _} γ {B = Env _ _} γ' → eval γ t ≅ eval γ' t'
evalSim (refl∼ {t = t}) q = cong (λ (f : Env _ _) → eval f t) q 
evalSim (sym∼ p) q = sym (evalSim p (sym q))
evalSim (trans∼ p p₁) q = trans (evalSim p q) (evalSim p₁ refl)
evalSim {σ = σ} {γ = γ}{γ' = γ'} (beta∼ {t = t} {u = u}) q = proof
  eval ((λ {σ'} → renval {σ = σ'} renId ∘ γ) << eval γ u) t
  ≅⟨ cong (λ (f : Env _ _) → eval (f << (eval γ u)) t) (iext λ σ' → ext λ x → renvalId {σ = σ'} (γ x)) ⟩
  eval (γ << eval γ u) t
  ≅⟨ cong (λ (f : Env _ _) → eval f t) (iext λ σ' → ext λ x → evalsub<< γ u x) ⟩
  eval (eval γ ∘ (sub<< var u)) t
  ≅⟨ cong (λ (f : Env _ _) → eval (eval f ∘ (sub<< var u)) t) q ⟩
  eval (eval γ' ∘ (sub<< var u)) t
  ≅⟨ subeval  (sub<< var u) γ' t  ⟩
  eval γ' (sub (sub<< var u) t)
  ∎
evalSim {σ = σ ⇒ τ} {γ = γ}{γ' = γ'} (eta∼ {t = t}) q = Σeq 
  (iext λ Δ → ext λ (ρ : Ren _ _) → ext λ v → lem Δ ρ v) 
  refl 
  ((iext λ Δ → iext λ Δ' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → fixedtypesleft (cong (renval {σ = τ} ρ') (lem Δ ρ v)))) where 
         lem : ∀ Δ (ρ : Ren _ Δ) v → proj₁ (eval γ t) ρ v ≅ proj₁ (eval ((λ {σ} x → renval {σ = σ} ρ (γ' x)) << v) (ren (λ {σ} → vsu) t)) (λ {σ} x → x) v
         lem Δ ρ v = trans (trans (cong (λ (f : Env _ _) → proj₁ (eval f t) ρ v) q) (sym (cong (λ f → proj₁ f id v) (renvaleval γ' ρ t)))) (cong (λ f → proj₁ f id v) (reneval vsu ((λ {σ} x → renval {σ = σ} ρ (γ' x)) << v) t))
evalSim (congapp∼ p p₁) (q) = cong₂ (λ f g → proj₁ f renId g) (evalSim p q) (evalSim p₁ q)
evalSim {σ = σ ⇒ τ} (conglam∼ {t = t}{t' = t'} p) q = Σeq 
  (iext λ Δ → ext λ (α : Ren _ _) → ext λ v → evalSim p (iext λ σ₁ → cong (λ (f : Env _ _) → (λ {σ'} → renval {σ = σ'} α ∘ f) << v) q)) 
  refl 
  (iext λ Δ → iext λ Δ' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → 
      fixedtypesleft (cong (renval {σ = τ} ρ') (evalSim p (iext λ _ → ext λ x → cong (λ f → ((λ {σ'} x → renval {σ = σ'} ρ (f x)) << v) x) q))))
evalSim (congsc∼ p) q = cong nsu (evalSim p q)
evalSim (congcons∼ x xs) q = cong₂ consLV (evalSim x q) (evalSim xs q)
evalSim (congrec∼ z f n) q = cong₃ natfold (evalSim z q) (evalSim f q) (evalSim n q)
evalSim (congreczero∼ z f) refl = refl
evalSim {σ = σ}{γ = γ} (congrecsc∼ z f n) refl = refl
evalSim (congfold∼ z f n) q = cong₃ listfold (evalSim z q) (evalSim f q) (evalSim n q)
evalSim (congfoldnil∼ z f) refl = refl
evalSim (congfoldcons∼ z f x xs) refl = refl


≅to∼ : ∀{Γ σ} → {t t' : Tm Γ σ} → t ≅ t' → t ∼ t'
≅to∼ refl = refl∼


sub<<ren : ∀{Γ Δ σ τ} → (α : Ren Γ Δ)(u : Tm Γ σ)(y : Var (Γ < σ) τ) → sub<< var (ren α u) (wk α y) ≅ ren α (sub<< var u y)
sub<<ren α u vze = refl
sub<<ren α u (vsu x) = refl

ren∼ : ∀{Γ Δ σ} → {t t' : Tm Γ σ} → {ρ ρ' : Ren Γ Δ} → _≅_ {A = Ren _ _} ρ {B = Ren _ _} ρ' → t ∼ t' → ren ρ t ∼ ren ρ' t'
ren∼ refl refl∼ = refl∼
ren∼ p (sym∼ q) = sym∼ (ren∼ (sym p) q)
ren∼ p (trans∼ q q₁) = trans∼ (ren∼ p q) (ren∼ refl q₁)
ren∼ {ρ = ρ} refl (beta∼ {t = t}{u = u}) = trans∼ (beta∼ {t = ren (wk ρ) t}{u = ren ρ u}) (≅to∼ (
  proof
  sub (sub<< var (ren ρ u)) (ren (wk ρ) t) 
  ≅⟨ subren (sub<< var (ren ρ u)) (wk ρ) t ⟩
  sub ((sub<< var (ren ρ u)) ∘ (wk ρ)) t
  ≅⟨ cong (λ (x : Sub _ _) → sub x t) (iext (λ σ' → ext λ y → sub<<ren ρ u y))  ⟩
  sub (ren ρ ∘ (sub<< var u)) t
  ≅⟨ sym (rensub ρ (sub<< var u) t) ⟩
  ren ρ (sub (sub<< var u) t)
  ∎)) 
ren∼ {ρ = ρ} refl (eta∼ {t = t}) = trans∼ (eta∼ {t = ren ρ t}) (conglam∼ (congapp∼ (≅to∼ (
  proof
  ren vsu (ren ρ t) 
  ≅⟨ sym (rencomp vsu ρ t) ⟩
  ren (vsu ∘ ρ) t 
  ≅⟨ refl ⟩
  ren ((wk ρ) ∘ vsu) t 
  ≅⟨ rencomp (wk ρ) vsu t ⟩
  ren (wk ρ) (ren vsu t)
  ∎)) refl∼))
ren∼ p (congapp∼ q q₁) = congapp∼ (ren∼ p q) (ren∼ p q₁)
ren∼ p (conglam∼ q) = conglam∼ (ren∼ (cong wk p) q)
ren∼ p (congsc∼ n) = congsc∼ (ren∼ p n)
ren∼ p (congcons∼ x xs) = congcons∼ (ren∼ p x) (ren∼ p xs)
ren∼ p (congrec∼ z f n) = congrec∼ (ren∼ p z) (ren∼ p f) (ren∼ p n)
ren∼ {ρ = ρ} p (congreczero∼ z f) = trans∼ (congreczero∼ (ren ρ z) (ren ρ f)) (ren∼ p refl∼)
ren∼ {ρ = ρ} refl (congrecsc∼ z f n) = congrecsc∼ (ren ρ z) (ren ρ f) (ren ρ n)
ren∼ p (congfold∼ z f n) = congfold∼ (ren∼ p z) (ren∼ p f) (ren∼ p n)
ren∼ {ρ = ρ} p (congfoldnil∼ z f) = trans∼ (congfoldnil∼ (ren ρ z) (ren ρ f)) (ren∼ p refl∼)
ren∼ {ρ = ρ} refl (congfoldcons∼ z f x xs) = (congfoldcons∼ (ren ρ z) (ren ρ f) (ren ρ x) (ren ρ xs))


_∋_R_ : ∀{Γ} σ → (t : Tm Γ σ) → (v : Val Γ σ) → Set
ι ∋ t R v = t ∼ embNf (reify ι v)
nat ∋ t R nenat x = t ∼ embNe x
nat ∋ t R nze = t ∼ ze
nat ∋ t R nsu v = Σ (Tm _ nat) (λ t' → t ∼ su t' × nat ∋ t' R v)
(σ ⇒ τ) ∋ t R f = ∀{Δ} → (ρ : Ren _ Δ)(u : Tm Δ σ)(v : Val Δ σ) → σ ∋ u R v → τ ∋ app (ren ρ t) u R proj₁ f ρ v
[ σ ] ∋ t R neLV x = t ∼ embNe x
[ σ ] ∋ t R nilLV = t ∼ nil
[ σ ] ∋ t R consLV v vs = Σ (Tm _ σ) (λ h → Σ (Tm _ [ σ ]) (λ hs → t ∼ cons h hs × σ ∋ h R v × [ σ ] ∋ hs R vs))



R∼ : ∀{Γ σ} → {t t' : Tm Γ σ} → {v : Val Γ σ} → σ ∋ t R v → t ∼ t' → σ ∋ t' R v
R∼ {σ = ι} r p = trans∼ (sym∼ p) r 
R∼ {σ = nat} {v = nenat x} r p = trans∼ (sym∼ p) r
R∼ {σ = nat} {v = nze} r p = trans∼ (sym∼ p) r
R∼ {σ = nat}{t = t}{t' = t'} {v = nsu n} (t'' , t'∼ , t''Rn) p = t'' , ((trans∼ (sym∼ p) t'∼) , t''Rn)
R∼ {σ = σ ⇒ τ} r p = λ ρ u v r' → let a = r ρ u v r' in R∼ a (congapp∼ (ren∼ refl p) refl∼)
R∼ {σ = [ σ ]} {v = neLV x} r p = trans∼ (sym∼ p) r
R∼ {σ = [ σ ]} {v = nilLV} r p = trans∼ (sym∼ p) r
R∼ {σ = [ σ ]} {v = consLV h tl} (fh , ft , t∼ , tsRvs) p = fh , (ft , ((trans∼ (sym∼ p) t∼) , tsRvs))


mutual
  ren-embNf : ∀{Γ Δ σ} → (α : Ren Γ Δ)(n : Nf Γ σ) → ren α (embNf n) ∼ embNf (renNf α n)
  ren-embNf α (nlam n) = conglam∼ (ren-embNf (wk α) n)
  ren-embNf α (ne x) = ren-embNe α x
  ren-embNf α (nenat x) = ren-embNe α x
  ren-embNf α (ne[] x) = ren-embNe α x
  ren-embNf α nze = refl∼
  ren-embNf α (nsu n) = congsc∼ (ren-embNf α n)
  ren-embNf α nnil = refl∼
  ren-embNf α (ncons h t) = congcons∼ (ren-embNf α h) (ren-embNf α t)

  ren-embNe : ∀{Γ Δ σ} → (α : Ren Γ Δ)(n : Ne Γ σ) → ren α (embNe n) ∼ embNe (renNe α n)
  ren-embNe α (nvar x) = refl∼
  ren-embNe α (napp t u) = congapp∼ (ren-embNe α t) (ren-embNf α u)
  ren-embNe α (nrec z f n) = congrec∼ (ren-embNf α z) (ren-embNf α f) (ren-embNe α n)
  ren-embNe α (nfold z f n) = congfold∼ (ren-embNf α z) (ren-embNf α f) (ren-embNe α n)


R-ren : ∀{Γ Δ σ}{t : Tm Γ σ}{v : Val Γ σ} → (α : Ren Γ Δ) → σ ∋ t R v → σ ∋ ren α t R renval {σ = σ} α v
R-ren {σ = ι}{v = v} α r = trans∼ (ren∼ refl r) (ren-embNf α v)
R-ren {σ = nat} {v = nenat x} α r = trans∼ (ren∼ refl r) (ren-embNe α x)
R-ren {σ = nat} {v = nze} α r = ren∼ refl r
R-ren {σ = nat} {v = nsu v} α (n , t∼ , nRv) = (ren α n) , ((ren∼ refl t∼) , R-ren {t = n}{v = v} α nRv)
R-ren {σ = σ ⇒ τ} α r ρ u v₁ x = R∼ {σ = τ} (r (ρ ∘ α) u v₁ x) (congapp∼ (≅to∼ (rencomp ρ α _)) refl∼)
R-ren {σ = [ σ ]} {v = neLV x} α r = trans∼ (ren∼ refl r) (ren-embNe α x)
R-ren {σ = [ σ ]} {v = nilLV} α r = ren∼ refl r
R-ren {σ = [ σ ]} {v = consLV v vs} α (hd , tl , t∼ , hdRv , tlRvs) = (ren α hd) , ((ren α tl) , (ren∼ refl t∼) , ((R-ren {t = hd} α hdRv) , (R-ren {t = tl}{v = vs} α tlRvs)))


_E_ : ∀{Γ Δ} → (ρ : Sub Γ Δ) → (η : Env Γ Δ) → Set
ρ E η = ∀{σ} → (x : Var _ σ) → σ ∋ ρ x R η x

E-ren : ∀{Γ Δ Δ₁}{ρ : Sub Γ Δ}{η : Env Γ Δ} → (α : Ren Δ Δ₁) → ρ E η → (ren α ∘ ρ) E (λ {σ'} → renval {σ = σ'} α ∘ η)
E-ren α e (vze {σ = σ}) = R-ren {σ = σ} α (e vze)
E-ren α e (vsu {σ = σ} x) = R-ren {σ = σ} α (e (vsu x))


E<< : ∀{Γ Δ σ} → {ρ : Sub Γ Δ}{η : Env Γ Δ}{v : Val Δ σ}{u : Tm Δ σ} → (p : σ ∋ u R v)(e : ρ E η) → (sub<< ρ u) E (η << v)
E<< p e vze = p
E<< p e (vsu x) = e x

E<<-ren : ∀{Γ Δ Δ₁ σ} → {ρ : Sub Γ Δ}{η : Env Γ Δ}{v : Val Δ₁ σ}{u : Tm Δ₁ σ} → (α : Ren Δ Δ₁)(p : σ ∋ u R v)(e : ρ E η) → 
              (sub<< (ren α ∘ ρ) u) E ((λ {σ'} → renval {σ = σ'} α ∘ η) << v)
E<<-ren α p e vze = p
E<<-ren α p e (vsu {σ = σ} x) = R-ren {σ = σ} α (e x)


sub<<-lem : ∀{Γ Δ σ τ} → (ρ : Sub Γ Δ)(u : Tm Δ σ)(v : Var (Γ < σ) τ) → sub<< ρ u v ≅ (sub (sub<< var u) ∘ (lift ρ)) v
sub<<-lem ρ u vze = refl
sub<<-lem ρ u (vsu v) = trans (sym (subid (ρ v)) ) (sym (subren (sub<< var u) vsu (ρ v)))


mutual
  reifyR : ∀{Γ} σ {t : Tm Γ σ}{v : Val Γ σ} → σ ∋ t R v → t ∼ embNf (reify σ v)
  reifyR ι r = r
  reifyR nat {v = nenat x} r = r
  reifyR nat {v = nze} r = r
  reifyR nat {v = nsu v} (n , t∼ , nRv) = trans∼ t∼ (congsc∼ (reifyR nat {t = n}{v = v} nRv)) 
  reifyR (σ ⇒ τ) r = trans∼ eta∼ (conglam∼ (reifyR τ (r vsu (var vze) (reflect σ (nvar vze)) (reflectR σ refl∼))))
  reifyR [ σ ] {v = neLV x} r = r
  reifyR [ σ ] {v = nilLV} r = r
  reifyR [ σ ] {v = consLV v vs} (hd , tl , t∼ , hdRv , tlRvs) = trans∼ t∼ (congcons∼ (reifyR σ hdRv) (reifyR [ σ ] {v = vs} tlRvs))

  reflectR : ∀{Γ} σ {t : Tm Γ σ}{n : Ne Γ σ} → t ∼ embNe n → σ ∋ t R (reflect σ n)
  reflectR ι p = p
  reflectR nat p = p
  reflectR (σ ⇒ τ) p ρ u v x = reflectR τ (congapp∼ (trans∼ (ren∼ refl p) (ren-embNe ρ _)) (reifyR σ x))
  reflectR [ σ ] p = p


idEE : ∀{Γ} → var E idE {Γ}
idEE {ε} ()
idEE {Γ < σ} vze = reflectR σ refl∼
idEE {Γ < σ} (vsu {σ = σ'} x) = R-ren {σ = σ'} vsu (idEE x)


natfoldR : ∀{Γ σ} → {z : Tm Γ σ}{f : Tm Γ (σ ⇒ σ)}{n : Tm Γ nat}{zv : Val Γ σ}{fv : Val Γ (σ ⇒ σ)}{nv : Val Γ nat} → 
         σ ∋ z R zv → (σ ⇒ σ) ∋ f R fv → nat ∋ n R nv → σ ∋ (rec z f n) R natfold {σ = σ} zv fv nv
natfoldR {σ = σ}{f = f}{fv = fv} {nenat x} zR fR nR              = reflectR σ (congrec∼ (reifyR σ zR) (reifyR (σ ⇒ σ) {t = f}{v = fv} fR) nR)
natfoldR {Γ}{σ}{z = z}{f = f}{n = n}{fv = fv} {nze} zR fR nR   = R∼ {Γ}{σ} zR (trans∼ (sym∼ (congreczero∼ z f)) (congrec∼ refl∼ refl∼ (sym∼ nR)))
natfoldR {Γ}{σ}{z}{f}{n}{zv}{fv}{nsu nv} zR fR (n' , n∼ , nRnv) = R∼ {Γ}{σ} (fR renId (rec z f n') (natfold {σ = σ} zv fv nv) 
         (natfoldR {nv = nv} zR fR nRnv)) 
         (trans∼ (trans∼ (congapp∼ (≅to∼ (renid f)) refl∼) (sym∼ (congrecsc∼ z f n'))) (congrec∼ refl∼ refl∼ (sym∼ n∼)))


listfoldR : ∀{Γ σ τ} → {z : Tm Γ τ}{f : Tm Γ (σ ⇒ τ ⇒ τ)}{xs : Tm Γ [ σ ]}{zv : Val Γ τ}{fv : Val Γ (σ ⇒ τ ⇒ τ)}{xsv : Val Γ [ σ ]} → 
         τ ∋ z R zv → (σ ⇒ τ ⇒ τ) ∋ f R fv → [ σ ] ∋ xs R xsv → τ ∋ (fold z f xs) R listfold {τ = τ} zv fv xsv
listfoldR {σ = σ}{τ = τ}{f = f}{fv = fv}{xsv = neLV x} zR fR xsR = reflectR τ (congfold∼ (reifyR τ zR) (reifyR (σ ⇒ τ ⇒ τ) {t = f}{v = fv} fR) xsR)
listfoldR {Γ}{σ}{τ}{z}{f}{xsv = nilLV} zR fR xsR                 = R∼ {Γ}{τ} zR (trans∼ (sym∼ (congfoldnil∼ z f)) (congfold∼ refl∼ refl∼ (sym∼ xsR)))
listfoldR {Γ}{σ}{τ}{z}{f}{xs}{zv}{fv}{consLV xv xsv'} zR fR (hd , tl , xs∼ , hdRxv , tlRxsv') = R∼ {Γ}{τ} (fR renId hd xv hdRxv renId 
      (fold z f tl) (listfold {τ = τ} zv fv xsv') (listfoldR {xsv = xsv'} zR fR tlRxsv'))
      (trans∼ (trans∼ (congapp∼ (congapp∼ (≅to∼ (trans (renid (ren renId f)) (renid f))) (≅to∼ (renid hd))) refl∼) (sym∼ (congfoldcons∼ z f hd tl)))
              (congfold∼ refl∼ refl∼ (sym∼ xs∼)))


fund-thm : ∀{Γ Δ σ} (t : Tm Γ σ) → (ρ : Sub Γ Δ) → (η : Env Γ Δ) → ρ E η → σ ∋ sub ρ t R (eval η t)
fund-thm (var x) ρ η e = e x
fund-thm (lam t) ρ η e α u v p = R∼ (fund-thm t (sub<< (ren α ∘ ρ) u) ((λ {σ'} → renval {σ = σ'} α ∘ η) << v) (E<<-ren α p e))
  (trans∼ 
    (≅to∼ (
      proof
      sub (sub<< (ren α ∘ ρ) u) t 
      ≅⟨ cong (λ (f : Sub _ _) → sub f t) (iext (λ σ' → ext (λ v' → sub<<-lem (ren α ∘ ρ) u v'))) ⟩
      sub (sub (sub<< var u) ∘ (lift (ren α ∘ ρ))) t
      ≅⟨ subcomp (sub<< var u) (lift (ren α ∘ ρ)) t ⟩
      sub (sub<< var u) (sub (lift (ren α ∘ ρ)) t)
      ≅⟨ cong (λ (x : Sub _ _) → sub (sub<< var u) (sub x t)) (iext (λ σ' → ext (λ x → sym (renwklift α ρ x)))) ⟩
      sub (sub<< var u) (sub (ren (wk α) ∘ (lift ρ)) t)
      ≅⟨ cong (sub (sub<< var u)) (sym (rensub (wk α) (lift ρ) t)) ⟩
      sub (sub<< var u) (ren (wk α) (sub (lift ρ) t))
      ∎)) 
    (sym∼ (beta∼ {t = (ren (wk α) (sub (lift ρ) t))} {u = u})))
fund-thm (app t u) ρ η e = let
  r = fund-thm t ρ η e 
  r' = fund-thm u ρ η e in 
    R∼ (r id (sub ρ u) (eval η u) r') (congapp∼ (≅to∼ (renid (sub ρ t))) refl∼)
fund-thm ze ρ η e = refl∼
fund-thm (su n) ρ η e = (sub ρ n) , (refl∼ , fund-thm n ρ η e)
fund-thm {σ = σ} (rec z f n) ρ η e = natfoldR {nv = eval η n} (fund-thm z ρ η e) (fund-thm f ρ η e) (fund-thm n ρ η e)
fund-thm nil ρ η e = refl∼
fund-thm {σ = [ σ ]} (cons h t) ρ η e = (sub ρ h) , ((sub ρ t) , (refl∼ , ((fund-thm h ρ η e) , (fund-thm t ρ η e)))) 
fund-thm (fold z f n) ρ η e = listfoldR {xsv = eval η n} (fund-thm z ρ η e) (fund-thm f ρ η e) (fund-thm n ρ η e)


soundness : ∀{Γ σ} → {t t' : Tm Γ σ} → t ∼ t' → norm t ≅ norm t'
soundness p = cong (reify _) (evalSim p refl)
  
completeness : ∀{Γ σ} → (t : Tm Γ σ) → t ∼ embNf (norm t)
completeness t = trans∼ (≅to∼ (sym (subid t))) (reifyR _ (fund-thm t var idE idEE))

third : ∀{Γ σ} → (t t' : Tm Γ σ) → norm t ≅ norm t' → t ∼ t'
third t t' p = trans∼ (completeness t) (trans∼ (subst (λ x → embNf (norm t) ∼ embNf x) p refl∼) (sym∼ (completeness t')))

