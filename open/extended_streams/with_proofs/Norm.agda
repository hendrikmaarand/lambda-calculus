{-# OPTIONS --copatterns --termination-depth=1 #-}


module Norm where

open import Syntax
open import NormalForms
open import Values
open import ReifyReflect
open import Evaluator
open import Folds
open import Utils

open import Function
open import Data.Product hiding (map)
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Data.Nat hiding (_<_)



data _∼_ : ∀{Γ}{σ} → Tm Γ σ → Tm Γ σ → Set where
  refl∼  : ∀{Γ}{σ} → {t : Tm Γ σ} → t ∼ t
  sym∼   : ∀{Γ}{σ} → {t u : Tm Γ σ} → t ∼ u → u ∼ t
  trans∼ : ∀{Γ}{σ} → {t u v : Tm Γ σ} → t ∼ u → u ∼ v → t ∼ v
  beta∼  : ∀{Γ σ τ} → {t : Tm (Γ < σ) τ} → {u : Tm Γ σ} → app (lam t) u ∼ sub (sub<< var u) t
  eta∼   : ∀{Γ σ τ} → {t : Tm Γ (σ ⇒ τ)} → t ∼ lam (app (ren vsu t) (var vze))
  congapp∼  : ∀{Γ σ τ} → {t t' : Tm Γ (σ ⇒ τ)} → {u u' : Tm Γ σ} → t ∼ t' → u ∼ u' → app t u ∼ app t' u'
  conglam∼  : ∀{Γ σ τ} → {t t' : Tm (Γ < σ) τ} → t ∼ t' → lam t ∼ lam t'
  congsu∼   : ∀{Γ} → {t t' : Tm Γ nat} → t ∼ t' → su t ∼ su t'
  congrec∼  : ∀{Γ σ} → {z z' : Tm Γ σ}{f f' : Tm Γ (σ ⇒ σ)}{n n' : Tm Γ nat} → z ∼ z' → f ∼ f' → n ∼ n' → rec z f n ∼ rec z' f' n'
  congrecze∼ : ∀{Γ σ} → (z : Tm Γ σ)(f : Tm Γ (σ ⇒ σ)) → rec z f ze ∼ z
  congrecsu∼  : ∀{Γ σ} → (z : Tm Γ σ)(f : Tm Γ (σ ⇒ σ))(n : Tm Γ nat) → rec z f (su n) ∼ app f (rec z f n)
  congpair∼   : ∀{Γ σ τ} → {a a' : Tm Γ σ}{b b' : Tm Γ τ} → a ∼ a' → b ∼ b' → (a ,, b) ∼ (a' ,, b')
  paireta∼    : ∀{Γ σ τ} → {t : Tm Γ (σ ∧ τ)} → t ∼ (fst t ,, snd t)
  pairfst∼    : ∀{Γ σ τ} → {a : Tm Γ σ}{b : Tm Γ τ} → a ∼ fst (a ,, b)
  pairsnd∼    : ∀{Γ σ τ} → {a : Tm Γ σ}{b : Tm Γ τ} → b ∼ snd (a ,, b)
  congfst∼    : ∀{Γ σ τ} → {a a' : Tm Γ (σ ∧ τ)} → a ∼ a' → fst a ∼ fst a'
  congsnd∼    : ∀{Γ σ τ} → {a a' : Tm Γ (σ ∧ τ)} → a ∼ a' → snd a ∼ snd a'
  congtup∼    : ∀{Γ σ} → {f g : ℕ → Tm Γ σ} → (∀ n → f n ∼ g n) → tup f ∼ tup g
  congproj∼   : ∀{Γ σ} → {n : ℕ} → {f g : Tm Γ < σ >} → f ∼ g → proj n f ∼ proj n g
  streambeta∼ : ∀{Γ σ} → {n : ℕ} → {f : ℕ → Tm Γ σ} → proj n (tup f) ∼ f n
  streameta∼  : ∀{Γ σ} → {s : Tm Γ < σ >} → s ∼ tup (λ n → proj n s) 


idE : ∀{Γ} → Env Γ Γ
idE x = reflect _ (nvar x)

norm : ∀{Γ σ} → Tm Γ σ → Nf Γ σ
norm t = reify _ (eval idE t)


renvaleval : ∀{Γ Δ E σ} → (γ : Env Δ Γ) → (ρ : Ren Γ E) → (t : Tm Δ σ) → eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) t ≅ renval {σ = σ} ρ (eval γ t)
renvaleval γ ρ (var x) = refl
renvaleval {σ = σ ⇒ τ} γ ρ (lam t) = Σeq 
  ((iext λ Δ' → ext λ (α : Ren _ _) → ext λ v → cong (λ (f : Env _ _) → eval (f << v) t) (iext λ σ' → ext λ x → renvalcomp {σ = σ'} α ρ (γ x))))
  refl
  ((iext λ Δ₁ → iext λ Δ₂ → ext λ (ρ₁ : Ren _ _) → ext λ (ρ₂ : Ren _ _) → ext λ v → fixedtypesleft 
         (cong (λ (f : Env _ _) → renval {σ = τ} ρ₂ (eval (f << v) t)) (iext λ σ' → ext λ x → renvalcomp {σ = σ'} ρ₁ ρ (γ x)))))
renvaleval γ ρ (app {σ}{τ} t u) =  proof
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
renvaleval γ ρ (a ,, b) = cong₂ _,_ (renvaleval γ ρ a) (renvaleval γ ρ b)
renvaleval γ ρ (fst t) = cong proj₁ (renvaleval γ ρ t)
renvaleval γ ρ (snd t) = cong proj₂ (renvaleval γ ρ t)
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
renvaleval {σ = σ} γ ρ (proj n s) = proof
  lookup (eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) s) n
  ≅⟨ cong (λ s' → lookup s' n) (renvaleval γ ρ s) ⟩
  lookup (renval {σ = < σ >} ρ (eval γ s)) n
  ≅⟨  sym (renvalIso1 ρ (eval γ s) n)  ⟩
  renval {σ = σ} ρ (lookup (eval γ s) n)
  ∎
renvaleval {σ = < σ >} γ ρ (tup f) = proof
  eval (λ {σ'} → renval {σ = σ'} ρ ∘ γ) (tup f) 
  ≅⟨ cong tabulate (ext (λ n → renvaleval γ ρ (f n))) ⟩
  tabulate (λ n → renval {σ = σ} ρ (eval γ (f n)))
  ≅⟨ sym (SEq (renvalIso2 (λ n → eval γ (f n)) ρ)) ⟩
  renval {σ = < σ >} ρ (eval γ (tup f))
  ∎



evalsub<< : ∀{Γ Δ σ τ} → (γ : Env Γ Δ) → (u : Tm Γ σ) → (v : Var (Γ < σ) τ) → (γ << eval γ u) v ≅ (eval γ ∘ (sub<< var u)) v
evalsub<< γ u vze = refl
evalsub<< γ u (vsu v) = refl


evalSim : ∀{Γ Δ σ} → {t t' : Tm Γ σ} → {γ γ' : Env Γ Δ} → t ∼ t' → _≅_ {A = Env _ _} γ {B = Env _ _} γ' → eval γ t ≅ eval γ' t'
evalSim (refl∼ {t = t}) q = cong (λ (f : Env _ _) → eval f t) q 
evalSim (sym∼ p) q = sym (evalSim p (sym q))
evalSim (trans∼ p p₁) q = trans (evalSim p q) (evalSim p₁ refl)
evalSim {σ = σ} {γ = γ}{γ' = γ'} (beta∼ {t = t} {u = u}) q = proof
  eval ((λ {σ'} → renval {σ = σ'} renId ∘ γ) << eval γ u) t
  ≅⟨ cong (λ (f : Env _ _) → eval (f << (eval γ u)) t) (iext λ σ' → ext λ x → renvalid {σ = σ'} (γ x)) ⟩
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
evalSim (congsu∼ p) q = cong nsu (evalSim p q)
evalSim (congrec∼ z f n) q = cong₃ natfold (evalSim z q) (evalSim f q) (evalSim n q)
evalSim (congrecze∼ z f) refl = refl
evalSim {σ = σ}{γ = γ} (congrecsu∼ z f n) refl = refl
evalSim (congpair∼ a b) q = cong₂ _,_ (evalSim a q) (evalSim b q)
evalSim {γ = γ} (paireta∼ {t = t}) refl = refl
evalSim pairfst∼ refl = refl
evalSim pairsnd∼ refl = refl
evalSim (congfst∼ p) q = cong proj₁ (evalSim p q)
evalSim (congsnd∼ p) q = cong proj₂ (evalSim p q)
evalSim (congtup∼ f) q = cong tabulate (ext (λ n → evalSim (f n) q))
evalSim (congproj∼ {n = n} p) q = cong (λ h → lookup h n) (evalSim p q)
evalSim {γ = γ}{γ' = γ'} (streambeta∼ {n = n}{f = f}) q = proof
  lookup (tabulate (λ n₁ → eval γ (f n₁))) n
  ≅⟨ lookuptab (eval γ ∘ f) n ⟩
  eval γ (f n)
  ≅⟨ cong (λ (g : Env _ _) → eval g (f n)) q ⟩
  eval γ' (f n)
  ∎
evalSim {γ = γ}{γ' = γ'} (streameta∼ {s = s}) q = proof
   eval γ s 
   ≅⟨ cong (λ (f : Env _ _) → eval f s) q ⟩
   eval γ' s
   ≅⟨ sym (SEq (tablookup (eval γ' s))) ⟩ 
   tabulate (λ n → lookup (eval γ' s) n)
   ∎

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
ren∼ p (congsu∼ n) = congsu∼ (ren∼ p n)
ren∼ p (congrec∼ z f n) = congrec∼ (ren∼ p z) (ren∼ p f) (ren∼ p n)
ren∼ {ρ = ρ} p (congrecze∼ z f) = trans∼ (congrecze∼ (ren ρ z) (ren ρ f)) (ren∼ p refl∼)
ren∼ {ρ = ρ} refl (congrecsu∼ z f n) = congrecsu∼ (ren ρ z) (ren ρ f) (ren ρ n)
ren∼ p (congpair∼ a b) = congpair∼ (ren∼ p a) (ren∼ p b)
ren∼ {ρ = ρ} refl (paireta∼ {t = t}) = paireta∼ {t = ren ρ t}
ren∼ refl (pairfst∼ {a = a}{b = b}) = pairfst∼ {a = ren _ a} 
ren∼ refl (pairsnd∼ {a = a}{b = b}) = pairsnd∼ {b = ren _ b} 
ren∼ p (congfst∼ q) = congfst∼ (ren∼ p q)
ren∼ p (congsnd∼ q) = congsnd∼ (ren∼ p q)
ren∼ p (congtup∼ h) = congtup∼ (λ n → ren∼ p (h n))
ren∼ p (congproj∼ {n = n} q)= congproj∼ (ren∼ p q)
ren∼ {ρ = ρ} p (streambeta∼ {n = n}{f = f}) = trans∼ (streambeta∼ {f = ren ρ ∘ f}) (ren∼ p refl∼)
ren∼ {ρ = ρ}{ρ' = .ρ} refl (streameta∼ {s = s}) = streameta∼ {s = ren ρ s}

--(congtup∼ (λ n → subst (λ (X : Ren _ _) → proj n (ren ρ s) ∼ proj n (ren X s)) p refl∼))

_∋_R_ : ∀{Γ} σ → (t : Tm Γ σ) → (v : Val Γ σ) → Set
ι ∋ t R v = t ∼ embNf (reify ι v)
nat ∋ t R ne x = t ∼ embNe x
nat ∋ t R nze = t ∼ ze
nat ∋ t R nsu v = Σ (Tm _ nat) (λ t' → t ∼ su t' × nat ∋ t' R v )
(σ ⇒ τ) ∋ t R f = ∀{Δ} → (ρ : Ren _ Δ)(u : Tm Δ σ)(v : Val Δ σ) → σ ∋ u R v → τ ∋ app (ren ρ t) u R proj₁ f ρ v
(σ ∧ τ) ∋ t R v = Σ (σ ∋ fst t R proj₁ v) (λ _ → τ ∋ snd t R proj₂ v)
< σ > ∋ t R v = ∀ n → σ ∋ proj n t R lookup v n 


R∼ : ∀{Γ σ} → {t t' : Tm Γ σ} → {v : Val Γ σ} → σ ∋ t R v → t ∼ t' → σ ∋ t' R v
R∼ {σ = ι} r p = trans∼ (sym∼ p) r
R∼ {σ = σ ⇒ τ} r p =  λ ρ u v r' → let a = r ρ u v r' in R∼ a (congapp∼ (ren∼ refl p) refl∼)
R∼ {σ = nat} {v = ne x} r p = trans∼ (sym∼ p) r
R∼ {σ = nat} {v = nze} r p = trans∼ (sym∼ p) r
R∼ {σ = nat}{t = t}{t' = t'} {v = nsu n} (t'' , t'∼ , t''Rn) p = t'' , ((trans∼ (sym∼ p) t'∼) , t''Rn)
R∼ {σ = σ ∧ τ} {v = v} r p = R∼ (proj₁ r) (congfst∼ p) , R∼ (proj₂ r) (congsnd∼ p)
R∼ {σ = < σ >} r p n = R∼ (r n) (congproj∼ p)

R'∼ : ∀{Γ σ} → {t : Tm Γ σ} → {v v' : Val Γ σ} → σ ∋ t R v → v ≅ v' → σ ∋ t R v'
R'∼ r refl = r



mutual
  ren-embNf : ∀{Γ Δ σ} → (α : Ren Γ Δ)(n : Nf Γ σ) → ren α (embNf n) ∼ embNf (renNf α n)
  ren-embNf α (nlam n) = conglam∼ (ren-embNf (wk α) n)
  ren-embNf α (ne x) = ren-embNe α x
  ren-embNf α (a ,-, b) = congpair∼ (ren-embNf α a) (ren-embNf α b)
  ren-embNf α nze = refl∼
  ren-embNf α (nsu n) = congsu∼ (ren-embNf α n)
  ren-embNf α (ntup f) = congtup∼ (λ n → ren-embNf α (f n))

  ren-embNe : ∀{Γ Δ σ} → (α : Ren Γ Δ)(n : Ne Γ σ) → ren α (embNe n) ∼ embNe (renNe α n)
  ren-embNe α (nvar x) = refl∼
  ren-embNe α (napp t u) = congapp∼ (ren-embNe α t) (ren-embNf α u)
  ren-embNe α (nfst x) = congfst∼ (ren-embNe α x)
  ren-embNe α (nsnd x) = congsnd∼ (ren-embNe α x)
  ren-embNe α (nrec z f n) = congrec∼ (ren-embNf α z) (ren-embNf α f) (ren-embNe α n)
  ren-embNe α (nproj n s) = congproj∼ (ren-embNe α s)


R-ren : ∀{Γ Δ σ}{t : Tm Γ σ}{v : Val Γ σ} → (α : Ren Γ Δ) → σ ∋ t R v → σ ∋ ren α t R renval {σ = σ} α v
R-ren {σ = ι}{v = v} α r = trans∼ (ren∼ refl r) (ren-embNf α v)
R-ren {σ = σ ⇒ τ} α r ρ u v₁ x = R∼ {σ = τ} (r (ρ ∘ α) u v₁ x) (congapp∼ (≅to∼ (rencomp ρ α _)) refl∼)
R-ren {σ = nat} {v = ne x} α r = trans∼ (ren∼ refl r) (ren-embNe α x)
R-ren {σ = nat} {v = nze} α r = ren∼ refl r
R-ren {σ = nat} {v = nsu v} α (n , t∼ , nRv) = (ren α n) , ((ren∼ refl t∼) , R-ren {t = n}{v = v} α nRv)
R-ren {σ = σ ∧ τ}{v = v} α r = (R-ren {σ = σ} α (proj₁ r)) , (R-ren {σ = τ} α (proj₂ r))
R-ren {σ = < σ >}{t = s}{v = v} α r = λ n → R'∼ {t = ren α (proj n s)} (R-ren {σ = σ} α (r n)) (renvalIso1 α v n)

_E_ : ∀{Γ Δ} → (ρ : Sub Γ Δ) → (η : Env Γ Δ) → Set
ρ E η = ∀{σ} → (x : Var _ σ) → σ ∋ ρ x R η x

E-ren : ∀{Γ Δ  Δ₁}{ρ : Sub Γ Δ}{η : Env Γ Δ} → (α : Ren Δ Δ₁) → ρ E η → (ren α ∘ ρ) E (λ {σ'} → renval {σ = σ'} α ∘ η)
E-ren {Γ = Γ} α e = λ {σ'} x → R-ren {σ = σ'} α (e x)


E<< : ∀{Γ Δ σ} → {ρ : Sub Γ Δ}{η : Env Γ Δ}{v : Val Δ σ}{u : Tm Δ σ} → (p : σ ∋ u R v)(e : ρ E η) → (sub<< ρ u) E (η << v)
E<< p e vze = p
E<< p e (vsu x) = e x

E<<-ren : ∀{Γ Δ Δ₁ σ} → {ρ : Sub Γ Δ}{η : Env Γ Δ}{v : Val Δ₁ σ}{u : Tm Δ₁ σ} → (α : Ren Δ Δ₁)(p : σ ∋ u R v)(e : ρ E η) → 
                        (sub<< (ren α ∘ ρ) u) E ((λ {σ'} → renval {σ = σ'} α ∘ η) << v)
E<<-ren α p e vze = p
E<<-ren α p e (vsu {σ = σ'} x) = R-ren {σ = σ'} α (e x)


sub<<-lem : ∀{Γ Δ σ τ} → (ρ : Sub Γ Δ)(u : Tm Δ σ)(v : Var (Γ < σ) τ) → sub<< ρ u v ≅ (sub (sub<< var u) ∘ (lift ρ)) v
sub<<-lem ρ u vze = refl
sub<<-lem ρ u (vsu v) = trans (sym (subid (ρ v)) ) (sym (subren (sub<< var u) vsu (ρ v))) 


mutual
  reifyR : ∀{Γ} σ {t : Tm Γ σ}{v : Val Γ σ} → σ ∋ t R v → t ∼ embNf (reify σ v)
  reifyR ι r = r
  reifyR (σ ⇒ τ){t = t}{v = v} r =  trans∼ eta∼ (conglam∼ (reifyR τ (r vsu (var vze) (reflect σ (nvar vze)) (reflectR σ refl∼))))
  reifyR nat {v = ne x} r = r
  reifyR nat {v = nze} r = r
  reifyR nat {v = nsu v} (n , t∼ , nRv) = trans∼ t∼ (congsu∼ (reifyR nat {t = n}{v = v} nRv)) 
  reifyR (σ ∧ τ) {t = t}{v = v} r = trans∼ (paireta∼ {t = t}) (congpair∼ (reifyR σ (proj₁ r)) (reifyR τ (proj₂ r)))
  reifyR < σ > r = trans∼ streameta∼ (congtup∼ (λ n → reifyR σ (r n)))


  reflectR : ∀{Γ} σ {t : Tm Γ σ}{n : Ne Γ σ} → t ∼ embNe n → σ ∋ t R (reflect σ n)
  reflectR ι p = p
  reflectR (σ ⇒ τ) {t = t} p ρ u v p' = reflectR τ (congapp∼ (trans∼ (ren∼ refl p) (ren-embNe ρ _)) (reifyR σ p'))
  reflectR nat p = p
  reflectR (σ ∧ τ) {t = t}{n = n} p = reflectR σ (congfst∼ p) , reflectR τ (congsnd∼ p)
  reflectR < σ > {t = t} p n = R'∼ {t = proj n t} (reflectR σ (congproj∼ p)) (sym (lookuptab (λ a → reflect σ (nproj a _)) n))


natfoldR : ∀{Γ σ} → {z : Tm Γ σ}{f : Tm Γ (σ ⇒ σ)}{n : Tm Γ nat}{zv : Val Γ σ}{fv : Val Γ (σ ⇒ σ)}{nv : Val Γ nat} → 
         σ ∋ z R zv → (σ ⇒ σ) ∋ f R fv → nat ∋ n R nv → σ ∋ (rec z f n) R natfold {σ = σ} zv fv nv
natfoldR {σ = σ}{f = f}{fv = fv} {ne x} zR fR nR              = reflectR σ (congrec∼ (reifyR σ zR) (reifyR (σ ⇒ σ) {t = f}{v = fv} fR) nR)
natfoldR {Γ}{σ}{z = z}{f = f}{n = n}{fv = fv} {nze} zR fR nR   = R∼ {Γ}{σ} zR (trans∼ (sym∼ (congrecze∼ z f)) (congrec∼ refl∼ refl∼ (sym∼ nR)))
natfoldR {Γ}{σ}{z}{f}{n}{zv}{fv}{nsu nv} zR fR (n' , n∼ , nRnv) = R∼ {Γ}{σ} (fR renId (rec z f n') (natfold {σ = σ} zv fv nv) 
         (natfoldR {nv = nv} zR fR nRnv)) 
         (trans∼ (trans∼ (congapp∼ (≅to∼ (renid f)) refl∼) (sym∼ (congrecsu∼ z f n'))) (congrec∼ refl∼ refl∼ (sym∼ n∼)))


fund-thm : ∀{Γ Δ σ} (t : Tm Γ σ) → (ρ : Sub Γ Δ) → (η : Env Γ Δ) → ρ E η → σ ∋ sub ρ t R (eval η t)
fund-thm (var x) ρ η e = e x
fund-thm (lam t) ρ η e = λ α u v p → R∼ (fund-thm t (sub<< (ren α ∘ ρ) u) ((λ {σ'} → renval {σ = σ'} α ∘ η) << v) (E<<-ren α p e))
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
fund-thm (a ,, b) ρ η e = R∼ {t = sub ρ a} (fund-thm a ρ η e) (pairfst∼ {a = sub ρ a}) , R∼ {t = sub ρ b} (fund-thm b ρ η e) (pairsnd∼ {b = sub ρ b})
fund-thm (fst t) ρ η e = proj₁ (fund-thm t ρ η e)
fund-thm (snd t) ρ η e = proj₂ (fund-thm t ρ η e)
fund-thm ze ρ η e = refl∼
fund-thm (su n) ρ η e = (sub ρ n) , (refl∼ , (fund-thm n ρ η e))
fund-thm (rec z f n) ρ η e = natfoldR {nv = eval η n} (fund-thm z ρ η e) (fund-thm f ρ η e) (fund-thm n ρ η e)
fund-thm (proj n s) ρ η e = fund-thm s ρ η e n
fund-thm (tup f) ρ η e n = R∼ {t = sub ρ (f n)} (R'∼ {t = sub ρ (f n)} (fund-thm (f n) ρ η e) (sym (lookuptab (eval η ∘ f) n))) (sym∼ streambeta∼)


idEE : ∀{Γ} → var E idE {Γ}
idEE {ε} ()
idEE {Γ < σ} vze = reflectR σ refl∼
idEE {Γ < σ} (vsu {σ = τ} x) = R'∼ {t = var (vsu x)} (R-ren {σ = τ} vsu (idEE x)) (renvalReflect {σ = τ} vsu (nvar x))


soundness : ∀{Γ σ} → {t t' : Tm Γ σ} → t ∼ t' → norm t ≅ norm t'
soundness p = cong (reify _) (evalSim p refl)

completeness : ∀{Γ σ} → (t : Tm Γ σ) → t ∼ embNf (norm t)
completeness t = trans∼ (≅to∼ (sym (subid t))) (reifyR _ (fund-thm t var idE idEE))

third : ∀{Γ σ} → (t t' : Tm Γ σ) → norm t ≅ norm t' → t ∼ t'
third t t' p = trans∼ (completeness t) (trans∼ (subst (λ x → embNf (norm t) ∼ embNf x) p refl∼) (sym∼ (completeness t')))
