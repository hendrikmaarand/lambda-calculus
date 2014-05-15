module Norm where

open import Syntax
open import Evaluator

open import Data.Product
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)


data _∼_ {Γ : Con} : ∀{σ : Ty} → Tm Γ σ → Tm Γ σ → Set where
  refl∼  : ∀{σ} → {t : Tm Γ σ} → t ∼ t
  sym∼   : ∀{σ} → {t u : Tm Γ σ} → t ∼ u → u ∼ t
  trans∼ : ∀{σ} → {t u v : Tm Γ σ} → t ∼ u → u ∼ v → t ∼ v
  beta∼  : ∀{σ τ} → {t : Tm (Γ < σ) τ} → {u : Tm Γ σ} → app (lam t) u ∼ sub (sub<< var u) t
  eta∼   : ∀{σ τ} → {t : Tm Γ (σ ⇒ τ)} → t ∼ lam (app (ren vsu t) (var vze))
  congapp∼ : ∀{σ τ} → {t t' : Tm Γ (σ ⇒ τ)} → {u u' : Tm Γ σ} → t ∼ t' → u ∼ u' → app t u ∼ app t' u'
  conglam∼ : ∀{σ τ} → {t t' : Tm (Γ < σ) τ} → t ∼ t' → lam t ∼ lam t'


idE : ∀{Γ} → Env Γ Γ
idE x = reflect _ (nvar x)


idEvsu<< : ∀{Γ σ τ} → (x : Var (Γ < σ) τ) → idE x ≅ ((renval vsu ∘ idE) << reflect σ (nvar vze)) x
idEvsu<< vze = refl
idEvsu<< (vsu x) = sym (renvalReflect vsu (nvar x))


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
evalsub<< γ u vze = refl
evalsub<< γ u (vsu v) = refl


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
         lem : ∀ Δ (ρ : Ren _ Δ) v → proj₁ (eval γ t) ρ v ≅ proj₁ (eval ((λ {σ} x → renval ρ (γ' x)) << v) (ren (λ {σ} → vsu) t)) (λ {σ} x → x) v
         lem Δ ρ v = trans (trans (cong (λ (f : Env _ _) → proj₁ (eval f t) ρ v) q) (sym (cong (λ f → proj₁ f id v) (renvaleval γ' ρ t)))) (cong (λ f → proj₁ f id v) (reneval vsu ((λ {σ} x → renval ρ (γ' x)) << v) t))
evalSim (congapp∼ p p₁) (q) = cong₂ (λ f g → proj₁ f renId g) (evalSim p q) (evalSim p₁ q)
evalSim (conglam∼ {t = t}{t' = t'} p) q = Σeq 
  (iext λ Δ → ext λ (α : Ren _ _) → ext λ v → evalSim p (iext λ σ₁ → cong (λ (f : Env _ _) → (renval α ∘ f) << v) q)) 
  refl 
  (iext λ Δ → iext λ Δ' → ext λ (ρ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v → 
      fixedtypesleft (cong (renval ρ') (evalSim p (iext λ _ → ext λ x → cong (λ f → ((λ {_} x → renval {σ = _} ρ (f x)) << v) x) q))))


correctnessA : ∀{Γ σ} → {t t' : Tm Γ σ} → t ∼ t' → norm t ≅ norm t'
correctnessA p = cong (reify _) (evalSim p refl)

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


_∋_R_ : ∀{Γ} σ → (t : Tm Γ σ) → (v : Val Γ σ) → Set
ι ∋ t R v = t ∼ embNf (reify ι v)
(σ ⇒ τ) ∋ t R f = ∀{Δ} → (ρ : Ren _ Δ)(u : Tm Δ σ)(v : Val Δ σ) → σ ∋ u R v → τ ∋ app (ren ρ t) u R proj₁ f ρ v



R∼ : ∀{Γ σ} → {t t' : Tm Γ σ} → {v : Val Γ σ} → σ ∋ t R v → t ∼ t' → σ ∋ t' R v
R∼ {Γ} {ι} r p = trans∼ (sym∼ p) r
R∼ {Γ} {σ ⇒ τ} r p =  λ ρ u v r' → let a = r ρ u v r' in R∼ a (congapp∼ (ren∼ refl p) refl∼)

R'∼ : ∀{Γ σ} → {t : Tm Γ σ} → {v v' : Val Γ σ} → σ ∋ t R v → v ≅ v' → σ ∋ t R v'
R'∼ r refl = r

mutual
  ren-embNf : ∀{Γ Δ σ} → (α : Ren Γ Δ)(n : Nf Γ σ) → ren α (embNf n) ∼ embNf (renNf α n)
  ren-embNf α (nlam n) = conglam∼ (ren-embNf (wk α) n)
  ren-embNf α (ne x) = ren-embNe α x

  ren-embNe : ∀{Γ Δ σ} → (α : Ren Γ Δ)(n : Ne Γ σ) → ren α (embNe n) ∼ embNe (renNe α n)
  ren-embNe α (nvar x) = refl∼
  ren-embNe α (napp t u) = congapp∼ (ren-embNe α t) (ren-embNf α u)

R-ren : ∀{Γ Δ σ}{t : Tm Γ σ}{v : Val Γ σ} → (α : Ren Γ Δ) → σ ∋ t R v → σ ∋ ren α t R renval α v
R-ren {σ = ι}{v = v} α r = trans∼ (ren∼ refl r) (ren-embNf α v)
R-ren {σ = σ ⇒ τ} α r ρ u v₁ x = R∼ (r (ρ ∘ α) u v₁ x) (congapp∼ (≅to∼ (rencomp ρ α _)) refl∼)


_E_ : ∀{Γ Δ} → (ρ : Sub Γ Δ) → (η : Env Γ Δ) → Set
ρ E η = ∀{σ} → (x : Var _ σ) → σ ∋ ρ x R η x

E-ren : ∀{Γ Δ  Δ₁}{ρ : Sub Γ Δ}{η : Env Γ Δ} → (α : Ren Δ Δ₁) → ρ E η → (ren α ∘ ρ) E (renval α ∘ η)
E-ren α e x = R-ren α (e x)

E<< : ∀{Γ Δ σ} → {ρ : Sub Γ Δ}{η : Env Γ Δ}{v : Val Δ σ}{u : Tm Δ σ} → (p : σ ∋ u R v)(e : ρ E η) → (sub<< ρ u) E (η << v)
E<< p e vze = p
E<< p e (vsu x) = e x

E<<-ren : ∀{Γ Δ Δ₁ σ} → {ρ : Sub Γ Δ}{η : Env Γ Δ}{v : Val Δ₁ σ}{u : Tm Δ₁ σ} → (α : Ren Δ Δ₁)(p : σ ∋ u R v)(e : ρ E η) → (sub<< (ren α ∘ ρ) u) E ((renval α ∘ η) << v)
E<<-ren α p e vze = p
E<<-ren α p e (vsu x) = R-ren α (e x)


sub<<-lem : ∀{Γ Δ σ τ} → (ρ : Sub Γ Δ)(u : Tm Δ σ)(v : Var (Γ < σ) τ) → sub<< ρ u v ≅ (sub (sub<< var u) ∘ (lift ρ)) v
sub<<-lem ρ u vze = refl
sub<<-lem ρ u (vsu v) = trans (sym (subid (ρ v))) (sym (subren (sub<< var u) vsu (ρ v))) 


fund-thm : ∀{Γ Δ σ} (t : Tm Γ σ) → (ρ : Sub Γ Δ) → (η : Env Γ Δ) → ρ E η → σ ∋ sub ρ t R (eval η t)
fund-thm (var x) ρ η e = e x
fund-thm (lam t) ρ η e = λ α u v p → R∼ (fund-thm t (sub<< (ren α ∘ ρ) u) ((renval α ∘ η) << v) (E<<-ren α p e))
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


mutual
  reifyR : ∀{Γ} σ {t : Tm Γ σ}{v : Val Γ σ} → σ ∋ t R v → t ∼ embNf (reify σ v)
  reifyR ι r = r
  reifyR (σ ⇒ τ){t = t}{v = v} r =  trans∼ eta∼ (conglam∼ (reifyR τ (r vsu (var vze) (reflect σ (nvar vze)) (reflectR σ refl∼))))

  reflectR : ∀{Γ} σ {t : Tm Γ σ}{n : Ne Γ σ} → t ∼ embNe n → σ ∋ t R (reflect σ n)
  reflectR ι p = p
  reflectR (σ ⇒ τ) {t = t} p ρ u v p' = reflectR τ (congapp∼ (trans∼ (ren∼ refl p) (ren-embNe ρ _)) (reifyR σ p'))


idEE : ∀{Γ} → var E idE {Γ}
idEE {ε} ()
idEE {Γ < σ} vze = reflectR σ refl∼
idEE {Γ < σ} (vsu x) = R'∼ (R-ren vsu (idEE x)) (renvalReflect vsu (nvar x))


  
completeness-lem : ∀{Γ σ} → (t : Tm Γ σ) → t ∼ embNf (norm t)
completeness-lem t = trans∼ (≅to∼ (sym (subid t))) (reifyR _ (fund-thm t var idE idEE))

correctnessB : ∀{Γ σ} → (t t' : Tm Γ σ) → norm t ≅ norm t' → t ∼ t'
correctnessB t t' p = trans∼ (completeness-lem t) (trans∼ (subst (λ x → embNf (norm t) ∼ embNf x) p refl∼) (sym∼ (completeness-lem t')))


mutual
  stabilityNf : ∀{Γ σ} (n : Nf Γ σ) → n ≅ norm (embNf n)
  stabilityNf {σ = σ ⇒ τ} (nlam n) = cong nlam (proof
    n 
    ≅⟨ stabilityNf n ⟩
    reify τ (eval idE (embNf n))
    ≅⟨ cong (λ (f : Env _ _) → reify τ (eval f (embNf n))) (iext (λ σ' → ext (λ x → idEvsu<< x))) ⟩
    reify τ (eval ((renval vsu ∘ idE) << reflect σ (nvar vze)) (embNf n))
    ∎)
  stabilityNf (ne n) = sym (stabilityNe n)

  stabilityNe : ∀{Γ σ} (n : Ne Γ σ) → eval idE (embNe n) ≅ (reflect _ n)
  stabilityNe (nvar x) = refl
  stabilityNe (napp n x) = trans
                            (fcong (fcong (ifcong (cong proj₁ (stabilityNe n)) _) id)
                             (eval idE (embNf x)))
                            (cong (reflect _) (cong₂ napp (renNeId n) (sym (stabilityNf x))))
