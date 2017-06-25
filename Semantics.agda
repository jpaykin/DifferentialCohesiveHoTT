import Simple as Syn
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Fin using (Fin; zero; suc)
open import Data.Product
open import Data.Unit
open import Data.Vec using (Vec; foldr; lookup; map)
module Semantics where

record THSp : Set₁ where
  constructor mkTHSp
  field
    {r i p} : Set
    inf : r → i
    pc : i → p

record Sp : Set₁ where
  field
    {r p} : Set
    pc : r → p

record _⇒_ (X Y : THSp) : Set where
  constructor mk⇒
  field
    r : THSp.r X → THSp.r Y
    i : THSp.i X → THSp.i Y
    p : THSp.p X → THSp.p Y
    comm-ri : ⊤ -- ∀ xᵣ → THSp.inf Y (r xᵣ) ≡ i (THSp.inf X xᵣ)
    comm-rp : ⊤ -- ∀ xᵢ → THSp.pc Y (i xᵢ) ≡ p (THSp.pc X xᵢ)

r : THSp → Set
r X = THSp.r X

i : THSp → Set
i X = THSp.i X

p : THSp → Set
p X = THSp.p X

inf : ∀ X → r X → i X
inf X = THSp.inf X

pc : ∀ X → i X → p X
pc X = THSp.pc X

r→p : ∀ {X} → r X → p X
r→p {X} xᵣ = pc X (inf X xᵣ)

-----------------
-- Example Spaces

⊤sp : THSp
⊤sp = mkTHSp {r = ⊤}{i = ⊤}{p = ⊤} (λ _ → tt) (λ _ → tt)

tru : ⊤ → Bool
tru tt = true

disk : THSp
disk = mkTHSp tru (λ _ → tt)

ℜ : THSp → THSp
ℜ X = mkTHSp {r = r X}{i = r X}{p = p X} (λ z → z) (r→p {X = X})

ℑ : THSp → THSp
ℑ X = mkTHSp  {r = r X}{i = p X}{p = p X} (r→p {X = X}) (λ z → z)

& : THSp → THSp
& X = mkTHSp {r = r X}{i = i X}{p = i X} (inf X) (λ z → z)

∫ : THSp → THSp
∫ X = mkTHSp {r = p X}{i = p X}{p = p X} (λ z → z) (λ z → z)

♭ : THSp → THSp
♭ X = mkTHSp {r = r X}{i = r X}{p = r X} (λ z → z) (λ z → z)

♯ : THSp → THSp
♯ X = mkTHSp {r = r X}{i = ⊤}{p = ⊤} (λ _ → tt) (λ _ → tt)

⟦_⟧ : ∀ {Base} → Syn.Type Base → (Base → THSp) → THSp
⟦ Syn.∫ A ⟧ ρ = ∫ (⟦ A ⟧ ρ)
⟦ Syn.♭ A ⟧ ρ = ♭(⟦ A ⟧ ρ)
⟦ Syn.♯ A ⟧ ρ = ♯ (⟦ A ⟧ ρ)
⟦ Syn.ℜ A ⟧ ρ = ℜ (⟦ A ⟧ ρ)
⟦ Syn.ℑ A ⟧ ρ = ℑ (⟦ A ⟧ ρ)
⟦ Syn.& A ⟧ ρ = & (⟦ A ⟧ ρ)
⟦ Syn.base X ⟧ ρ = ρ X

infixr 2 _⊗_

_⊗_ : THSp → THSp → THSp
X ⊗ Y = mkTHSp {r = r X × r Y}{i = i X × i Y}{p = p X × p Y} (λ x → (inf X (proj₁ x)) , inf Y (proj₂ x)) (λ x → (pc X (proj₁ x)) , (pc Y (proj₂ x)))


⨂ : ∀ {n} →  Vec THSp n → THSp
⨂ v = foldr (λ x → THSp) (λ X Y → X ⊗ Y) ⊤sp v

sem-prod : ∀ {n}{Base} → Vec (Syn.Type Base) n → (Base → THSp) → THSp
sem-prod v ρ = ⨂ (Data.Vec.map (λ A → ⟦ A ⟧ ρ) v)

⟅_⟆ : ∀ {Base} → Syn.Ctx Base → (Base → THSp) → THSp
⟅_⟆ {Base} (Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]) ρ = sem-prod Γ ρ ⊗ sem-prod Δ ρ ⊗ sem-prod Θ ρ ⊗ sem-prod Λ ρ ⊗ sem-prod Ξ ρ

π1 : ∀ {A B C D E : Set} → A × B × C × D × E → A
π1 (proj₃ , proj₄) = proj₃

πΓ : ∀ {Base}{c}{ρ : Base → THSp} → ⟅ c ⟆ ρ ⇒ sem-prod (Syn.Ctx.Γ c) ρ
πΓ {Base} {Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {ρ} = mk⇒ π1 π1 π1 tt tt

⨂lookup : ∀ {n} → (x : Fin n) → ∀ v → ⨂ v ⇒ lookup x v
⨂lookup x = {!!}

comp⇒ : ∀ {X Y Z} → (X ⇒ Y) → (Y ⇒ Z) → X ⇒ Z
comp⇒ f g = mk⇒ (λ z → _⇒_.r g (_⇒_.r f z)) (λ z → _⇒_.i g (_⇒_.i f z))
              (λ z → _⇒_.p g (_⇒_.p f z)) tt tt

sem : ∀ {Base}{c}{A : Syn.Type Base} → Syn.Term c A → (ρ : Base → THSp) → (⟅ c ⟆ ρ ⇒ ⟦ A ⟧ ρ)
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {.(lookup v Γ)} (Syn.♭var v) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {.(lookup v Δ)} (Syn.ℜvar v) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {.(lookup v Θ)} (Syn.var v) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {.(Syn.ℜ _)} (Syn.ℜI t) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {A} (Syn.ℜE t t₁) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {.(Syn.ℑ _)} (Syn.ℑI t) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {A} (Syn.ℑE t t₁) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {.(Syn.& _)} (Syn.&I t) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {A} (Syn.&E t) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {.(Syn.∫ _)} (Syn.∫I t) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {A} (Syn.∫E t t₁) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {.(Syn.♭ _)} (Syn.♭I t) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {A} (Syn.♭E t t₁) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {.(Syn.♯ _)} (Syn.♯I t) ρ = {!!}
sem {c = Syn.[ Γ ∣ Δ ∣ Θ ∣ Λ ∣ Ξ ]} {A} (Syn.♯E t) ρ = {!!}
