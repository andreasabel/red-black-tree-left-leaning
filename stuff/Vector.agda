module Vector where

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat hiding (_≤_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Vektoren beliebigen Typs und einfache Operationen

data Vector (A : Set) : ℕ → Set where
 [] : Vector A 0
 _∷_ : ∀ {n} → A → Vector A n → Vector A (suc n)

head : ∀ {A n} → Vector A (suc n) → A
head (h ∷ _) = h

tail : ∀ {A n} → Vector A (suc n) → Vector A n
tail (_ ∷ t) = t

∥_∥ : ∀ {A n} → Vector A n → ℕ
∥_∥ {_} {n} _ = n

_++_ : ∀ {A n m} → Vector A n → Vector A m → Vector A (n + m)
[] ++ v = v
(h ∷ []) ++ v' = h ∷ v'
(h ∷ t) ++ v' = h ∷ (t ++ v')

-- fantastischer Beweis, dass das verdoppeln eines Vektors
-- seine Länge verdoppelt
doppelterVektor⇒doppelteLänge : ∀ {a n} (v : Vector a n) → ∥ v ++ v ∥  ≡  n + n
doppelterVektor⇒doppelteLänge _ = refl


-- Alles ab hier benötigt eine entscheidbare totale Ordnung, deswegen als
-- parametrisiertes Modul.

module OrderedVector {α : Set}
                     (_≤_ : α → α → Set)
                     (trans : Transitive _≤_)
                     (total : Total _≤_) where

  -- Element in Vektor einfügen, Sortierung beibehalten (Beweis folgt)
  insert : ∀ {n} → α → Vector α n → Vector α (suc n)
  insert {0} a [] = a ∷ []
  insert {suc n} a (x ∷ v) with total a x
  ... | inj₁ _ = a ∷ (x ∷ v)
  ... | inj₂ _ = x ∷ (insert a v)

  _≤*_ : ∀ {n} → α → (v : Vector α n) → Set
  _ ≤* [] = ⊤
  x ≤* (h ∷ t) = (x ≤ h) × (x ≤* t)

  -- Prädikat eines aufsteigend sortierten Vektors
  Sorted : ∀ {n} → Vector α n → Set
  Sorted [] = ⊤
  Sorted (h ∷ t) = (h ≤* t) × (Sorted t)

  -- Ist ein Element kleiner als der Kopf eines sortierten Vektors, so ist es
  -- kleiner als alle Elemente
  tailsmaller : ∀ {n a x} → (v : Vector α n) → Sorted (x ∷ v) → a ≤ x → a ≤* v
  tailsmaller [] _ _ = tt
  tailsmaller (h ∷ t) (x≤*ht , htSorted) a≤x =
    let a≤h = trans a≤x (proj₁ x≤*ht)
    in a≤h ,  tailsmaller t htSorted a≤h


  -- Ist x ≤ ein einzufügendes Element a und ≤ allen Elementen des Vektors in den
  -- eingefügt wird, so ist x auch ≤ allen Elementen des Vektors nachdem Element a
  -- eingefügt wurde.
  lemma : ∀ {n} → ∀ x a → (v : Vector α n) → x ≤ a → x ≤* v → x ≤* (insert a v)
  lemma _ _ [] x≤a _ =  x≤a , tt
  lemma x a (h ∷ t) x≤a (x≤h , h≤*v) with total a h
  ... | inj₁ p =  x≤a ,  x≤h , h≤*v
  ... | inj₂ p = x≤h , lemma x a t x≤a h≤*v

  -- insert behält die Sortierung eines Vektors bei.
  insertSorted : ∀ {n} → (a : α) (v : Vector α n) → Sorted v → Sorted (insert a v)
  insertSorted _ [] vSorted = tt , vSorted
  insertSorted a (x ∷ v) xvSorted with total a x
  ... | inj₁ a≤x = ( a≤x ,  tailsmaller v xvSorted a≤x) , xvSorted
  ... | inj₂ x≤a = lemma x a v x≤a (proj₁ xvSorted) , insertSorted a v (proj₂ xvSorted)


  -- Diese Datenstruktur ist per Konstruktion sortiert.
  -- Ich hab's mit Unicode wirklich total übertrieben, dieses mal.
  mutual
    data SortedVector : ℕ → Set where
      ≤[] : SortedVector 0
      _≤∷_⟵_ : ∀ {n} → (a : α) → (v : SortedVector n) → (a ≤≤* v) → SortedVector (suc n)

    _≤≤*_ : ∀ {n} → (a : α) → (v : SortedVector n) → Set
    _ ≤≤* ≤[] = ⊤
    a ≤≤* (x ≤∷ _ ⟵ _) = a ≤ x

  mutual
    insert≤ : ∀ {n} → (a : α) (v : SortedVector n) → SortedVector (suc n)
    insert≤ a ≤[] = a ≤∷ ≤[] ⟵ tt
    insert≤ a (x ≤∷ v ⟵ x≤≤*v) with total a x
    ... | inj₁ a≤x = a ≤∷ (x ≤∷ v ⟵ x≤≤*v) ⟵ a≤x
    ... | inj₂ x≤a = x ≤∷ (insert≤ a v) ⟵ (lemma≤ x a v x≤a x≤≤*v)

    lemma≤ : ∀ {n} → (x a : α) (v : SortedVector n) → x ≤ a → x ≤≤* v → x ≤≤* (insert≤ a v)
    lemma≤ _ _ ≤[] x≤a _ = x≤a
    lemma≤ x a (h ≤∷ t ⟵ h≤≤*t) x≤a x≤≤*v with total a h
    ... | inj₁ a≤h = x≤a
    ... | inj₂ h≤a = x≤≤*v
