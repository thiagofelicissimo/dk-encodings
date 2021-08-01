// ----------------- ITT ----------------

// ------------- TYPE SYSTEM ------------ 

// Levels
constant symbol L : TYPE;
constant symbol O : L;
constant symbol S : L → L;
symbol ⊔ : L → L → L;
notation ⊔ infix right 10;
rule O      ⊔ $x     ↪ $x
with $x     ⊔ O      ↪ $x
with (S $x) ⊔ (S $y) ↪ S ($x ⊔ $y);

// Sorts
constant symbol Set : L → TYPE;

// Terms
injective symbol El : Π {i : L}, Set i → TYPE;

// Axiom
symbol set : Π i : L, Set (S i);
rule El (set $i) ↪ Set $i;

// Products
constant symbol ⇝ : Π {i j : L} (A : Set i), (El A → Set j) → Set (i ⊔ j);
notation ⇝ infix right 10;
rule El ($A ⇝ $B) ↪ Π (x : El $A), El ($B x);

// ------------- TYPES ----------------

// --Natural numbers--
// type
constant symbol Nat : Set O;
// constructors
constant symbol zero : El Nat;
constant symbol succ : El Nat → El Nat;
// eliminator
symbol N_ind : Π {i : L} (P : El Nat → Set i), El (P zero) → (Π (n : El Nat), El (P n) → El (P (succ n))) → Π n : El Nat, El (P n);
// computation
rule N_ind $P $pzero $psucc zero      ↪ $pzero
with N_ind $P $pzero $psucc (succ $n) ↪ $psucc $n (N_ind $P $pzero $psucc $n);

// --Equality--
// type
constant symbol = : Π {i : L} {A : Set i}, El A → El A → Set i;
notation = infix right 10;
// constructors
constant symbol refl : Π {i : L} {A : Set i} {a : El A}, El (a = a);
// eliminator
symbol J : Π {i j : L} 
             {A : Set i} 
             (P : Π (a b : El A), El (a = b) → Set j), 
           (Π (a : El A), El (P a a refl)) → 
           Π (a b : El A) (p : El (a = b)), El (P a b p);
// computation
rule J $P $p_refl $a $a refl ↪ $p_refl $a;

symbol PaulinJ : Π {i j : L} 
                   (A : Set i)
                   (x : El A)
                   (D : Π (y : El A), El (x = y) → Set j)
                   (_ : El (D x refl))
                   (y : El A)
                   (p : El (x = y)),
                 El (D y p) ≔
λ i j A x D Drefl y p, J (λ a b p', (A ⇝ (λ y', (a = y') ⇝ (λ q, set j))) ⇝ (λ D', (D' a refl) ⇝ (λ _, D' b p'))) (λ a D' D'refl, D'refl) x y p D Drefl; 

compute PaulinJ;


// ------------ PROPOSITIONAL ETT --------------

symbol K : Π {i j : L} 
             (A : Set i)
             (a : El A)
             (P : El (a = a) → Set j),
           El (P refl) → 
           Π (p : El (a = a)), El (P p);
rule K $A $a $P $prefl refl ↪ $prefl;

// proving UIP
symbol UIP' : Π {i : L}
                (A : Set i)
                (a : El A)
                (p : El (a = a)),
              El (p = refl) ≔ 
  λ i A a, K A a (λ (p : El (a = a)), p = refl) refl;

symbol UIP : Π {i : L} 
               (A : Set i)
               (a b : El A)
               (p q : El (a = b)),
             El (p = q) ≔ 
  λ i A a b p q, J (λ a b q, (a = b) ⇝ (λ p, p = q)) (λ a', UIP' A a') a b q p;

compute UIP;
                        
                        



