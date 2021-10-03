// Levels
symbol L : TYPE;
symbol O : L;
symbol S : L → L;
symbol ⊔ : L → L → L;
rule ⊔ O $x ↪ $x
with ⊔ $x O ↪ $x
with ⊔ (S $x) (S $y) ↪ S (⊔ $x $y)
// adds more rules to simulate guillaume's encoding of L
with ⊔ $x $x ↪ $x
with ⊔ $x (S $x) ↪ S $x
with ⊔ (S $x) $x ↪ S $x
with ⊔ $x (⊔ $y $x) ↪ ⊔ $y $x
with ⊔ (⊔ $i (S $j)) (⊔ $i $j) ↪ (⊔ $i (S $j));

// Naturals
symbol N : TYPE;
symbol z : N;
symbol s : N → N;
symbol max : N → N → N;
rule max $x z ↪ $x
with max z $x ↪ $x
with max (s $x) (s $y) ↪ s (max $x $y);

// Sorts
constant symbol Sort : TYPE;
constant symbol U : Sort → TYPE;
constant symbol Set : L → Sort;
constant symbol Prop : L → Sort;
constant symbol Setω : N → Sort;
constant symbol SortLevel : Sort;

// Rule
symbol ∨ : Sort → Sort → Sort;
rule ∨ (Set $i) (Set $j) ↪ Set (⊔ $i $j)
with ∨ (Prop $i) (Prop $j) ↪ Prop (⊔ $i $j)
with ∨ (Setω $n) (Setω $m) ↪ Setω (max $n $m)
with ∨ (Set $i) (Prop $j) ↪ Prop (⊔ $i $j)
with ∨ (Prop $i) (Set $j) ↪ Set (⊔ $i $j)
with ∨ (Set _) (Setω $n) ↪ Setω $n
with ∨ (Setω $n) (Set _) ↪ Setω $n
with ∨ (Prop _) (Setω $n) ↪ Setω $n
with ∨ (Setω $n) (Prop _) ↪ Setω $n;


// Axiom
symbol □ : Sort → Sort;
rule □ (Set $i) ↪ Set (S $i)
with □ (Prop $i) ↪ Set (S $i)
with □ (Setω $n) ↪ Setω (s $n);

// Terms
symbol El : Π (s : Sort), U s → TYPE;

// Level
constant symbol Level : U SortLevel;
rule El _ Level ↪ L;


// Sort inclusion
symbol ⋄ : Π (s : Sort), U (□ s);
rule El _ (⋄ $s) ↪ U $s; 

symbol sortProd : Π (s : Sort) (A : U s) (s' : El s A → Sort), Sort;
rule sortProd SortLevel Level (λ y, $S[])   ↪ $S;
rule sortProd SortLevel Level (λ x, $S[x])  ↪ Setω z
with sortProd (Set $i) _ (λ _, $s')  ↪ ∨ (Set $i) $s';

compute sortProd (Set (S O)) (⋄ (Set O)) (λ _, Set (S (S O)));
compute sortProd SortLevel Level (λ y, Set (S O));
compute sortProd SortLevel Level (λ y, Set y);


// Products
symbol ⇝ : Π (s : Sort) (A : U s) (s' : El s A → Sort), (Π x : El s A, U (s' x)) → U (sortProd s A s');
rule El _ (⇝ $s $s' $A $B) ↪ Π (x : El $s $A), El $s' ($B x);


// Universe Polymorphism
symbol ∀s : Π α : L → L, (Π (i : L), U (Set (α i))) → U (Setω z);
rule El _ (∀s $α $A) ↪ Π (i : L), El (Set ($α i)) ($A i);
symbol ∀p : Π (α : L → L), (Π (i : L), U (Prop (α i))) → U (Setω z);
rule El _ (∀p $α $A) ↪ Π (i : L), El (Prop ($α i)) ($A i);
symbol ∀ω : Π (n : N), (L → U (Setω n)) → U (Setω n);
rule El _ (∀ω $n $A) ↪ Π (i : L), El (Setω $n) ($A i);

// Conjecture : The encoding described until here is both correct and complete


// Level lives in Set0
symbol Level : U (Set O);
rule El _ Level ↪ L;

// Conjecture : The encoding described until here is correct
// Problem : It is not complete
assert B ⊢ El (Set O) (⇝ (Set O) (Set O) Level B) ≡ El (Setω z) (∀s (λ _, O) B);

// ------- EXAMPLES ------- 

// --Nat--
// type
constant symbol Nat : El (Setω z) (∀s (λ i, S i) (λ i, ⋄ (Set i)));
// constructors
constant symbol zero : El (Setω z) (∀s (λ i, i) (λ i, Nat i));
constant symbol succ : El (Setω z) (∀s (λ i, i) (λ i, ⇝ (Set i) (Set i) (Nat i) (λ _, Nat i)));
// eliminator
symbol nat_ind : El (Setω z) (∀ω z (λ i, ∀s (λ j, (⊔ i (S j))) (λ j,
                                              (⇝ (Set (⊔ i (S j))) (Set (⊔ i j)) (⇝ (Set i) (Set (S j)) (Nat i) (λ _, ⋄ (Set j))) (λ P,
                                               ⇝ (Set j) (Set (⊔ i j)) (P (zero i)) (λ _,
                                               ⇝ (Set (⊔ i j)) (Set (⊔ i j)) (⇝ (Set i)  (Set j) (Nat i) (λ n,
                                                                                ⇝ (Set j) (Set j) (P n) (λ _, P ((succ i) n)))) (λ _,
                                               ⇝ (Set i) (Set j) (Nat i) (λ n, P n))))))));
// computation rules
rule nat_ind $i $j $P $pzero $psucc (zero $i) ↪ $pzero
with nat_ind $i $j $P $pzero $psucc (succ $i $n) ↪ $psucc $n (nat_ind $i $j $P $pzero $psucc $n);


// --Equality--
// type
constant symbol Eq : El (Setω z) (∀s (λ i, S i) (λ i, ⇝ (Set (S i)) (Set (S i)) (⋄ (Set i)) (λ A,
                                                      ⇝ (Set i) (Set (S i)) A (λ _,
                                                      ⇝ (Set i) (Set (S i)) A (λ _, ⋄ (Set i))))));
// constructors
constant symbol refl : El (Setω z) (∀s (λ i, S i) (λ i, ⇝ (Set (S i)) (Set i) (⋄ (Set i)) (λ A,
                                                        ⇝ (Set i) (Set i) A (λ x,
                                                        ⇝ (Set i) (Set i) A (λ y, Eq i A x y)))));
// eliminator
//nsymbol Eq_ind : El (Setω z) (∀s (λ i, S i) (λ i, ⇝ (Set (S i)) _ (⋄ (Set i)) (λ A,
//                                                 ⇝ _ _ (⇝ 


// --List--
// type
constant symbol List : El (Setω z) (∀s (λ i, S i) (λ i, ⇝ (Set (S i)) (Set (S i)) (⋄ (Set i)) (λ _, ⋄ (Set i))));
// constructors
constant symbol nil : El (Setω z) (∀s (λ i, S i) (λ i, ⇝ (Set (S i)) (Set i) (⋄ (Set i)) (λ A, List i A)));
constant symbol cons : El (Setω z) (∀s (λ i, S i) (λ i, ⇝ (Set (S i)) (Set i) (⋄ (Set i)) (λ A,
                                                        ⇝ (Set i) (Set i) A (λ a,
                                                        ⇝ (Set i) (Set i) (List i A) (λ l, List i A)))));
// eliminators TODO

// --List Nat--

// 1st option
// type
symbol ListNat : El (Setω z) (∀s (λ i, S i) (λ i, ⋄ (Set i))) ≔ λ i, (List i) (Nat i);
// constructors 
symbol nilNat : El (Setω z) (∀s (λ i, i) (λ i, ListNat i)) ≔ λ i, nil i (Nat i);
symbol consNat : El (Setω z) (∀s (λ i, i) (λ i, ⇝ (Set i) (Set i) (Nat i) (λ _,
                                                ⇝ (Set i) (Set i) (ListNat i) (λ _, ListNat i)))) ≔ λ i, cons i (Nat i);
                                                                           

// 2nd option : declare comp operator
symbol comp : El (Setω z) (⇝ (Setω z) (Setω z) (∀s (λ i, S i) (λ i, ⋄ (Set i))) (λ _, 
                           ⇝ (Setω z) (Setω z) (∀s (λ i, S i) (λ i, ⇝ (Set (S i)) (Set (S i)) (⋄ (Set i)) (λ _, ⋄ (Set i)))) (λ _, (∀s (λ i, S i) (λ i, ⋄ (Set i))))))
     ≔ λ x f i, (f i) (x i);

symbol ListNat' : El (Setω z) (∀s (λ i, S i) (λ i, ⋄ (Set i))) ≔ comp Nat List;
// symbol nilNat' : El (Setω z) (∀s (λ i, i) (λ i, ListNat' i)) ≔ comp Nat nil;

// --Contractible--
// type
constant symbol SetType : El (Setω (s z)) (⋄ (Setω z));
// constructor
constant symbol isSet : El (Setω z) (∀ω z (λ i, ⇝ (Set (S i)) (Setω z) (⋄ (Set i)) (λ i, SetType)));
// eliminator
//symbol SetType_ind : El (Setω z) (∀s _ (λ i, ⇝ (Setω z) _ (∀s (λ i, S i) (λ i, ⇝ (Set (S i)) (Set (S i)) (⋄ (Set i)) (λ A, ⋄ (Set i)))) (λ P,
//                                             ⇝ _ _ (∀s (λ i, S i) (λ i,  ⇝ (Set (S i)) (Set (S i)) (⋄ (Set i)) (λ A, P A))) (λ _,
//                                             ⇝ (Setω z) (Setω z) SetType (λ S_el, P


