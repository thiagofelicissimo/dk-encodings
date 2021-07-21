constant symbol Set : TYPE;
injective symbol El : Set → TYPE;

constant symbol π : Π A : Set, (El A → Set) → Set;
rule El (π $A $B) ↪ Π (x : El $A), El ($B x);

constant symbol ∧ : Set → Set → Set;
rule El (∧ $A $B) ↪ Π (x : Set), (El $A → El $B → El x) → El x;

symbol andIn : Π (A B : Set), El A → El B → El (∧ A B) ≔
  λ A B a b x abx, abx a b;

symbol andEl : Π (A B : Set) (C : Set), (Π (a : El A) (b : El B), El C) → Π x : El (∧ A B), El C ≔
  λ A B C abc x, x C abc;


constant symbol Nat : Set;
rule El Nat ↪ Π (x : Set), (El x) → ((El x) → (El x)) → (El x);

symbol zero : El Nat ≔ λ x c0 cs, c0;
symbol succ : El Nat → El Nat ≔ λ (n : El Nat) (x : Set) (c0 : El x) (cs : El x → El x), cs (n x c0 cs);

// PROBLEM: no dependent elimination principle
symbol elimNat : Π C : Set, El C → (El C → El C) → El Nat → El C ≔ λ C p0 ps n, n C p0 ps;

assert C f0 fs ⊢ elimNat C f0 fs zero ≡ f0;
assert C f0 fs x ⊢ elimNat C f0 fs (succ x) ≡ fs (elimNat C f0 fs x);



symbol + : El Nat → El Nat → El Nat ≔ λ n m, elimNat Nat n (λ x, succ x) m;


compute + zero (succ zero);

compute + (succ zero) (succ (succ (succ zero)));

//assert n ⊢ (+ n (succ zero)) ≡ n;
