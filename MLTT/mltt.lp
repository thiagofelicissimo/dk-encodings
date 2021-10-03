constant symbol Type : TYPE;
constant symbol El : Type → TYPE;

// product

constant symbol Prod : Π (A : Type), (El A → Type) → Type;

constant symbol abs' : Π (A : Type) (B : El A → Type), (Π x : El A, El (B x)) → El (Prod A B);

symbol app' : Π (A : Type) (B : El A → Type), El (Prod A B) → Π (x : El A),  El (B x);

rule app' $A $B (abs' $A $B $M) $N ↪ $M $N;

// sum

constant symbol Sum : Π (A : Type), (El A → Type) → Type;

constant symbol pair : Π (A : Type) (B : El A → Type), Π (x : El A), El (B x) → El (Sum A B);

symbol pair_ind : Π (A : Type) (B : El A → Type) (P : El (Sum A B) → Type), (Π (x : El A) (y : El (B x)), El (P (pair A B x y))) → Π (p : El (Sum A B)), El (P p);

rule pair_ind $A $B $P $proof (pair $A $B $a $b) ↪ $proof $a $b;

// helpers

symbol Λ : Π {A : Type} {B : El A → Type}, (Π x : El A, El (B x)) → El (Prod A B)
     ≔ λ A B M, abs' A B M;
notation Λ quantifier;

symbol ∘ : Π {A : Type} {B : El A → Type}, El (Prod A B) → Π (x : El A),  El (B x)
     ≔ λ A B M N, app' A B M N;
notation ∘ infix left 7;

// nat

constant symbol Nat : Type;

constant symbol zero : El Nat;
constant symbol succ : El Nat → El Nat;

symbol nat_rec : Π (P : El Nat → Type), El (P zero) → (Π (n : El Nat), El (P n) → El (P (succ n))) → Π n : El Nat, El (P n);

rule nat_rec $P $p0 $ps zero ↪ $p0
with nat_rec $P $p0 $ps (succ $n) ↪ $ps $n (nat_rec $P $p0 $ps $n);

// sum
symbol plus ≔ `Λ n, `Λ m, nat_rec (λ _, Nat) m (λ _ acc, succ acc) n;

type plus;

symbol two_plus_one ≔ (plus ∘ (succ (succ zero))) ∘ (succ zero);

compute two_plus_one;

// universes

constant symbol Sort : TYPE;
constant symbol U : Sort → Type;
symbol T : Π {s : Sort}, El (U s) → Type;


constant symbol Set : Sort;
constant symbol TSet : Sort;
symbol ∨ : Sort → Sort → Sort;
rule ∨ Set Set ↪ Set
with ∨ TSet Set ↪ TSet
with ∨ TSet TSet ↪ TSet
with ∨ Set TSet ↪ TSet;
notation ∨ infix left 4;


constant symbol nat : El (U Set);
rule T nat ↪ Nat;

constant symbol π {s1 s2 : Sort} : Π (A : El (U s1)), (El (T A) → El (U s2)) → El (U (s1 ∨ s2));
rule T (π $a $b) ↪ Prod (T $a) (λ x, T ($b x));

constant symbol σ {s1 s2 : Sort} : Π (A : El (U s1)), (El (T A) → El (U s2)) → El (U (s1 ∨ s2));
rule T (σ $a $b) ↪ Sum (T $a) (λ x, T ($b x));

