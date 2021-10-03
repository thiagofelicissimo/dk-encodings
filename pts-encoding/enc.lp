constant symbol Sort : TYPE;
constant symbol U : Sort → TYPE;
symbol El : Π s : Sort, U s → TYPE;
constant symbol ⊤ : TYPE;
constant symbol I : ⊤;
symbol ℜ : Sort → Sort → Sort → TYPE;
rule ℜ _ _ _ ↪ ⊤;

symbol □ : Sort → Sort → TYPE;
constant symbol ⋄ s1 s2 (_ : □ s1 s2) : U s2;
rule El _ (⋄ _ $s _) ↪ U $s;





constant symbol Prod s1 s2 s3 (_ : ℜ s1 s2 s3) : Π (A : U s1) (B : El s1 A → U s2), U s3;

constant symbol abs s1 s2 s3 (i : ℜ s1 s2 s3) : Π (A : U s1) (B : El s1 A → U s2), (Π x : El s1 A, El s2 (B x)) → El s3 (Prod s1 s2 s3 i A B);

symbol app s1 s2 s3 (i : ℜ s1 s2 s3) : Π (A : U s1) (B : El s1 A → U s2), El s3 (Prod s1 s2 s3 i A B) → Π x : El s1 A, El s2 (B x);

rule app _ _ _ _ $A $B (abs _ _ _ _ $A $B $M) $N ↪ $M $N;
