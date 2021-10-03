constant symbol Prop : TYPE;
constant symbol Set  : TYPE;
constant symbol T    : Set → TYPE;
constant symbol i    : Set;
constant symbol eq   : T i → T i → Prop;

//symbol ∀ :Π a : Set, (T a → Prop) → Prop;
//notation ∀ quantifier;
//compute λ p, ∀ (λ x, p); // prints `∀ x, p

//symbol ∀ {a} : (T a → Prop) → Prop;
//notation ∀ quantifier;
//compute λ p, ∀ (λ x, p); // prints `∀ x, p
//type λ p, `∀ x, p; // quantifiers can be written as such


