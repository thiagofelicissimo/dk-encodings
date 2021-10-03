require open dk-encodings.att.att;

constant symbol Σ : El TSet (⇝ TSet  TSet I set (λ A,
                             ⇝ TProp TSet I (⇝ Set TProp I A (λ _, prop)) (λ _, set)));

constant symbol cons : El TSet  (⇝ TSet  TProp I set (λ A, 
                                (⇝ TProp Set   I (⇝ Set TProp I A (λ _, prop)) (λ B,
                                (⇝ Set   Set   I A (λ fst, 
                                (⇝ Prop  Set   I (B fst) (λ snd, Σ A B))))))));

symbol fst : El TSet (⇝ TSet  TProp I set (λ A,
                      ⇝ TProp Set   I (⇝ Set TProp I A (λ _, prop)) (λ B,
                      ⇝ Set   Set   I (Σ A B) (λ _, A))));

symbol snd : El ∀Prop (⇝ TSet  ∀Prop I set (λ A,
                       ⇝ TProp Prop  I (⇝ Set TProp I A (λ _, prop)) (λ B,
                       ⇝ Set   Prop  I (Σ A B) (λ pair, B (fst A B pair)))));

rule fst $A $B (cons $A _  $a $b) ↪ $a;
rule snd $A $B (cons $A $B $a $b) ↪ $b;
 
