require open dk-encodings.att-u.att;

constant symbol Σ : El ((⋄ (set z))              ⇝ (λ A, 
                        (A ⇝ (λ _, ⋄ (prop z))) ⇝ (λ _, 
                         ⋄ (prop z))));

constant symbol cons : El ((⋄ (set z))               ⇝ (λ A,
                           (A ⇝ (λ _, ⋄ (prop z)))  ⇝ (λ B,
                           A                         ⇝ (λ fst,
                           (B fst)                   ⇝ (λ snd,
                           Σ A B)))));

 
