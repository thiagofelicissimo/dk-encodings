require open dk-encodings.att.att;

// type
constant symbol heq : Π A : U TSet, El TSet A → El TSet A → U Prop;

// constructor
constant symbol hrefl : Π (A : U TSet) (a : El TSet A), El Prop (heq A a a);

// eliminators

// into Prop
symbol heq_ind : Π (A : U TSet)
                  (x : El TSet A)
                  (P : Π y : El TSet A, El Prop (heq A x y) → U Prop)
                  (_ : El Prop (P x (hrefl A x)))
                  (y : El TSet A)
                  (e : El Prop (heq A x y)),
                  El Prop (P y e);

// into TProp (large)
symbol heq_hind : Π (A : U TSet)
                  (x : El TSet A)
                  (P : Π y : El TSet A, El Prop (heq A x y) → U TProp)
                  (_ : El TProp (P x (hrefl A x)))
                  (y : El TSet A)
                  (e : El Prop (heq A x y)),
                  El TProp (P y e);

// into Set (large)
symbol heq_rec : Π (A : U TSet)
                  (x : El TSet A)
                  (P : Π y : El TSet A, El Prop (heq A x y) → U Set)
                  (_ : El Set (P x (hrefl A x)))
                  (y : El TSet A)
                  (e : El Prop (heq A x y)),
                  El Set (P y e);

// into TSet (large)
symbol heq_hrec : Π (A : U TSet)
                  (x : El TSet A)
                  (P : Π y : El TSet A, El Prop (heq A x y) → U TSet)
                  (_ : El TSet (P x (hrefl A x)))
                  (y : El TSet A)
                  (e : El Prop (heq A x y)),
                  El TSet (P y e);

// computation rules                
rule heq_ind $A $x _ $px $x (hrefl $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?
rule heq_hind $A $x _ $px $x (hrefl $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?
rule heq_rec $A $x _ $px $x (hrefl $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?
rule heq_hrec $A $x _ $px $x (hrefl $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?
