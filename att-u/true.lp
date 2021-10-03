require open dk-encodings.att.att;

// type
constant symbol ⊤ : U Prop;

// constructor
constant symbol I-⊤ : El Prop ⊤;

// eliminators

// into Prop
symbol ⊤_ind : Π (A : U Prop),
                 El Prop A →
                 El Prop ⊤ →
                 El Prop A;

// into TProp (large)
symbol ⊤_hind : Π (A : U TProp),
                 El TProp A →
                 El Prop ⊤ →
                 El TProp A;

// into Set (large)
symbol ⊤_rec : Π (A : U Set),
                 El Set A →
                 El Prop ⊤ →
                 El Set A;

// into TSet (large)
symbol ⊤_hrec : Π (A : U TSet),
                 El TSet A →
                 El Prop ⊤ →
                 El TSet A;

// computation rules                
rule ⊤_ind _ $a I-⊤ ↪ $a;
rule ⊤_hind _ $a I-⊤ ↪ $a;
rule ⊤_rec _ $a I-⊤ ↪ $a;
rule ⊤_hrec _ $a I-⊤ ↪ $a;
