(* WORK IN PROGRESS (2018-05-30) *)

(* The two Four Lemmas *)

Require Import Utf8.
Require Import AbGroup Setoid.

Definition is_mono {A B} (f : HomGr A B) :=
  ∀ C (g₁ g₂ : C → gr_set A),
  (∀ x, (Happ f (g₁ x) = Happ f (g₂ x))%G)
  → (∀ x, (g₁ x = g₂ x)%G).

Definition is_epi {A B} (f : HomGr A B) :=
  ∀ C (g₁ g₂ : gr_set B → C),
  (∀ x, g₁ (Happ f x) = g₂ (Happ f x))
  → (∀ y, g₁ y = g₂ y).

Definition is_iso {A B} (f : HomGr A B) :=
  ∃ g : HomGr B A,
  (∀ x, (Happ g (Happ f x) = x)%G) ∧
  (∀ y, (Happ f (Happ g y) = y)%G).

(* Four lemma #1
           g       h        j
        B------>C------>D------>E
        |       |       |       |
       b|      c|      d|      e|
        |       |       |       |
        v       v       v       v
        B'----->C'----->D'----->E'
           g'      h'      j'

  If 1/ the diagram is commutative,
     2/ (g, h, j) and (g', h', j') are exact,
     3/ b and d are epimorphisms,
     4/ e is monomorphism,
  Then
     c is an epimorphism.
*)

Lemma four_1 :
  ∀ (B C D E B' C' D' E' : AbGroup)
     (g : HomGr B C) (h : HomGr C D) (j : HomGr D E)
     (g' : HomGr B' C') (h' : HomGr C' D') (j' : HomGr D' E')
     (b : HomGr B B') (c : HomGr C C')
     (d : HomGr D D') (e : HomGr E E'),
  diagram_commutes g b c g'
  → diagram_commutes h c d h'
  → diagram_commutes j d e j'
  → exact_sequence [g; h; j]
  → exact_sequence [g'; h'; j']
  → is_epi b ∧ is_epi d ∧ is_mono e
  → is_epi c.
Proof.
intros * Hcgg' Hchh' Hcjj' s s' (Heb & Hed & Hme).
unfold is_epi.
enough
  (∀ T (g₁ g₂ : gr_set C' → T),
  (∀ z : gr_set C, g₁ (Happ c z) = g₂ (Happ c z))
  → ∀ z' : gr_set C', g₁ z' = g₂ z'). {
  now intros T g₁ g₂ H1; apply H.
}
intros * Hgc *.
...
