(* WORK IN PROGRESS (2018-06-02) *)

(* Five lemma *)

Require Import Utf8.
Require Import AbGroup Setoid.
Require Import four.

Theorem iso_is_epi : ∀ A B (f : HomGr A B), is_iso f → is_epi f.
Proof.
intros * (g & Hgf & Hfg) C * Hgg * Hy.
specialize (Hfg y) as H1.
etransitivity.
-apply g₁; [ easy | | symmetry; apply H1 ].
 now apply f, g.
-rewrite Hgg; [ | now apply g ].
 apply g₂; [ now apply f, g | easy | easy ].
Qed.

Theorem iso_is_mono : ∀ A B (f : HomGr A B), is_iso f → is_mono f.
Proof.
intros * (g & Hgf & Hfg) C * Hgg * Hz.
specialize (Hgg z Hz) as H1.
...

(* The five lemma
         f      g       h        j
     A------>B------>C------>D------>E
     |       |       |       |       |
    a|      b|      c|      d|      e|
     |       |       |       |       |
     v       v       v       v       v
     A'----->B'----->C'----->D'----->E'
        f'      g'      h'      j'

  If 1/ the diagram is commutative,
     2/ (f, g, h, j) and (f', g', h', j') are exact
     3/ b and d are isomorphisms
     4/ a is an epimorphism
     5/ e is a monomorphism
  Then
     c is an isomorphism.
*)

Lemma five :
  ∀ (A B C D E A' B' C' D' E' : AbGroup)
     (f : HomGr A B) (g : HomGr B C) (h : HomGr C D) (j : HomGr D E)
     (f' : HomGr A' B') (g' : HomGr B' C')
     (h' : HomGr C' D') (j' : HomGr D' E')
     (a : HomGr A A') (b : HomGr B B') (c : HomGr C C')
     (d : HomGr D D') (e : HomGr E E'),
  diagram_commutes f a b f'
  → diagram_commutes g b c g'
  → diagram_commutes h c d h'
  → diagram_commutes j d e j'
  → exact_sequence [f; g; h; j]
  → exact_sequence [f'; g'; h'; j']
  → is_epi a ∧ is_iso b ∧ is_iso d ∧ is_mono e
  → is_iso c.
Proof.
intros *.
intros Hcff' Hcgg' Hchh' Hcjj' s s' (Hea & Hib & Hid & Hme).
(* using lemma four #1 *)
specialize (four_1 B C D E B' C' D' E') as H1.
specialize (H1 g h j g' h' j' b c d e).
specialize (H1 Hcgg' Hchh' Hcjj').
assert (H : exact_sequence [g; h; j]) by apply s.
specialize (H1 H); clear H.
assert (H : exact_sequence [g'; h'; j']) by apply s'.
specialize (H1 H); clear H.
assert (H : is_epi b ∧ is_epi d ∧ is_mono e). {
  split; [ | split ]; [ | | easy ]; now apply iso_is_epi.
}
specialize (H1 H); clear H.
(* using lemma four #2 *)
specialize (four_2 A B C D A' B' C' D') as H2.
specialize (H2 f g h f' g' h' a b c d).
specialize (H2 Hcff' Hcgg' Hchh').
assert (H : exact_sequence [f; g; h]) by now destruct s as (t & u & v).
specialize (H2 H); clear H.
assert (H : exact_sequence [f'; g'; h']) by now destruct s' as (t & u & v).
specialize (H2 H); clear H.
assert (H : is_mono b ∧ is_mono d ∧ is_epi a). {
  split; [ | split ]; [ | | easy ].

...
