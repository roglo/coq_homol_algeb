(* Five lemma *)

Require Import Utf8.
Require Import AbGroup.

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
     (h' : HomGr C' D') (j' : HomGr D' E'),
  diagram_commutes f a b f'
  → diagram_commutes g b c g'
  → diagram_commutes h c d h'
  → diagram_commutes j d e j'
  → exact_sequence (Seq f (Seq g (Seq h (Seq j SeqEnd))))
  → exact_sequence (Seq f' (Seq g' (Seq h' (Seq j' SeqEnd))))
  → is_iso b ∧ is_iso d ∧ is_epi a ∧ is_mono e
  → is_iso c.
Proof.
...
