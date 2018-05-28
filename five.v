(* WORK IN PROGRESS (2018-05-18) *)

(* Five lemma *)

Require Import Utf8.
Require Import AbGroup.

Definition is_mono {A B} (f : HomGr A B) :=
  ∀ C (g₁ g₂ : HomGr C A),
  (∀ x, H_app f (H_app g₁ x) = H_app f (H_app g₂ x))
  → (∀ x, H_app g₂ x = H_app g₂ x).

Definition is_epi {A B} (f : HomGr A B) :=
  ∀ C (g₁ g₂ : HomGr B C),
  (∀ x, H_app g₁ (H_app f x) = H_app g₂ (H_app f x))
  → (∀ y, H_app g₂ y = H_app g₂ y).

Definition is_iso {A B} (f : HomGr A B) :=
  ∃ g : HomGr B A, (∀ x, H_app g (H_app f x) = x) ∧ (∀ y, H_app f (H_app g y) = y).

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
intros * Hcff' Hcgg' Hchh' Hcjj' s s' (Hea & Hib & Hid & Hme).
destruct Hib as (b' & Hb'b & Hbb').
destruct Hid as (d' & Hd'd & Hdd').
unfold is_epi in Hea.
unfold is_mono in Hme.
move b' before s'; move d' before b'.
unfold is_iso.
enough
  (H : ∃ c',
   (∀ x : gr_set C, H_app c' (H_app c x) = x) ∧
   (∀ y : gr_set C', H_app c (H_app c' y) = y)). {
  destruct H as (c' & Hc'c & Hcc').
  now exists c'.
}
...
