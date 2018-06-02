(* Five lemma *)

Require Import Utf8.
Require Import AbGroup Setoid.
Require Import four.

Theorem is_iso_is_epi : ∀ A B (f : HomGr A B), is_iso f → is_epi f.
Proof.
intros * (g & Hgf & Hfg) C * Hgg * Hy.
specialize (Hfg y Hy) as H1.
etransitivity.
-apply g₁; [ easy | | symmetry; apply H1 ].
 now apply f, g.
-rewrite Hgg; [ | now apply g ].
 apply g₂; [ now apply f, g | easy | easy ].
Qed.

Theorem is_iso_is_mono : ∀ A B (f : HomGr A B), is_iso f → is_mono f.
Proof.
intros * (g & Hgf & Hfg) C * Hgg * Hz.
specialize (Hgg z Hz) as H1.
apply (Happ_compat _ _ g) in H1; [ | now apply f, g₁ | now apply f, g₂ ].
rewrite Hgf in H1; [ | now apply g₁ ].
rewrite Hgf in H1; [ | now apply g₂ ].
easy.
Qed.

Theorem epi_mono_is_iso : ∀ A B (f : HomGr A B),
  Decidable_Membership * Choice
  → is_epi f → is_mono f → is_iso f.
Proof.
intros * (mem_dec, choice) He Hm.
unfold is_iso.
specialize (epi_is_surj He) as H1.
specialize (mono_is_inj Hm) as H2.
assert (H3 : ∀ y, ∃ t, y ∈ B → t ∈ A ∧ (Happ f t = y)%G). {
  intros y.
  specialize (H1 y).
  specialize (mem_dec B y) as [H3| H3].
  -specialize (H1 H3) as (x & Hx & Hfx).
   exists x; intros H; easy.
  -exists 0; easy.
}
specialize (choice _ _ _ H3) as (g & Hg).
assert (Hmc : ∀ x : gr_set B, x ∈ B → g x ∈ A). {
  intros y Hy.
  now specialize (Hg _ Hy).
}
assert (Hac : ∀ x y, x ∈ B → y ∈ B → (x = y)%G → (g x = g y)%G). {
  intros y1 y2 Hy1 Hy2 Hyy.
  specialize (Hg _ Hy1) as H; destruct H as (Hgy1, Hfgy1).
  specialize (Hg _ Hy2) as H; destruct H as (Hgy2, Hfgy2).
  move Hgy2 before Hgy1.
  rewrite Hyy in Hfgy1 at 2.
  rewrite <- Hfgy2 in Hfgy1.
  now apply H2.
}
assert (Had : ∀ x y, x ∈ B → y ∈ B → (g (x + y) = g x + g y)%G). {
  intros y1 y2 Hy1 Hy2.
  specialize (Hg _ Hy1) as H; destruct H as (Hg1, Hfg1).
  specialize (Hg _ Hy2) as H; destruct H as (Hg2, Hfg2).
  move Hg2 before Hg1.
  apply H2; [ now apply Hmc, B | now apply A | ].
  rewrite Hadditive; [ | easy | easy ].
  rewrite Hfg1, Hfg2.
  now apply Hg, B.
}
set (hv :=
  {| Happ := g;
     Hmem_compat := Hmc;
     Happ_compat := Hac;
     Hadditive := Had |}).
exists hv; simpl.
split.
-intros x Hx.
 apply H2; [ now apply Hmc, f | easy | ].
 now apply Hg, f.
-intros y Hy.
 now apply Hg.
Qed.

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
  Decidable_Membership * Choice
  → diagram_commutes f a b f'
  → diagram_commutes g b c g'
  → diagram_commutes h c d h'
  → diagram_commutes j d e j'
  → exact_sequence [f; g; h; j]
  → exact_sequence [f'; g'; h'; j']
  → is_epi a ∧ is_iso b ∧ is_iso d ∧ is_mono e
  → is_iso c.
Proof.
intros * dc.
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
  split; [ | split ]; [ | | easy ]; now apply is_iso_is_epi.
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
  split; [ | split ]; [ | | easy ]; now apply is_iso_is_mono.
}
specialize (H2 H); clear H.
now apply epi_mono_is_iso.
Qed.

Check five.
