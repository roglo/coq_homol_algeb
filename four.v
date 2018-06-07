(* The two Four Lemmas *)

Require Import Utf8.
Require Import AbGroup Setoid.

(* Four lemma #1
           g       h        j
        B------>C------>D------>E
        |       |       |       ∩
       b|      c|      d|      e|
        v       |       v       |
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
  (∀ T (g₁ g₂ : HomGr C' T),
   (∀ z, z ∈ C → (Happ g₁ (Happ c z) = Happ g₂ (Happ c z))%G)
   → ∀ z', z' ∈ C' → (Happ g₁ z' = Happ g₂ z')%G). {
  now intros T g₁ g₂ H1; apply H.
}
intros * Hgc * Hz'.
assert (H : ∃ t, t ∈ D ∧ (Happ d t = Happ h' z')%G). {
  apply epi_is_surj; [ easy | now apply h' ].
}
destruct H as (t & Ht & Hdt).
move t after z'; move Ht after Hz'.
assert (H : ∃ z, z ∈ C ∧ (Happ h z = t)%G). {
  assert (H : t ∈ Ker j). {
    split; [ easy | ].
    assert (H : (Happ e (Happ j t) = 0)%G). {
      rewrite Hcjj'.
(* works not: a coq morphism is required
rewrite Hdt.
*)
      etransitivity; [ apply Happ_compat | ]; [ | apply Hdt | ]; cycle 1.
      -assert (H : Happ h' z' ∈ Im h') by (exists z'; easy).
       now apply s' in H; simpl in H.
      -now apply d.
    }
    specialize (mono_is_inj Hme) as H1.
    apply H1; [ now apply j | apply E | now rewrite Hzero ].
  }
  apply s in H.
  destruct H as (z & Hz & Hhz).
  now exists z.
}
destruct H as (z & Hz & Hhz).
move z after t; move Hz after Ht.
assert (H : Happ c z - z' ∈ Ker h'). {
  split.
  -apply C'; [ now apply c | now apply C' ].
  -rewrite Hadditive; [ | now apply c | now apply C' ].
   rewrite Hopp; [ | easy ].
   rewrite <- Hchh'.
   apply gr_sub_move_r.
   rewrite gr_add_0_l.
   etransitivity; [ apply Happ_compat | ]; [ | apply Hhz | ]; try easy.
   now apply h.
}
apply s' in H.
destruct H as (y' & Hy' & Hgy').
move y' after z'; move Hy' before Hz'.
assert (H : ∃ y, y ∈ B ∧ (Happ b y = y')%G) by now apply epi_is_surj.
destruct H as (y & Hy & Hby).
move y after z; move Hy before Hz.
specialize (Hgc (z - Happ g y)) as H1.
assert (H : z - Happ g y ∈ C). {
  apply C; [ easy | now apply C, g ].
}
specialize (H1 H); clear H.
assert (H : (Happ c (z - Happ g y) = z')%G). {
  rewrite Hadditive; [ | easy | now apply C, g ].
  rewrite Hopp; [ | now apply g ].
  apply gr_sub_move_r.
  apply gr_sub_move_l.
  rewrite <- Hgy'.
  rewrite Hcgg'.
  apply g'; [ easy | now symmetry ].
}
symmetry in H.
etransitivity; [ apply Happ_compat | ]; [ | apply H | ]; cycle 1.
-rewrite H1.
 apply g₂; [ | easy ].
 apply c, C; [ easy | now apply C, g ].
-easy.
Qed.

Check four_1.

(* Four lemma #2
            f      g       h
        A------>B------>C------>D
        |       ∩       |       ∩
       a|      b|      c|      d|
        v       |       |       |
        v       v       v       v
        A'----->B'----->C'----->D'
           f'      g'      h'

  If 1/ the diagram is commutative,
     2/ (f, g, h) and (f', g', h') are exact,
     3/ b and d are monomorphisms,
     4/ a is epimorphism,
  Then
     c is an monomorphism.
*)

Lemma four_2 :
  ∀ (A B C D A' B' C' D' : AbGroup)
     (f : HomGr A B) (g : HomGr B C) (h : HomGr C D)
     (f' : HomGr A' B') (g' : HomGr B' C') (h' : HomGr C' D')
     (a : HomGr A A') (b : HomGr B B')
     (c : HomGr C C') (d : HomGr D D'),
  diagram_commutes f a b f'
  → diagram_commutes g b c g'
  → diagram_commutes h c d h'
  → exact_sequence [f; g; h]
  → exact_sequence [f'; g'; h']
  → is_mono b ∧ is_mono d ∧ is_epi a
  → is_mono c.
Proof.
intros * Hcff' Hcgg' Hchh' s s' (Hmb & Hmd & Hea).
intros T g₁ g₂ Hcg u Hu.
specialize (Hcg u Hu) as H.
assert (H1 :( Happ c (Happ g₁ u - Happ g₂ u) = 0)%G). {
  rewrite Hadditive; [ | now apply g₁ | now apply C, g₂ ].
  rewrite Hopp; [ | now apply g₂ ].
  now rewrite H, gr_add_opp_r.
}
clear H.
symmetry; rewrite <- gr_add_0_r; symmetry.
apply gr_sub_move_l.
set (z := Happ g₁ u - Happ g₂ u) in H1 |-*.
assert (Hz : z ∈ C) by (apply C; [ now apply g₁ | now apply C, g₂ ]).
move Hz before z.
generalize H1; intros H2.
apply (Happ_compat _ _ h') in H2; [ | now apply c ].
rewrite <- Hchh', Hzero in H2.
assert (H3 : z ∈ Ker h). {
  split; [ easy | ].
  apply (mono_is_inj Hmd); [ now apply h | apply D | now rewrite Hzero ].
}
apply s in H3.
destruct H3 as (y & Hy & Hgy).
generalize Hgy; intros H3.
apply (Happ_compat _ _ c) in H3; [ | now apply g ].
rewrite Hcgg', H1 in H3.
assert (H4 : Happ b y ∈ Ker g') by (split; [ now apply b | easy ]).
apply s' in H4.
destruct H4 as (x' & Hx' & Hfx').
assert (H : ∃ x, x ∈ A ∧ (Happ a x = x')%G) by now apply epi_is_surj.
destruct H as (x & Hx & Hax).
assert (H4 : (Happ f' (Happ a x) = Happ b y)%G). {
  etransitivity; [ apply Happ_compat | ]; [ | apply Hax | ]; try easy.
  now apply a.
}
rewrite <- Hcff' in H4.
apply mono_is_inj in H4; [ | easy | now apply f | easy ].
assert (H5 : (Happ g (Happ f x) = z)%G). {
  etransitivity; [ apply Happ_compat | ]; [ | apply H4 | ]; try easy.
  now apply f.
}
rewrite <- H5.
assert (H : Happ f x ∈ Im f) by now exists x.
apply s in H.
now destruct H.
Qed.

Check four_2.
