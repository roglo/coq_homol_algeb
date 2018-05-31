(* WORK IN PROGRESS (2018-05-30) *)

(* The two Four Lemmas *)

Require Import Utf8.
Require Import AbGroup Setoid.

(* Four lemma #1
           g       h        j
        B------>C------>D------>E
        |       |       |       Γ
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
  (Decidable_Equality * Excluded_Middle)
  → diagram_commutes g b c g'
  → diagram_commutes h c d h'
  → diagram_commutes j d e j'
  → exact_sequence [g; h; j]
  → exact_sequence [g'; h'; j']
  → is_epi b ∧ is_epi d ∧ is_mono e
  → is_epi c.
Proof.
intros * (eq_dec, excl_midd) Hcgg' Hchh' Hcjj' s s' (Heb & Hed & Hme).
unfold is_epi.
enough
  (∀ T (g₁ g₂ : gr_set C' → T),
  (∀ z : gr_set C, g₁ (Happ c z) = g₂ (Happ c z))
  → ∀ z' : gr_set C', g₁ z' = g₂ z'). {
  now intros T g₁ g₂ H1; apply H.
}
intros * Hgc *.
unfold is_epi in Heb, Hed.
unfold is_mono in Hme.
assert (H : ∃ t, (Happ d t = Happ h' z')%G). {
  assert (Hn : ¬ (∀ t, (Happ d t ≠ Happ h' z')%G)). {
    set (v d' := if eq_dec _ d' (Happ h' z') then true else false).
    set (w (d' : gr_set D') := false).
    specialize (Hed _ v w) as H1.
    intros H2.
    assert (H : ∀ x : gr_set D, v (Happ d x) = w (Happ d x)). {
      intros t.
      unfold v, w.
      destruct (eq_dec _ (Happ d t) (Happ h' z')) as [H| H]; [ | easy ].
      now specialize (H2 t).
    }
    specialize (H1 H (Happ h' z')).
    unfold v, w in H1.
    destruct (eq_dec _ (Happ h' z') (Happ h' z')) as [H3| H3]; [ easy | ].
    now apply H3.
  }
  specialize (excl_midd (∃ t, Happ d t = Happ h' z')) as H2.
  destruct H2 as [H2| H2]; [ easy | ].
  exfalso; apply Hn; intros t H3.
  apply H2.
  now exists t.
}
destruct H as (t & Ht).
assert (H : ∃ z, (Happ h z = t)%G). {
  assert (H : t ∈ Ker j). {
    simpl.
...
