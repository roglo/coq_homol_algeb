(* WORK IN PROGRESS (2018-06-01) *)

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

Theorem mono_is_inj : ∀ A B (f : HomGr A B),
  is_mono f
  → ∀ x1 x2, x1 ∈ A → x2 ∈ A → (Happ f x1 = Happ f x2)%G → (x1 = x2)%G.
Proof.
intros * Hf * Hx1 Hx2 Hxx.
(* morphism identity from Ker f to A *)
set (v x := let _ : gr_set (Ker f) := x in x : gr_set A).
assert (Hmc : ∀ x, x ∈ Ker f → v x ∈ A) by (intros x Hx; apply Hx).
set (hv :=
  {| Happ := v;
     Hmem_compat := Hmc;
     Happ_compat _ _ _ _ H := H;
     Hadditive _ _ _ _ := gr_eq_rel_Reflexive _ |}).
(* morphism null from Ker f to A *)
set (hw :=
  {| Happ x := let _ : gr_set (Ker f) := x in 0 : gr_set A;
     Hmem_compat _ _ := gr_zero_mem A;
     Happ_compat _ _ _ _ _ := gr_eq_rel_Reflexive _;
     Hadditive _ _ _ _ := gr_eq_rel_Symmetric _ _ (gr_add_0_r _ _) |}).
specialize (Hf (Ker f) hv hw) as H1.
assert (H : ∀ z, (Happ f (Happ hv z) = Happ f (Happ hw z))%G). {
  intros z.
  unfold hv, hw, v; simpl.
...

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
      etransitivity.
      -apply Happ_compat; [ now apply d | | apply Hdt ].
       now apply h'.
      -assert (H : Happ h' z' ∈ Im h') by (exists z'; easy).
       now apply s' in H; simpl in H.
    }
...
    set (v (b : gr_set Gr2) := if b then Happ j t else 0).
    assert (Hmc : ∀ x : gr_set Gr2, x ∈ Gr2 → v x ∈ E). {
      intros x Hx.
      destruct x; [ now apply j | apply E ].
    }
    assert (Hac : ∀ x y, x ∈ Gr2 → y ∈ Gr2 → (x = y)%G → (v x = v y)%G). {
      intros * Hx Hy Hxy.
      now rewrite <- Hxy.
    }
    assert (Had : ∀ x y, x ∈ Gr2 → y ∈ Gr2 → (v (x + y) = v x + v y)%G). {
      intros * Hx Hy.
      destruct x, y; simpl.
...
    set (hv :=
      {| Happ := v;
         Hmem_compat := Hmc;
         Happ_compat := Hac;
         Hadditive := Had |}).
    specialize (Hme Gr2 hv) as H1.
...

set (w (b : bool) := @gr_zero E).
...
    specialize (Hme bool (λ b, if b then Happ j t else 0) (λ _, 0)) as H1.
    simpl in H1.
    assert
      (H2 : ∀ x : bool, (Happ e (if x then Happ j t else 0) = Happ e 0)%G). {
      intros x; destruct x; [ | easy ].
      now rewrite Hzero.
    }
    now specialize (H1 H2 true); clear H2.
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
   rewrite Hinv; [ | easy ].
   rewrite <- Hchh'.
   apply gr_sub_move_r.
   rewrite gr_add_0_l.
   etransitivity; [ | apply Hdt ].
   apply d; [ now apply h | easy | apply Hhz ].
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
  rewrite Hinv; [ | now apply g ].
  apply gr_sub_move_r.
  apply gr_sub_move_l.
  rewrite <- Hgy'.
  rewrite Hcgg'.
  apply g'; [ easy | now apply b | ].
  now symmetry.
}
etransitivity.
-apply g₁; [ easy | | symmetry; apply H ].
 apply c, C; [ easy | now apply C, g ].
-rewrite H1.
 apply g₂; [ | easy | easy ].
 apply c, C; [ easy | now apply C, g ].
Qed.

Check four_1.

(*
Print Assumptions four_1.
*)

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
unfold is_mono.
intros T g₁ g₂ H z.
...
