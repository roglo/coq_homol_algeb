(* Snake lemma *)

Require Import Utf8.
Require Import Classes.RelationClasses.
Require Import Setoid.

Require Import AbGroup.

(* Functor HomGr A B → HomGr (KerA) (KerB) *)

Theorem KK_mem_compat {A B A' B'} : ∀ (a : HomGr A A') (b : HomGr B B') f f',
  diagram_commutes f a b f'
  → ∀ x : gr_set (Ker a), x ∈ Ker a → Happ f x ∈ Ker b.
intros * Hc * (Hx & Hax).
split; [ now apply f | ].
rewrite Hc, <- (Hzero _ _ f').
apply f'; [ apply a, Hx | apply A' | apply Hax ].
Qed.

Theorem KK_app_compat {A B A'} : ∀ (f : HomGr A B) (a : HomGr A A'),
  ∀ x y : gr_set (Ker a),
  x ∈ Ker a → y ∈ Ker a → (x = y)%G → (Happ f x = Happ f y)%G.
Proof.
intros * Hx Hy Hxy.
simpl in Hx, Hy.
now apply f.
Qed.

Theorem KK_additive {A B A'} : ∀ (f : HomGr A B) (a : HomGr A A'),
  ∀ x y : gr_set (Ker a),
  x ∈ Ker a → y ∈ Ker a → (Happ f (x + y) = Happ f x + Happ f y)%G.
Proof.
intros * Hx Hx'; simpl in Hx, Hx'.
now apply f.
Qed.

Definition HomGr_Ker_Ker {A B A' B'}
    {f : HomGr A B} {f' : HomGr A' B'} (a : HomGr A A') (b : HomGr B B')
    (Hc : diagram_commutes f a b f') :=
  {| Happ (x : gr_set (Ker a)) := Happ f x : gr_set (Ker b);
     Hmem_compat := KK_mem_compat a b f f' Hc;
     Happ_compat := KK_app_compat f a;
     Hadditive := KK_additive f a |}.

(* Functor f:HomGr A B → g:HomGr B C → HomGr (CoKer f) (Coker g) *)

Theorem CC_mem_compat {A B A' B'} :
  ∀ (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  ∀ x : gr_set (Coker a), x ∈ Coker a → Happ f' x ∈ Coker b.
Proof.
intros * Hx.
now apply f'.
Qed.

Theorem CC_app_compat {A B A' B'} :
  ∀ (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  diagram_commutes f a b f'
  → ∀ x y : gr_set (Coker a),
     x ∈ Coker a
     → y ∈ Coker a
     → (x = y)%G
     → @gr_eq (Coker b) (Happ f' x) (Happ f' y)%G.
Proof.
intros * Hc * Hx Hy Hxy.
simpl in Hx, Hy, x, y, Hxy; simpl.
destruct Hxy as (z & Hz & Haz).
simpl; unfold Coker_eq; simpl.
exists (Happ f z).
split; [ now apply f | ].
rewrite Hc.
transitivity (Happ f' (x - y)%G).
-apply Happ_compat; [ now apply a | | easy ].
 apply A'; [ easy | now apply A' ].
-rewrite Hadditive; [ | easy | now apply A' ].
 apply gr_add_compat; [ easy | now apply Hinv ].
Qed.

Theorem CC_additive {A B A' B'} :
  ∀ (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  ∀ x y : gr_set (Coker a),
  x ∈ Coker a
  → y ∈ Coker a
  → @gr_eq (Coker b) (Happ f' (x + y))%G (Happ f' x + Happ f' y)%G.
Proof.
intros * Hx Hy; simpl in Hx, Hy.
exists 0%G.
split; [ apply B | ].
rewrite Hzero; symmetry.
simpl; apply gr_sub_move_r.
rewrite gr_add_0_l.
now apply Hadditive.
Qed.

Definition HomGr_Coker_Coker {A B A' B'}
    {f : HomGr A B} {f' : HomGr A' B'} (a : HomGr A A') (b : HomGr B B')
    (Hc : diagram_commutes f a b f') :=
  {| Happ (x : gr_set (Coker a)) := Happ f' x : gr_set (Coker b);
     Hmem_compat := CC_mem_compat f' a b;
     Happ_compat := CC_app_compat f f' a b Hc;
     Hadditive := CC_additive f' a b |}.

(* Morphism g in snake lemma is surjective *)

Theorem g_is_surj {B C C' g} (c : HomGr C C') {cz : HomGr C Gr1} :
   Decidable_Membership
   → Im g == Ker cz
   → ∀ x : gr_set (Ker c), ∃ y, x ∈ C → y ∈ B ∧ (Happ g y = x)%G.
Proof.
intros * mem_dec sg x.
destruct (mem_dec C x) as [H2| H2]; [ | now exists 0%G ].
enough (H : x ∈ Im g). {
  simpl in H.
  destruct H as (y & Hy & Hyx).
  now exists y.
}
apply sg.
split; [ easy | ].
now destruct (Happ cz x).
Qed.

(* Morphism f' in snake lemma is injective *)

Theorem f'_is_inj {A' B'} {f' : HomGr A' B'} {za' : HomGr Gr1 A'} :
   Im za' == Ker f'
   → ∀ x y, x ∈ A' → y ∈ A' → (Happ f' x = Happ f' y)%G → (x = y)%G.
Proof.
intros * sf' * Hx Hy Hxy.
assert (H2 : (Happ f' x - Happ f' y = 0)%G). {
  apply gr_sub_move_r.
  now rewrite gr_add_0_l.
}
assert (H3 : (Happ f' (x - y) = 0)%G). {
  rewrite Hadditive; [ | easy | now apply A' ].
  rewrite Hxy, Hinv; [ | easy ].
  apply gr_add_inv_r.
}
assert (H4 : (x - y)%G ∈ Ker f'). {
  split; [ | apply H3 ].
  apply A'; [ easy | now apply A' ].
}
apply sf' in H4.
simpl in H4.
destruct H4 as (z & _ & H4).
destruct z.
assert (H5 : (x - y = 0)%G). {
  rewrite <- H4.
  apply Hzero.
}
apply gr_sub_move_r in H5.
rewrite H5.
apply gr_add_0_l.
Qed.

(* Morphism f' (on cokernel) in snake lemma is injective *)

Theorem f'c_is_inj
    {A A' B'} {f' : HomGr A' B'} {a : HomGr A A'} {za' : HomGr Gr1 A'} :
  Im za' == Ker f'
  → ∀ x y, x ∈ Coker a → y ∈ Coker a →
     (Happ f' x = Happ f' y)%G → (x = y)%G.
Proof.
intros * sf' * Hx Hy Hxy.
simpl; unfold Coker_eq; simpl.
exists 0; split; [ apply A | ].
eapply (f'_is_inj sf'); [ apply a, A | | ].
-apply A'; [ easy | now apply A' ].
-transitivity (Happ f' 0).
 +apply f'; [ apply a, A | apply A' | apply Hzero ].
 +rewrite Hzero; symmetry.
  rewrite Hadditive; [ | easy | now apply A' ].
  rewrite Hxy, Hinv; [ | easy ].
  apply gr_add_inv_r.
Qed.

(* Property of g₁ function, inverse of snake lemma function g *)

Definition g₁_prop {B C C'} g (c : HomGr C C') g₁ :=
  ∀ x : gr_set (Ker c), x ∈ C → g₁ x ∈ B ∧ (Happ g (g₁ x) = x)%G.

(* Property of f'₁ function, inverse of snake lemma function f' *)

Definition f'₁_prop
    {A A' B C B' C'} (a : HomGr A A') (b : HomGr B B') {c : HomGr C C'}
    (f' : HomGr A' B') g₁ f'₁ :=
  ∀ x : gr_set B',
  (∃ x1 : gr_set (Ker c), x1 ∈ Ker c ∧ (x = Happ b (g₁ x1))%G)
  → f'₁ x ∈ Coker a ∧ (Happ f' (f'₁ x) = x)%G.

Theorem g₁_in_B : ∀ {B C C' g} {c : HomGr C C'} {g₁},
  g₁_prop g c g₁ → ∀ x, x ∈ C → g₁ x ∈ B.
Proof.
intros * Hg₁ * Hx.
now specialize (Hg₁ x Hx) as H.
Qed.

(* *)

Theorem exists_B'_to_Coker_a : ∀ {A A' B B' C C' g f'}
  {g' : HomGr B' C'} (a : HomGr A A') {b : HomGr B B'} {c : HomGr C C'} {g₁},
  Decidable_Membership
  → Im f' == Ker g'
  → g₁_prop g c g₁
  → diagram_commutes g b c g'
  → ∀ y', ∃ z',
    (∃ x, x ∈ Ker c ∧ (y' = Happ b (g₁ x))%G)
    → z' ∈ Coker a ∧ (Happ f' z' = y')%G.
Proof.
intros * mem_dec sg' Hg₁ Hcgg' *.
destruct (mem_dec (Im b) y') as [Hy'| Hy'].
-destruct (mem_dec (Im f') y') as [(z' & Hz' & Hfz')| Hfy'].
 +exists z'; now intros (x' & Hx' & Hyx').
 +exists 0%G; intros (x' & Hx' & Hyx').
  exfalso; apply Hfy', sg'; simpl.
  split.
  *destruct Hy' as (y & Hy & Hby).
   eapply B'; [ apply Hby | now apply b ].
  *transitivity (Happ g' (Happ b (g₁ x'))).
  --apply g'; [ | | easy ].
    ++destruct Hy' as (y & Hy & Hby).
      eapply B'; [ apply Hby | now apply b ].
    ++apply b, (g₁_in_B Hg₁), Hx'.
  --rewrite <- Hcgg'.
    destruct Hx' as (Hx', Hcx').
    specialize (Hg₁ x' Hx') as H2.
    destruct H2 as (Hgx', Hggx').
    transitivity (Happ c x'); [ | easy ].
    apply c; [ now apply g, (g₁_in_B Hg₁) | easy | easy ].
-exists 0%G; intros (x' & Hx' & Hyx').
 exfalso; apply Hy'.
 exists (g₁ x').
 split; [ apply (g₁_in_B Hg₁); now simpl in Hx' | ].
 now symmetry.
Qed.

(* Connecting homomorphism: d *)

Theorem d_mem_compat
     {A A' B B' C C'} {a : HomGr A A'} {b : HomGr B B'} {c : HomGr C C'}
     {f' : HomGr A' B'} {g₁ f'₁} :
  let d := λ x, f'₁ (Happ b (g₁ x)) in
  f'₁_prop a b f' g₁ f'₁
  → ∀ x, x ∈ Ker c → d x ∈ Coker a.
Proof.
intros * Hf'₁ * Hx.
apply Hf'₁.
now exists x.
Qed.

Theorem d_app_compat
    {A A' B B' C C'} {a : HomGr A A'} {b : HomGr B B'} {c : HomGr C C'}
    {f : HomGr A B} {g : HomGr B C} {f' : HomGr A' B'} {g' : HomGr B' C'}
    {za' : HomGr Gr1 A'} {g₁ f'₁} :
  diagram_commutes f a b f'
  → diagram_commutes g b c g'
  → Im f == Ker g
  → Im za' == Ker f'
  → Im f' == Ker g'
  → g₁_prop g c g₁
  → f'₁_prop a b f' g₁ f'₁
  → let d := λ x, f'₁ (Happ b (g₁ x)) in
     ∀ x1 x2, x1 ∈ Ker c → x2 ∈ Ker c → (x1 = x2)%G → (d x1 = d x2)%G.
Proof.
intros * Hcff' Hcgg' sf sf' sg' Hg₁ Hf'₁ * Hx1 Hx2 Hxx.
assert (Hgy1 : (Happ g (g₁ x1) = x1)%G) by apply Hg₁, Hx1.
assert (Hgy2 : (Happ g (g₁ x2) = x2)%G) by apply Hg₁, Hx2.
assert (Hgb1 : (Happ g' (Happ b (g₁ x1)) = 0)%G). {
  rewrite <- Hcgg'.
  etransitivity; [ | apply Hx1 ].
  apply c; [ apply g, Hg₁, Hx1 | apply Hx1 | apply Hgy1 ].
}
assert (Hgb2 : (Happ g' (Happ b (g₁ x2)) = 0)%G). {
  rewrite <- Hcgg'.
  etransitivity; [ | apply Hx2 ].
  apply c; [ apply g, Hg₁, Hx2 | apply Hx2 | apply Hgy2 ].
}
assert (H1 : Happ b (g₁ x1) ∈ Im f'). {
  apply sg'; split; [ apply b, (g₁_in_B Hg₁), Hx1 | easy ].
}
assert (H2 : Happ b (g₁ x2) ∈ Im f'). {
  apply sg'; split; [ apply b, (g₁_in_B Hg₁), Hx2 | easy ].
}
destruct H1 as (z'1 & Hz'1 & Hfz'1).
destruct H2 as (z'2 & Hz'2 & Hfz'2).
move z'2 before z'1; move Hz'2 before Hz'1.
assert (H3 : (Happ f' (z'1 - z'2) = Happ b (g₁ x1 - g₁ x2))%G). {
  rewrite Hadditive; [ | easy | now apply A' ].
  rewrite Hadditive.
  -apply gr_add_compat; [ apply Hfz'1 | ].
   rewrite Hinv; [ | easy ].
   rewrite Hinv; [ | apply Hg₁, Hx2 ].
   now rewrite Hfz'2.
  -apply (g₁_in_B Hg₁), Hx1.
  -apply B, (g₁_in_B Hg₁), Hx2.
}
assert (H4 : g₁ x1 - g₁ x2 ∈ Im f). {
  apply sf.
  split.
  -apply B; [ apply (g₁_in_B Hg₁), Hx1 | apply B, (g₁_in_B Hg₁), Hx2 ].
  -rewrite Hadditive; [ | apply Hg₁, Hx1 | apply B, Hg₁, Hx2 ].
   rewrite Hinv; [ | apply Hg₁, Hx2 ].
   apply gr_sub_move_r.
   now rewrite Hgy1, Hgy2, gr_add_0_l.
}
destruct H4 as (z & Hz & Hfz).
assert (H4 : (z'1 - z'2 = Happ a z)%G). {
  apply (f'_is_inj sf'); [ | now apply a | ].
  -apply A'; [ easy | now apply A' ].
  -rewrite <- Hcff', H3.
   apply b; [ | now apply f | now symmetry ].
   apply B; [ apply (g₁_in_B Hg₁), Hx1 | apply B, (g₁_in_B Hg₁), Hx2 ].
}
assert (H6 : z'1 - z'2 ∈ Im a). {
  exists z; split; [ easy | now symmetry ].
}
assert (Hdx2 : (d x2 = z'2)%G). {
  simpl; unfold Coker_eq; simpl.
  exists 0.
  split; [ apply A | ].
  rewrite Hzero; symmetry.
  apply gr_sub_move_r; symmetry.
  rewrite gr_add_0_l.
  apply (f'_is_inj sf'); [ easy | now apply Hf'₁; exists x2 | ].
  rewrite Hfz'2; symmetry.
  now apply Hf'₁; exists x2.
}
assert (Hdx1 : (d x1 = z'1)%G). {
  simpl; unfold Coker_eq; simpl.
  exists 0.
  split; [ apply A | ].
  rewrite Hzero; symmetry.
  apply gr_sub_move_r; symmetry.
  rewrite gr_add_0_l.
  apply (f'_is_inj sf'); [ easy | now apply Hf'₁; exists x1 | ].
  rewrite Hfz'1.
  now symmetry; apply Hf'₁; exists x1.
}
assert (Hzz' : @gr_eq (@Coker A A' a) z'1 z'2). {
  destruct H6 as (zz & Hzz & Hazz).
  simpl; unfold Coker_eq; simpl.
  now exists zz; split.
}
now rewrite Hdx1, Hzz'; symmetry.
Qed.

Theorem d_additive
    {A A' B B' C C'} {f : HomGr A B} {g : HomGr B C} {f' : HomGr A' B'}
    {a : HomGr A A'} {b : HomGr B B'} {c : HomGr C C'} {za' : HomGr Gr1 A'}
    {g₁ f'₁} :
  diagram_commutes f a b f'
  → Im f == Ker g
  → Im za' == Ker f'
  → g₁_prop g c g₁
  → f'₁_prop a b f' g₁ f'₁
  → let d := λ x, f'₁ (Happ b (g₁ x)) in
     ∀ x1 x2, x1 ∈ Ker c → x2 ∈ Ker c → (d (x1 + x2) = d x1 + d x2)%G.
Proof.
intros * Hcff' sf sf' Hg₁ Hf'₁ * Hx1 Hx2.
set (x3 := (x1 + x2)%G).
set (y1 := g₁ x1).
set (y2 := g₁ x2).
set (y3 := g₁ x3).
set (z1 := d x1).
set (z2 := d x2).
set (z3 := d x3).
assert (H1 : (Happ g y1 = x1)%G) by now apply Hg₁; simpl in Hx1.
assert (H2 : (Happ g y2 = x2)%G) by now apply Hg₁; simpl in Hx2.
assert (H3 : (Happ g (y1 + y2)%G = x3)%G). {
  rewrite Hadditive; [ now rewrite H1, H2 | | ].
  -apply (g₁_in_B Hg₁), Hx1.
  -apply (g₁_in_B Hg₁), Hx2.
}
assert (Hy1 : y1 ∈ B) by apply (g₁_in_B Hg₁), Hx1.
assert (Hy2 : y2 ∈ B) by apply (g₁_in_B Hg₁), Hx2.
assert (Hy3 : y3 ∈ B) by (apply (g₁_in_B Hg₁), C; [ apply Hx1 | apply Hx2 ]).
assert (H4 : (y1 + y2 - y3)%G ∈ Ker g). {
  split; [ now apply B; apply B | ].
  rewrite Hadditive; [ | now apply B | now apply B ].
  symmetry; apply gr_sub_move_r.
  rewrite gr_add_0_l, Hinv; [ | easy ].
  rewrite gr_inv_involutive, H3.
  apply Hg₁, C; [ apply Hx1 | apply Hx2 ].
}
assert (Hfx1 : (Happ f' z1 = Happ b y1)%G). {
  now apply Hf'₁; exists x1.
}
assert (Hfx2 : (Happ f' z2 = Happ b y2)%G). {
  now apply Hf'₁; exists x2.
}
assert (Hfx3 : (Happ f' z3 = Happ b y3)%G). {
  unfold z3, y3.
  apply Hf'₁.
  exists x3.
  split; [ now apply (Ker c)| easy ].
}
assert
  (Hfzzz :
     (Happ f' (z1 + z2 - z3) = Happ b y1 + Happ b y2 - Happ b y3)%G). {
  assert (Hz1A' : z1 ∈ A' ∧ z2 ∈ A' ∧ z3 ∈ A'). {
    assert (H : z1 ∈ A' ∧ z2 ∈ A'). {
      split.
      -now apply Hf'₁; exists x1.
      -now apply Hf'₁; exists x2.
    }
    split; [ easy | ].
    split; [ easy | ].
    unfold z3.
    apply Hf'₁.
    exists x3; split; [ now apply (Ker c) | easy ].
  }
  simpl; rewrite Hadditive; [ | now apply A' | now apply A' ].
  apply gr_add_compat.
  -rewrite Hadditive; [ now apply gr_add_compat | easy | easy ].
  -rewrite Hinv; [ now apply gr_inv_compat | easy ].
}
apply sf in H4.
destruct H4 as (z & Hz & Hzf).
assert (Hfz : (Happ f' (z1 + z2 - z3) = Happ f' (Happ a z))%G). {
  rewrite Hfzzz.
  etransitivity.
  -apply gr_add_compat; [ now symmetry; apply b | now symmetry; apply Hinv ].
  -rewrite <- Hadditive; [ | now apply B | now apply B ].
   rewrite <- Hcff'.
   apply b; [ | now apply f | now apply B; apply B ].
   rewrite <- Hzf.
   now apply f.
}
apply (f'_is_inj sf') in Hfz; [ | | now apply a ].
-simpl; unfold Coker_eq; simpl.
 exists (- z).
 split; [ now apply A | ].
 rewrite Hinv; [ | easy ].
 rewrite <- Hfz.
 symmetry; rewrite gr_add_comm.
 rewrite gr_inv_add_distr.
 apply gr_eq_inv_l.
 rewrite gr_inv_add_distr.
 simpl; apply gr_add_compat; [ | easy ].
 rewrite gr_inv_add_distr.
 now do 2 rewrite gr_inv_involutive.
-apply A'.
 +apply A'; [ now apply Hf'₁; exists x1 | now apply Hf'₁; exists x2 ].
 +apply A'.
  apply Hf'₁; exists x3.
  split; [ now apply (Ker c) | easy ].
Qed.

(* 1/ proof exact sequence: Ker a → Ker b → Ker c *)

Theorem exact_sequence_1 {A B C A' B' C'} :
  ∀ (f : HomGr A B) (g : HomGr B C) (f' : HomGr A' B') (g' : HomGr B' C')
     (a : HomGr A A') (b : HomGr B B') (c : HomGr C C') (za' : HomGr Gr1 A')
     (Hcff' : diagram_commutes f a b f') (Hcgg' : diagram_commutes g b c g'),
  Im f == Ker g
  → Im za' == Ker f'
  → Im (HomGr_Ker_Ker a b Hcff') == Ker (HomGr_Ker_Ker b c Hcgg').
Proof.
intros * sf sf'.
split.
+intros y (x & (Hx & Hax) & Hxy).
 split; [ split | ].
 *eapply B; [ apply Hxy | now apply f ].
 *transitivity (Happ b (Happ f x)).
 --apply b; [ | now apply f | now symmetry ].
   eapply gr_mem_compat; [ apply Hxy | now apply f ].
 --rewrite Hcff'.
   transitivity (Happ f' (@gr_zero A')); [ | apply Hzero ].
   apply f'; [ now apply a | apply A' | easy ].
 *now apply sf; exists x.
+intros y ((Hy & Hby) & Hgy).
 assert (H : y ∈ Im f) by now apply sf; split.
 destruct H as (x & Hx & Hxy).
 exists x; split; [ | easy ].
 split; [ easy | ].
 specialize (proj2 sf' (Happ a x)) as H1.
 assert (H3 : Happ a x ∈ Ker f'). {
   split; [ now apply a | ].
   rewrite <- Hcff'.
   transitivity (Happ b y); [ | easy ].
   apply b; [ now apply f | easy | easy ].
 }
 specialize (H1 H3).
 destruct H1 as (z & _ & Hzz).
 rewrite <- Hzz.
 destruct z.
 apply Hzero.
Qed.

(* 2/ proof exact sequence: Ker b → Ker c → CoKer a *)

Theorem exact_sequence_2 {A B C A' B' C'} :
  ∀ (f : HomGr A B) (g : HomGr B C) (f' : HomGr A' B') (g' : HomGr B' C')
    (a : HomGr A A') (b : HomGr B B') (c : HomGr C C') (za' : HomGr Gr1 A')
    (g₁ : gr_set (Ker c) → gr_set B) (f'₁ : gr_set B' → gr_set (Coker a))
    (sf : Im f == Ker g) (sf' : Im za' == Ker f')
    (Hcff' : diagram_commutes f a b f')
    (Hcgg' : diagram_commutes g b c g')
    (Hg₁ : g₁_prop g c g₁) (Hf'₁ : f'₁_prop a b f' g₁ f'₁),
 let d := λ x : gr_set (Ker c), f'₁ (Happ b (g₁ x)) in
 ∀ (dm : HomGr (Ker c) (Coker a)), Happ dm = d
 → Im (HomGr_Ker_Ker b c Hcgg') == Ker dm.
Proof.
intros *.
intros sf sf' Hcff' Hcgg' Hg₁ Hf'₁ d.
intros * Hd.
split.
-intros x (y & (Hy & Hay) & Hyx).
 split; [ split | ].
 +eapply C; [ apply Hyx | now apply g ].
 +specialize (Hcgg' y) as H1.
  transitivity (Happ c (Happ g y)).
  *eapply c; [ | now apply g | now apply C ].
   eapply C; [ apply Hyx | now apply g ].
  *rewrite H1.
   transitivity (Happ g' (@gr_zero B')); [ | apply Hzero ].
   apply g'; [ now apply b | apply B' | easy ].
 +simpl in Hyx.
  assert (Hgy : Happ g y ∈ Ker c). {
    split; [ now apply g | ].
    rewrite Hcgg'.
    etransitivity; [ | apply Hzero ].
    apply g'; [ now apply b | apply B' | easy ].
  }
  assert (Hxk : x ∈ Ker c). {
    assert (Hx : x ∈ C). {
      eapply gr_mem_compat; [ apply Hyx | now apply g ].
    }
    split; [ easy | ].
    etransitivity; [ | apply Hgy ].
    apply c; [ easy | now apply g | now symmetry ].
  }
  assert (Hyk : g₁ x - y ∈ Ker g). {
    split.
    -apply B; [ apply (g₁_in_B Hg₁), Hxk | now apply B ].
    -rewrite Hadditive; [ | apply (g₁_in_B Hg₁), Hxk | now apply B ].
     etransitivity.
     *apply gr_add_compat; [ apply Hg₁, Hxk | ].
      now simpl; apply Hinv.
     *apply gr_sub_move_r; rewrite <- Hyx.
      symmetry; apply gr_add_0_l.
  }
  apply sf in Hyk.
  destruct Hyk as (z & Hz & Haz).
  assert (Hdx : (d x = Happ a z)%G). {
    apply (f'c_is_inj sf'); [ | now apply a | ].
    -now apply (d_mem_compat Hf'₁).
    -etransitivity; [ apply Hf'₁; now exists x | ].
     rewrite <- Hcff'; symmetry.
     etransitivity.
     +apply Happ_compat; [ | | apply Haz ].
      *apply Hmem_compat, Hz.
      *apply B; [ apply (g₁_in_B Hg₁), Hxk | now apply B ].
     +rewrite Hadditive; [ | apply (g₁_in_B Hg₁), Hxk | now apply B ].
      etransitivity.
      *apply gr_add_compat; [ easy | now simpl; apply Hinv ].
      *etransitivity.
      --apply gr_add_compat; [ easy | apply gr_inv_compat, Hay ].
      --rewrite gr_sub_0_r.
        apply b; [ apply (g₁_in_B Hg₁), Hxk | apply (g₁_in_B Hg₁), Hxk | ].
        easy.
  }
  rewrite Hd.
  simpl; rewrite Hdx.
  exists z; split; [ easy | ].
  now simpl; rewrite gr_sub_0_r.
-intros x (Hx & z & Hz & Haz).
 rewrite Hd in Haz.
 simpl in x, Haz.
 move z before x; move Hz before Hx.
 rewrite gr_sub_0_r in Haz.
 enough (∃ y, (y ∈ B ∧ (Happ b y = 0)%G) ∧ (Happ g y = x)%G) by easy.
 apply (Happ_compat _ _ f') in Haz; [ | now apply a | ].
 +rewrite <- Hcff' in Haz.
  exists (g₁ x - Happ f z).
  split; [ split | ].
  *apply B; [ apply Hg₁, Hx | now apply B, f ].
  *rewrite Hadditive; [ | apply Hg₁, Hx | now apply B, f ].
   etransitivity.
  --apply gr_add_compat; [ easy | now apply Hinv, f ].
  --apply gr_sub_move_r; rewrite gr_add_0_l; symmetry.
    now rewrite Haz; apply Hf'₁; exists x.
  *rewrite Hadditive; [ | apply Hg₁, Hx | now apply B, f ].
  --etransitivity.
   ++apply gr_add_compat; [ easy | now apply Hinv, f ].
   ++apply gr_sub_move_l.
     etransitivity; [ apply Hg₁, Hx | ].
     rewrite <- gr_add_0_l at 1.
     apply gr_add_compat; [ | easy ].
     enough (H1 : Happ f z ∈ Ker g) by now simpl in H1.
     now apply sf; exists z.
 +eapply gr_mem_compat; [ apply Haz | now apply a ].
Qed.

(* 3/ proof exact sequence: Ker c → CoKer a → Coker b *)

Theorem exact_sequence_3 {A B C A' B' C'} :
  ∀ (f : HomGr A B) (g : HomGr B C) (f' : HomGr A' B') (g' : HomGr B' C')
    (a : HomGr A A') (b : HomGr B B') (c : HomGr C C') (za' : HomGr Gr1 A')
    (Hcff' : diagram_commutes f a b f')
    (Hcgg' : diagram_commutes g b c g')
    (sf : Im f == Ker g) (sf' : Im za' == Ker f') (sg' : Im f' == Ker g')
    (g₁ : gr_set (Ker c) → gr_set B)
    (f'₁ : gr_set B' → gr_set (Coker a))
    (Hg₁ : g₁_prop g c g₁)
    (Hf'₁ : f'₁_prop a b f' g₁ f'₁),
  let d := λ x : gr_set (Ker c), f'₁ (Happ b (g₁ x)) in
  ∀ (dm : HomGr (Ker c) (Coker a)), Happ dm = d →
  Im dm == Ker (HomGr_Coker_Coker a b Hcff').
Proof.
intros *.
intros Hcgg' sf sf' sg' * Hg₁ Hf'₁ * Hdm.
split.
-intros z' Hz'.
 destruct Hz' as (x & Hx & z & Hz & Haz).
 move z before x.
 rewrite Hdm in Haz.
 simpl in Haz.
 assert (Hz' : z' ∈ A'). {
   apply gr_mem_compat with (x := d x - Happ a z).
   -transitivity (d x - (d x - z')); simpl.
    +apply gr_add_compat; [ easy | now apply gr_inv_compat ].
    +apply gr_sub_move_l.
     rewrite gr_add_assoc; symmetry.
     etransitivity; [ | apply gr_add_0_r ].
     apply gr_add_compat; [ easy | ].
     apply gr_add_inv_l.
   -apply A'; [ now apply Hf'₁; exists x | now apply A', a ].
 }
 simpl; split; [ easy | ].
 unfold Coker_eq; simpl.
 enough (H : ∃ y, y ∈ B ∧ (Happ b y = Happ f' z')%G). {
   destruct H as (y & Hy & Hby).
   exists y.
   split; [ easy | now rewrite gr_sub_0_r ].
 }
 simpl in z'.
 exists (g₁ x - Happ f z).
 split.
 +apply B; [ apply Hg₁, Hx | now apply B, f ].
 +apply (Happ_compat _ _ f') in Haz; [ | now apply a | ].
  *rewrite Hadditive; [ | apply Hg₁, Hx | now apply B, f ].
  --etransitivity.
   ++apply gr_add_compat; [ easy | now apply Hinv, f ].
   ++etransitivity.
    **apply gr_add_compat; [ easy | ].
      apply gr_inv_compat, Hcff'.
    **apply gr_sub_move_r.
      etransitivity; [ now symmetry; apply Hf'₁; exists x | ].
      fold (d x).
      apply gr_sub_move_l.
      etransitivity.
    ---apply gr_add_compat; [ easy | now symmetry; apply Hinv ].
    ---rewrite <- Hadditive; [ now symmetry | | now apply A' ].
       now apply Hf'₁; exists x.
  *apply A'; [ now apply Hf'₁; exists x | now apply A' ].
-intros z' (Hz' & y & Hy & Hby).
 simpl in z', Hz', Hby.
 rewrite gr_sub_0_r in Hby.
 simpl; unfold Coker_eq; simpl.
 rewrite Hdm.
 enough (H :
  ∃ x, x ∈ C ∧ (Happ c x = 0)%G ∧
  ∃ z, z ∈ A ∧ (Happ a z = d x - z')%G). {
   destruct H as (x & Hx).
   now exists x.
 }
 exists (Happ g y).
 split; [ now apply g | ].
 split.
 +rewrite Hcgg'.
  etransitivity.
  *apply Happ_compat; [ now apply b | | apply Hby ].
   now apply f'.
  *assert (H : Happ f' z' ∈ Im f') by now exists z'.
   now apply sg' in H; simpl in H.
 +assert (H : g₁ (Happ g y) - y ∈ Ker g). {
    split.
    -apply B; [ now apply Hg₁, g | now apply B ].
    -rewrite Hadditive; [ | now apply Hg₁, g | now apply B ].
     rewrite <- gr_add_inv_r.
     apply gr_add_compat; [ now apply Hg₁, g | now apply Hinv ].
  }
  apply sf in H.
  destruct H as (z & Hz & Hfz).
  exists z; split; [ easy | ].
  apply (Happ_compat _ _ b) in Hfz; [ | now apply f | ].
  *rewrite Hadditive in Hfz; [ | now apply Hg₁, g | now apply B ].
   rewrite Hcff' in Hfz.
  --apply (f'_is_inj sf'); [ now apply a | | ].
   ++apply A'; [ | now apply A' ].
     apply Hf'₁.
     exists (Happ g y); split; [ | easy ].
     split; [ now apply g | ].
     rewrite Hcgg'.
     etransitivity.
    **apply Happ_compat; [ now apply b | | apply Hby ].
      now apply f'.
    **assert (H : Happ f' z' ∈ Im f') by (exists z'; easy).
      now apply sg' in H; simpl in H.
   ++rewrite Hfz.
     symmetry; simpl; rewrite Hadditive; [ | | now apply A' ].
    **apply gr_add_compat.
    ---apply Hf'₁.
       exists (Happ g y); split; [ | easy ].
       split; [ now apply g | ].
       rewrite Hcgg'.
       etransitivity.
     +++apply Happ_compat; [ now apply b | | apply Hby ].
        now apply f'.
     +++assert (H : Happ f' z' ∈ Im f') by (exists z'; easy).
        now apply sg' in H; simpl in H.
    ---rewrite Hinv; [ | easy ].
       rewrite Hinv; [ | easy ].
       apply gr_inv_compat.
       now symmetry.
    **apply Hf'₁; exists (Happ g y); split; [ | easy ].
      split; [ now apply g | ].
      rewrite Hcgg'.
      etransitivity.
    ---apply Happ_compat; [ now apply b | | apply Hby ].
       now apply f'.
    ---assert (H : Happ f' z' ∈ Im f') by (exists z'; easy).
       now apply sg' in H; simpl in H.
  *apply B; [ now apply Hg₁, g | now apply B ].
Qed.

(* 4/ proof exact sequence: CoKer a → CoKer b → Coker c *)

Theorem exact_sequence_4 {A B C A' B' C'} :
  ∀ (f : HomGr A B) (g : HomGr B C) (f' : HomGr A' B') (g' : HomGr B' C')
    (a : HomGr A A') (b : HomGr B B') (c : HomGr C C')
    (Hcff' : diagram_commutes f a b f')
    (Hcgg' : diagram_commutes g b c g')
    (sg' : Im f' == Ker g')
    (g₁ : gr_set (Ker c) → gr_set B)
    (Hg₁ : g₁_prop g c g₁),
  Im (HomGr_Coker_Coker a b Hcff') == Ker (HomGr_Coker_Coker b c Hcgg').
Proof.
intros.
split.
-simpl.
 intros y' (z' & Hz' & y & Hy & Hby).
 simpl in Hby.
 assert (Hb' : y' ∈ B'). {
   symmetry in Hby.
   apply gr_sub_move_r in Hby.
   rewrite gr_add_comm in Hby.
   apply gr_sub_move_r in Hby.
   rewrite <- Hby.
   apply B'; [ now apply f' | now apply B', b ].
 }
 split; [ easy | ].
 unfold Coker_eq; simpl.
 enough (H : ∃ x, x ∈ C ∧ (Happ c x = Happ g' y')%G). {
   destruct H as (x & Hx & Hcx).
   exists x; split; [ easy | ].
   rewrite Hcx; symmetry.
   apply gr_sub_0_r.
 }
 exists (- Happ g y).
 split; [ now apply C, g | ].
 rewrite Hinv, Hcgg'; [ | now apply g ].
 apply gr_eq_inv_l.
 rewrite <- Hinv; [ | easy ].
 symmetry.
 transitivity (Happ g' (Happ f' z' - y')).
 +rewrite Hadditive; [ | now apply f' | now apply B' ].
  rewrite <- gr_add_0_l at 1.
  apply gr_add_compat; [ | easy ].
  symmetry.
  assert (H : Happ f' z' ∈ Im f') by (exists z'; easy).
  now apply sg' in H; simpl in H.
 +apply g'; [ | now apply b | now symmetry ].
  apply B'; [ now apply f' | now apply B' ].
-simpl; intros y' (Hy' & x & Hx & Hcx).
 simpl in Hcx; rewrite gr_sub_0_r in Hcx.
 unfold Coker_eq; simpl.
 enough (H : ∃ y z', y ∈ B ∧ z' ∈ A' ∧ (Happ b y = Happ f' z' - y')%G). {
   destruct H as (y & z' & Hz' & Hy & Hby).
   exists z'; split; [ easy | ].
   now exists y.
 }
 assert (Hby : y' - Happ b (g₁ x) ∈ Ker g'). {
   split.
   -apply B'; [ easy | now apply B', b, Hg₁ ].
   -rewrite Hadditive; [ | easy | now apply B', b, Hg₁ ].
    rewrite <- Hcx, Hinv; [ | now apply b, Hg₁ ].
    rewrite <- Hcgg'.
    etransitivity; [ | apply gr_add_inv_r ].
    apply gr_add_compat; [ easy | ].
    apply gr_inv_compat.
    apply Happ_compat; [ now apply g, Hg₁ | apply Hx | now apply Hg₁ ].
 }
 apply sg' in Hby.
 destruct Hby as (z' & Hz' & Hfz').
 exists (- g₁ x), z'.
 split; [ now apply B, Hg₁ | ].
 split; [ easy | ].
 rewrite Hfz', gr_add_comm, <- gr_add_assoc, gr_add_inv_l, gr_add_0_l.
 now apply Hinv, Hg₁.
Qed.

(* The snake lemma
                f      g       cz
            A------>B------>C------>0
            |       |       |
           a|      b|      c|
            |       |       |
            v       v       v
     0----->A'----->B'----->C'
       za'      f'      g'

  If 1/ the diagram is commutative,
     2/ (f, g, cz) and (za', f', g') are exact sequences,
  Then
     there exists a morphism d from Ker c to Coker a, such that
     Ker a→Ker b→Ker c→Coker a→Coker b→Coker c is an exact sequence.
*)

Lemma snake :
  ∀ (A B C A' B' C' : AbGroup)
     (f : HomGr A B) (g : HomGr B C)
     (f' : HomGr A' B') (g' : HomGr B' C')
     (a : HomGr A A') (b : HomGr B B') (c : HomGr C C')
     (cz : HomGr C Gr1) (za' : HomGr Gr1 A'),
  Decidable_Membership * Choice
  → diagram_commutes f a b f'
  → diagram_commutes g b c g'
  → exact_sequence [f; g; cz]
  → exact_sequence [za'; f'; g']
  → ∃ (fk : HomGr (Ker a) (Ker b)) (gk : HomGr (Ker b) (Ker c))
        (fk' : HomGr (Coker a) (Coker b)) (gk' : HomGr (Coker b) (Coker c)),
     ∃ (d : HomGr (Ker c) (Coker a)),
        exact_sequence (Seq fk (Seq gk (Seq d (Seq fk' (Seq gk' SeqEnd))))).
Proof.
intros *.
intros (mem_dec, choice) Hcff' Hcgg' s s'.
exists (HomGr_Ker_Ker a b Hcff').
exists (HomGr_Ker_Ker b c Hcgg').
exists (HomGr_Coker_Coker a b Hcff').
exists (HomGr_Coker_Coker b c Hcgg').
destruct s as (sf & sg & _).
destruct s' as (sf' & sg' & _).
specialize (g_is_surj c mem_dec sg) as H1.
specialize (choice _ _ _ H1) as H; destruct H as (g₁, Hg₁).
specialize (exists_B'_to_Coker_a a mem_dec sg' Hg₁ Hcgg') as H2.
specialize (choice _ _ _ H2) as H; destruct H as (f'₁, Hf'₁).
fold (g₁_prop g c g₁) in Hg₁.
fold (f'₁_prop a b f' g₁ f'₁) in Hf'₁.
move f'₁ before g₁.
clear H1 H2.
set (d := λ x, f'₁ (Happ b (g₁ x))).
set
  (dm :=
   {| Happ := d;
      Hmem_compat := d_mem_compat Hf'₁;
      Happ_compat := d_app_compat Hcff' Hcgg' sf sf' sg' Hg₁ Hf'₁;
      Hadditive := d_additive Hcff' sf sf' Hg₁ Hf'₁ |}).
exists dm.
split; [ now eapply exact_sequence_1 | ].
split; [ now eapply exact_sequence_2; try easy | ].
split; [ now eapply exact_sequence_3; try easy | ].
split; [ eapply exact_sequence_4; try easy; apply Hg₁ | easy ].
Qed.

Check snake.

(*
Print Assumptions snake.
*)
