(* Abelian groups and Homomorphisms *)

Require Import Utf8.
Require Import Setoid Morphisms.

Reserved Notation "x '∈' S" (at level 60).
Reserved Notation "x '≡' y" (at level 70).

(* Abelian Groups.

   Notes:

   -sets in groups are predicates (naive theory of sets); a value of type
    gr_set is not necessarily in the group set. To be in the group set, it
    must satisfy the predicate gr_mem, which is later syntaxified by the
    usual symbol ∈. This allows to create subgroups by changing gr_mem.

   -group sets are setoids: there is a specific equality (gr_eq) which is
    compatible with membership (gr_mem_compat), addition (gr_add_compat),
    and opposite (gr_opp_compat). This allows to define quotient groups,
    for example in cokernets, by changing this equality.
*)

Record AbGroup :=
  { (* data *)
    gr_set : Type;
    gr_mem : gr_set → Prop where "x ∈ G" := (gr_mem x);
    gr_eq : gr_set → gr_set → Prop where "x ≡ y" := (gr_eq x y);
    gr_zero : gr_set where "0" := (gr_zero);
    gr_add : gr_set → gr_set → gr_set where "x + y" := (gr_add x y);
    gr_opp : gr_set → gr_set where "- x" := (gr_opp x);
    (* properties *)
    gr_zero_mem : 0 ∈ G;
    gr_add_mem : ∀ x y, x ∈ G → y ∈ G → x + y ∈ G;
    gr_add_0_l : ∀ x, 0 + x ≡ x;
    gr_add_assoc : ∀ x y z, (x + y) + z ≡ x + (y + z);
    gr_opp_mem : ∀ x, x ∈ G → - x ∈ G;
    gr_add_opp_r : ∀ x, x + (- x) ≡ 0;
    gr_add_comm : ∀ x y, x + y ≡ y + x;
    gr_equiv : Equivalence gr_eq;
    gr_mem_compat : ∀ x y, x ≡ y → x ∈ G → y ∈ G;
    gr_add_compat : ∀ x y x' y', x ≡ y → x' ≡ y' → x + x' ≡ y + y';
    gr_opp_compat : ∀ x y, x ≡ y → - x ≡ - y }.

(* coq stuff: implicit and renamed arguments *)

Arguments gr_eq [_].
Arguments gr_zero [_].
Arguments gr_add [_].
Arguments gr_opp [_].
Arguments gr_zero_mem G : rename.
Arguments gr_add_mem G : rename.
Arguments gr_add_0_l G : rename.
Arguments gr_add_assoc G : rename.
Arguments gr_opp_mem G : rename.
Arguments gr_add_opp_r G : rename.
Arguments gr_add_comm G : rename.
Arguments gr_equiv G : rename.
Arguments gr_mem_compat G : rename.
Arguments gr_add_compat G : rename.
Arguments gr_opp_compat G : rename.

(* syntaxes for expressions for groups elements and sets *)

Delimit Scope group_scope with G.

Notation "0" := (gr_zero) : group_scope.
Notation "a = b" := (gr_eq a b) : group_scope.
Notation "a ≠ b" := (¬ gr_eq a b) : group_scope.
Notation "a + b" := (gr_add a b) : group_scope.
Notation "a - b" := (gr_add a (gr_opp b)) : group_scope.
Notation "- a" := (gr_opp a) : group_scope.

Notation "x '∈' S" := (gr_mem S x) (at level 60).
Notation "x '∉' S" := (¬ gr_mem S x) (at level 60).

Open Scope group_scope.

(* Homomorphism between groups *)

Record HomGr (A B : AbGroup) :=
  { Happ : gr_set A → gr_set B;
    Hmem_compat : ∀ x, x ∈ A → Happ x ∈ B;
    Happ_compat : ∀ x y,
      x ∈ A → y ∈ A → (x = y)%G → (Happ x = Happ y)%G;
    Hadditive : ∀ x y,
      x ∈ A → y ∈ A → (Happ (x + y) = Happ x + Happ y)%G }.

(* coq stuff: implicit and renamed arguments *)

Arguments Happ [A] [B].
Arguments Hmem_compat _ _ f : rename.
Arguments Happ_compat _ _ f : rename.
Arguments Hadditive _ _ f : rename.

(* Equality (gr_eq) of groups elements is an equivalence relation *)

Add Parametric Relation {G} : (gr_set G) (@gr_eq G)
 reflexivity proved by (@Equivalence_Reflexive _ (@gr_eq G) (@gr_equiv G))
 symmetry proved by (@Equivalence_Symmetric _ (@gr_eq G) (@gr_equiv G))
 transitivity proved by (@Equivalence_Transitive _ (@gr_eq G) (@gr_equiv G))
 as gr_eq_rel.

(* Coq "Morphisms": they allow to use "rewrite" in expressions containing
   opposites (-), additions (+) and memberships (∈) *)

Instance gr_opp_morph {G} : Proper (@gr_eq G ==> @gr_eq G) (@gr_opp G).
Proof.
intros x y Hxy.
now apply gr_opp_compat.
Qed.

Instance gr_add_morph {G} :
  Proper (@gr_eq G ==> @gr_eq G ==> @gr_eq G) (@gr_add G).
Proof.
intros x y Hxy x' y' Hxy'.
now apply gr_add_compat.
Qed.

Instance gr_mem_morph {G} : Proper (@gr_eq G ==> iff) (@gr_mem G).
Proof.
intros x y Hxy.
split; intros H.
-eapply gr_mem_compat; [ apply Hxy | easy ].
-eapply gr_mem_compat; [ symmetry; apply Hxy | easy ].
Qed.

(*
Trying to make a (coq) morphism when there are hypotheses.
  E.g. Happ_compat : x ∈ A → y ∈ A → (x = y)%G → (Happ f x = Happ f y)%G
But it does not work. The rewrite does not apply.
See https://github.com/coq/coq/issues/7708
Seems that this kind of morphism is not implemented in Coq.

Definition gr_elem A := { a : gr_set A | a ∈ A }.
Definition gr_mem_eq A (x y : gr_elem A) := (proj1_sig x = proj1_sig y)%G.

Theorem gr_mem_refl {A} : Reflexive (gr_mem_eq A).
Proof.
intros (x & Hx).
now unfold gr_mem_eq.
Qed.

Theorem gr_mem_symm {A} : Symmetric (gr_mem_eq A).
Proof.
intros (x & Hx) (y & Hy).
unfold gr_mem_eq; simpl; intros Hxy.
now symmetry.
Qed.

Theorem gr_mem_trans {A} : Transitive (gr_mem_eq A).
Proof.
intros (x & Hx) (y & Hy) (z & Hz).
unfold gr_mem_eq; simpl; intros Hxy Hyz.
now transitivity y.
Qed.

Add Parametric Relation {G} : _ (@gr_mem_eq G)
 reflexivity proved by gr_mem_refl
 symmetry proved by gr_mem_symm
 transitivity proved by gr_mem_trans
 as gr_mem_rel.

Add Parametric Morphism {G H} : (λ f e, Happ f (proj1_sig e))
  with signature eq ==> gr_mem_eq G ==> @gr_eq H
  as M_app_morph.
Proof.
intros f (x, Hx) (y, Hy) Hxy.
unfold gr_mem_eq in Hxy; simpl in Hxy.
now apply Happ_compat.
Qed.
*)

(* Miscellaneous theorems in groups *)

Theorem gr_add_0_r : ∀ G (x : gr_set G), (x + 0 = x)%G.
Proof.
intros.
rewrite gr_add_comm.
apply gr_add_0_l.
Qed.

Theorem gr_add_opp_l : ∀ G (x : gr_set G), (- x + x = 0)%G.
Proof.
intros.
rewrite gr_add_comm.
apply gr_add_opp_r.
Qed.

Theorem gr_opp_zero : ∀ G, (- 0 = @gr_zero G)%G.
Proof.
intros.
rewrite <- gr_add_0_l.
apply gr_add_opp_r.
Qed.

Theorem gr_sub_0_r : ∀ G (x : gr_set G), (x - 0 = x)%G.
Proof.
intros.
symmetry; rewrite <- gr_add_0_r at 1.
apply gr_add_compat; [ easy | now rewrite gr_opp_zero ].
Qed.

Theorem gr_sub_move_r : ∀ G (x y z : gr_set G),
  (x - y = z)%G ↔ (x = z + y)%G.
Proof.
intros.
split; intros Hxyz.
-now rewrite <- Hxyz, gr_add_assoc, gr_add_opp_l, gr_add_0_r.
-now rewrite Hxyz, gr_add_assoc, gr_add_opp_r, gr_add_0_r.
Qed.

Theorem gr_sub_move_l : ∀ G (x y z : gr_set G),
  (x - y = z)%G ↔ (x = y + z)%G.
Proof.
intros.
split; intros Hxyz.
-now rewrite <- Hxyz, gr_add_comm, gr_add_assoc, gr_add_opp_l, gr_add_0_r.
-now rewrite Hxyz, gr_add_comm, <- gr_add_assoc, gr_add_opp_l, gr_add_0_l.
Qed.

Theorem gr_opp_add_distr : ∀ G (x y : gr_set G), (- (x + y) = - x - y)%G.
Proof.
intros *.
symmetry.
apply gr_sub_move_r.
rewrite <- gr_add_0_l.
apply gr_sub_move_r.
symmetry; rewrite gr_add_assoc.
symmetry.
apply gr_sub_move_r.
rewrite gr_add_0_l.
apply gr_opp_compat, gr_add_comm.
Qed.

Theorem gr_opp_involutive : ∀ G (x : gr_set G), (- - x = x)%G.
Proof.
intros.
transitivity (- - x + (- x + x))%G.
-rewrite <- gr_add_0_r at 1.
 apply gr_add_compat; [ easy | ].
 now rewrite gr_add_opp_l.
-now rewrite <- gr_add_assoc, gr_add_opp_l, gr_add_0_l.
Qed.

Theorem gr_eq_opp_l : ∀ G (x y : gr_set G), (- x = y)%G ↔ (x = - y)%G.
Proof.
intros.
split; intros Hxy.
-rewrite <- Hxy; symmetry; apply gr_opp_involutive.
-rewrite Hxy; apply gr_opp_involutive.
Qed.

(* Theorems on homomorphisms *)

Theorem Hzero : ∀ A B (f : HomGr A B), (Happ f 0 = 0)%G.
Proof.
intros.
assert (H1 : (@gr_zero A + 0 = 0)%G) by apply A.
assert (H2 : (Happ f 0 + Happ f 0 = Happ f 0)%G). {
  rewrite <- Hadditive; [ | apply A | apply A ].
  apply f; [ apply A; apply A | apply A | easy ].
}
assert (H3 : (Happ f 0 + Happ f 0 - Happ f 0 = Happ f 0 - Happ f 0)%G). {
  apply gr_add_compat; [ apply H2 | easy ].
}
assert (H4 : (Happ f 0 + Happ f 0 - Happ f 0 = 0)%G). {
  rewrite H3; apply gr_add_opp_r.
}
rewrite <- H4.
now rewrite gr_add_assoc, gr_add_opp_r, gr_add_0_r.
Qed.

Theorem Hopp : ∀ A B (f : HomGr A B) x,
  x ∈ A → (Happ f (- x) = - Happ f x)%G.
Proof.
intros * Hx.
assert (H1 : (x - x = 0)%G) by apply A.
assert (H2 : (Happ f (x - x) = Happ f 0)%G). {
  apply Happ_compat; [ now apply A, A | apply A | apply H1 ].
}
assert (H3 : (Happ f x + Happ f (- x) = Happ f 0)%G). {
  rewrite <- H2.
  symmetry; apply Hadditive; [ easy | now apply A ].
}
assert (H4 : (Happ f x + Happ f (- x) = 0)%G). {
  rewrite H3; apply Hzero.
}
symmetry; rewrite <- gr_add_0_l.
apply gr_sub_move_l.
now symmetry.
Qed.

(* Images *)

Theorem Im_zero_mem {G H} : ∀ (f : HomGr G H),
  ∃ a : gr_set G, a ∈ G ∧ (Happ f a = 0)%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | apply Hzero ].
Qed.

Theorem Im_add_mem {G H} : ∀ f (x y : gr_set H),
  (∃ a : gr_set G, a ∈ G ∧ (Happ f a = x)%G)
  → (∃ a : gr_set G, a ∈ G ∧ (Happ f a = y)%G)
  → ∃ a : gr_set G, a ∈ G ∧ (Happ f a = x + y)%G.
Proof.
intros f y y' (x & Hxg & Hx) (x' & Hx'g & Hx').
exists (gr_add x x').
split; [ now apply G | ].
rewrite Hadditive; [ | easy | easy ].
now apply gr_add_compat.
Qed.

Theorem Im_opp_mem {G H} : ∀ (f : HomGr G H) (x : gr_set H),
  (∃ a : gr_set G, a ∈ G ∧ (Happ f a = x)%G)
  → ∃ a : gr_set G, a ∈ G ∧ (Happ f a = - x)%G.
Proof.
intros f x (y & Hy & Hyx).
exists (gr_opp y).
split; [ now apply gr_opp_mem | ].
rewrite <- Hyx.
now apply Hopp.
Qed.

Theorem Im_mem_compat {G H} : ∀ f (x y : gr_set H),
  (x = y)%G
  → (∃ a, a ∈ G ∧ (Happ f a = x)%G)
  → ∃ a, a ∈ G ∧ (Happ f a = y)%G.
intros * Hxy (z & Hz & Hfz).
exists z.
split; [ easy | now rewrite Hfz ].
Qed.

Definition Im {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero;
     gr_eq := @gr_eq H;
     gr_mem := λ b, ∃ a, a ∈ G ∧ (Happ f a = b)%G;
     gr_add := @gr_add H;
     gr_opp := @gr_opp H;
     gr_zero_mem := Im_zero_mem f;
     gr_add_mem := Im_add_mem f;
     gr_add_0_l := gr_add_0_l H;
     gr_add_assoc := gr_add_assoc H;
     gr_opp_mem := Im_opp_mem f;
     gr_add_opp_r := gr_add_opp_r H;
     gr_add_comm := gr_add_comm H;
     gr_equiv := gr_equiv H;
     gr_mem_compat := Im_mem_compat f;
     gr_add_compat := gr_add_compat H;
     gr_opp_compat := gr_opp_compat H |}.

(* Kernels *)

Theorem Ker_zero_mem {G H} : ∀ (f : HomGr G H), 0%G ∈ G ∧ (Happ f 0 = 0)%G.
Proof.
intros f.
split; [ apply gr_zero_mem | apply Hzero ].
Qed.

Theorem Ker_add_mem {G H} : ∀ (f : HomGr G H) (x y : gr_set G),
  x ∈ G ∧ (Happ f x = 0)%G
  → y ∈ G ∧ (Happ f y = 0)%G → (x + y)%G ∈ G ∧ (Happ f (x + y) = 0)%G.
Proof.
intros f x x' (Hx, Hfx) (Hx', Hfx').
split; [ now apply gr_add_mem | ].
rewrite Hadditive; [ | easy | easy ].
rewrite Hfx, Hfx'.
apply gr_add_0_r.
Qed.

Theorem Ker_opp_mem {G H} : ∀ (f : HomGr G H) (x : gr_set G),
  x ∈ G ∧ (Happ f x = 0)%G → (- x)%G ∈ G ∧ (Happ f (- x) = 0)%G.
Proof.
intros f x (Hx & Hfx).
split; [ now apply gr_opp_mem | ].
rewrite Hopp; [ | easy ].
rewrite Hfx.
apply gr_opp_zero.
Qed.

Theorem Ker_mem_compat {G H} : ∀ (f : HomGr G H) x y,
  (x = y)%G → x ∈ G ∧ (Happ f x = 0)%G → y ∈ G ∧ (Happ f y = 0)%G.
Proof.
intros * Hxy (ax, Hx).
split.
-eapply gr_mem_compat; [ apply Hxy | easy ].
-rewrite <- Hx.
 apply f; [ | easy | easy ].
 now rewrite <- Hxy.
Qed.

Definition Ker {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set G;
     gr_zero := gr_zero;
     gr_eq := @gr_eq G;
     gr_mem := λ a, a ∈ G ∧ (Happ f a = gr_zero)%G;
     gr_add := @gr_add G;
     gr_opp := @gr_opp G;
     gr_zero_mem := Ker_zero_mem f;
     gr_add_mem := Ker_add_mem f;
     gr_add_0_l := gr_add_0_l G;
     gr_add_assoc := gr_add_assoc G;
     gr_opp_mem := Ker_opp_mem f;
     gr_add_opp_r := gr_add_opp_r G;
     gr_add_comm := gr_add_comm G;
     gr_equiv := gr_equiv G;
     gr_mem_compat := Ker_mem_compat f;
     gr_add_compat := gr_add_compat G;
     gr_opp_compat := gr_opp_compat G |}.

(* Cokernels

   x ∈ Coker f ↔ x ∈ H/Im f
   quotient group is H with setoid, i.e. set with its own equality *)

Definition Coker_eq {G H} (f : HomGr G H) x y := (x - y)%G ∈ Im f.

Theorem Coker_add_0_l {G H} : ∀ (f : HomGr G H) x, Coker_eq f (0 + x)%G x.
Proof.
intros.
unfold Coker_eq.
exists 0%G.
split; [ apply gr_zero_mem | ].
rewrite gr_add_0_l, gr_add_opp_r.
simpl; apply Hzero.
Qed.

Theorem Coker_add_assoc {G H} : ∀ (f : HomGr G H) x y z,
  Coker_eq f (x + y + z)%G (x + (y + z))%G.
Proof.
intros.
unfold Coker_eq.
exists 0%G.
split; [ apply gr_zero_mem | ].
rewrite Hzero.
symmetry; simpl.
apply gr_sub_move_r.
rewrite gr_add_0_l.
apply gr_add_assoc.
Qed.

Theorem Coker_add_opp_r {G H} : ∀ (f : HomGr G H) x, Coker_eq f (x - x)%G 0%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | ].
now rewrite Hzero, gr_add_opp_r, gr_sub_0_r.
Qed.

Theorem Coker_add_comm {G H} : ∀ (f : HomGr G H) x y,
  Coker_eq f (x + y)%G (y + x)%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | ].
rewrite Hzero.
symmetry.
simpl; apply gr_sub_move_l.
now rewrite gr_add_0_r, gr_add_comm.
Qed.

Theorem Coker_eq_refl {G H} (f : HomGr G H) : Reflexive (Coker_eq f).
Proof.
intros x.
exists 0%G.
split; [ apply gr_zero_mem | ].
rewrite gr_add_opp_r.
simpl; apply Hzero.
Qed.

Theorem Coker_eq_symm {G H} (f : HomGr G H) : Symmetric (Coker_eq f).
Proof.
intros x y Hxy.
destruct Hxy as (z & Hz & Hfz).
exists (- z)%G.
split; [ now apply gr_opp_mem | ].
rewrite Hopp; [ | easy ].
rewrite Hfz.
simpl; rewrite gr_opp_add_distr, gr_add_comm.
apply gr_add_compat; [ | easy ].
apply gr_opp_involutive.
Qed.

Theorem Coker_eq_trans {G H} (f : HomGr G H) : Transitive (Coker_eq f).
Proof.
intros x y z Hxy Hyz.
simpl in Hxy, Hyz.
destruct Hxy as (t & Ht & Hft).
destruct Hyz as (u & Hu & Hfu).
exists (t + u)%G.
split; [ now apply gr_add_mem | ].
rewrite Hadditive; [ | easy | easy ].
rewrite Hft, Hfu.
simpl; rewrite gr_add_assoc.
apply gr_add_compat; [ easy | ].
now rewrite <- gr_add_assoc, gr_add_opp_l, gr_add_0_l.
Qed.

Theorem Coker_equiv {G H} : ∀ (f : HomGr G H), Equivalence (Coker_eq f).
Proof.
intros.
unfold Coker_eq; split.
-apply Coker_eq_refl.
-apply Coker_eq_symm.
-apply Coker_eq_trans.
Qed.

Add Parametric Relation {G H} {f : HomGr G H} : (gr_set (Im f)) (Coker_eq f)
 reflexivity proved by (Coker_eq_refl f)
 symmetry proved by (Coker_eq_symm f)
 transitivity proved by (Coker_eq_trans f)
 as gr_cokereq_rel.

Theorem Coker_mem_compat {G H} : ∀ (f : HomGr G H) x y,
  Coker_eq f x y → x ∈ H → y ∈ H.
Proof.
intros * Heq Hx.
destruct Heq as (z & Hz & Hfz).
apply gr_mem_compat with (x := (x - Happ f z)%G).
-rewrite Hfz.
 simpl; apply gr_sub_move_r.
 now rewrite gr_add_comm, gr_add_assoc, gr_add_opp_l, gr_add_0_r.
-simpl; apply gr_add_mem; [ easy | ].
 apply gr_opp_mem.
 now apply f.
Qed.

Theorem Coker_add_compat {G H} : ∀ (f : HomGr G H) x y x' y',
  Coker_eq f x y → Coker_eq f x' y' → Coker_eq f (x + x')%G (y + y')%G.
Proof.
intros f x y x' y' (z & Hz & Hfz) (z' & Hz' & Hfz').
exists (z + z')%G.
split.
-now apply gr_add_mem.
-rewrite Hadditive; [ | easy | easy ].
 rewrite Hfz, Hfz'; simpl.
 rewrite gr_add_assoc; symmetry.
 rewrite gr_add_assoc; symmetry.
 apply gr_add_compat; [ easy | ].
 rewrite gr_add_comm, gr_add_assoc.
 apply gr_add_compat; [ easy | ].
 rewrite gr_add_comm; symmetry.
 apply gr_opp_add_distr.
Qed.

Theorem Coker_opp_compat {G H} :∀ (f : HomGr G H) x y,
  Coker_eq f x y → Coker_eq f (- x)%G (- y)%G.
Proof.
intros * (z & Hz & Hfz).
unfold Coker_eq; simpl.
exists (- z)%G.
split; [ now apply gr_opp_mem | ].
rewrite Hopp; [ | easy ].
rewrite Hfz.
simpl; apply gr_opp_add_distr.
Qed.

Definition Coker {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero;
     gr_eq := Coker_eq f;
     gr_mem := gr_mem H;
     gr_add := @gr_add H;
     gr_opp := @gr_opp H;
     gr_zero_mem := @gr_zero_mem H;
     gr_add_mem := @gr_add_mem H;
     gr_add_0_l := Coker_add_0_l f;
     gr_add_assoc := Coker_add_assoc f;
     gr_opp_mem := gr_opp_mem H;
     gr_add_opp_r := Coker_add_opp_r f;
     gr_add_comm := Coker_add_comm f;
     gr_equiv := Coker_equiv f;
     gr_mem_compat := Coker_mem_compat f;
     gr_add_compat := Coker_add_compat f;
     gr_opp_compat := Coker_opp_compat f |}.

(* Exact sequences *)

Inductive sequence {A : AbGroup} :=
  | SeqEnd : sequence
  | Seq : ∀ {B} (f : HomGr A B), @sequence B → sequence.

Notation "A ⊂ B" := (∀ a, a ∈ A → a ∈ B) (at level 60).
Notation "A == B" := (A ⊂ B ∧ B ⊂ A) (at level 60).

Fixpoint exact_sequence {A : AbGroup} (S : sequence) :=
  match S with
  | SeqEnd => True
  | Seq f S' =>
      match S' with
      | SeqEnd => True
      | Seq g S'' => Im f == Ker g ∧ exact_sequence S'
      end
  end.

Delimit Scope seq_scope with S.

Notation "[ ]" := SeqEnd (format "[ ]") : seq_scope.
Notation "[ x ]" := (Seq x SeqEnd) : seq_scope.
Notation "[ x ; y ; .. ; z ]" := (Seq x (Seq y .. (Seq z SeqEnd) ..)) : seq_scope.

Arguments exact_sequence _ S%S.

(* Commuting diagram
        f
    A------>B
    |       |
   g|       |h
    |       |
    v       v
    C------>D
        k
*)

Definition diagram_commutes {A B C D}
     (f : HomGr A B) (g : HomGr A C) (h : HomGr B D) (k : HomGr C D) :=
  ∀ x, (Happ h (Happ f x) = Happ k (Happ g x))%G.

(* The trivial group *)

Theorem Gr1_add_0_l : ∀ x : True, I = x.
Proof. now destruct x. Qed.

Definition Gr1 :=
   {| gr_set := True;
      gr_mem _ := True;
      gr_eq := eq;
      gr_zero := I;
      gr_add _ _ := I;
      gr_opp x := x;
      gr_zero_mem := I;
      gr_add_mem _ _ _ _ := I;
      gr_add_0_l := Gr1_add_0_l;
      gr_add_assoc _ _ _ := eq_refl;
      gr_opp_mem _ H := H;
      gr_add_opp_r _ := eq_refl;
      gr_add_comm _ _ := eq_refl;
      gr_equiv := eq_equivalence;
      gr_mem_compat _ _ _ _ := I;
      gr_add_compat _ _ _ _ _ _ := eq_refl;
      gr_opp_compat _ _ H := H |}.

(* *)

Definition is_mono {A B} (f : HomGr A B) :=
  ∀ C (g₁ g₂ : HomGr C A),
  (∀ z, z ∈ C → (Happ f (Happ g₁ z) = Happ f (Happ g₂ z))%G)
  → (∀ z, z ∈ C → (Happ g₁ z = Happ g₂ z)%G).

Definition is_epi {A B} (f : HomGr A B) :=
  ∀ C (g₁ g₂ : HomGr B C),
  (∀ x, x ∈ A → (Happ g₁ (Happ f x) = Happ g₂ (Happ f x))%G)
  → (∀ y, y ∈ B → (Happ g₁ y = Happ g₂ y)%G).

Definition is_iso {A B} (f : HomGr A B) :=
  ∃ g : HomGr B A,
  (∀ x, x ∈ A → (Happ g (Happ f x) = x)%G) ∧
  (∀ y, y ∈ B → (Happ f (Happ g y) = y)%G).

(* Proofs that epimorphism is surjective and monomorphism is injective *)

Theorem epi_is_surj : ∀ {A B} {f : HomGr A B},
  is_epi f
  → ∀ y, y ∈ B → ∃ t, t ∈ A ∧ (Happ f t = y)%G.
Proof.
intros * Hed y Hy.
(* trick to make identity of type gr_set B → gr_set (Coker f) *)
set (v y1 := let _ : gr_set B := y1 in y1 : gr_set (Coker f)).
assert (Hmc : ∀ y1, y1 ∈ B → v y1 ∈ B) by easy.
assert (Hac : ∀ y1 y2, y1 ∈ B → y2 ∈ B → (y1 = y2)%G → (v y1 = v y2)%G). {
  intros * Hy1 Hy2 Hyy.
  exists 0; split; [ apply A | ].
  now unfold v; simpl; rewrite Hzero, Hyy, gr_add_opp_r.
}
assert (Had : ∀ y1 y2, y1 ∈ B → y2 ∈ B → (v (y1 + y2) = v y1 + v y2)%G). {
  intros * Hy1 Hy2.
  exists 0; split; [ apply A | now unfold v; rewrite Hzero, gr_add_opp_r ].
}
set (hv :=
  {| Happ := v;
     Hmem_compat := Hmc;
     Happ_compat := Hac;
     Hadditive := Had |}).
assert (Hmc₀ : ∀ y1, y1 ∈ B → 0 ∈ Coker f) by (intros; apply B).
assert
  (Hac₀ :
   ∀ y1 y2, y1 ∈ B → y2 ∈ B → (y1 = y2)%G → (@gr_zero (Coker f) = 0)%G). {
  intros * Hy1 Hy2 Hyy.
  simpl; unfold Coker_eq; simpl.
  exists 0; split; [ apply A | now rewrite Hzero, gr_add_opp_r ].
}
assert (Had₀ : ∀ y1 y2, y1 ∈ B → y2 ∈ B → (@gr_zero (Coker f) = 0 + 0)%G). {
  intros * Hy1 Hy2.
  simpl; unfold Coker_eq; simpl.
  exists 0; split; [ apply A | now rewrite Hzero, gr_add_0_r, gr_sub_0_r ].
}
set (hw :=
  {| Happ _ := 0;
     Hmem_compat := Hmc₀;
     Happ_compat := Hac₀;
     Hadditive := Had₀ |}).
specialize (Hed (Coker f) hv hw) as H1.
assert (H : ∀ x, x ∈ A → (Happ hv (Happ f x) = Happ hw (Happ f x))%G). {
  intros x Hx.
  simpl; unfold v; unfold Coker_eq; simpl.
  exists x; split; [ easy | now rewrite gr_sub_0_r ].
}
specialize (H1 H y Hy); clear H.
simpl in H1; unfold Coker_eq in H1; simpl in H1.
destruct H1 as (x & Hx).
rewrite gr_sub_0_r in Hx.
now exists x.
Qed.

Theorem mono_is_inj : ∀ {A B} {f : HomGr A B},
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
assert (H : ∀ z, z ∈ Ker f → (Happ f (Happ hv z) = Happ f (Happ hw z))%G). {
  intros z (Hz, Hfz).
  unfold hv, hw, v; simpl.
  now rewrite Hfz, Hzero.
}
specialize (H1 H (x1 - x2)); clear H.
assert (H : x1 - x2 ∈ Ker f). {
  split.
  -apply A; [ easy | now apply A ].
  -rewrite Hadditive; [ | easy | now apply A ].
   rewrite Hopp; [ | easy ].
   now rewrite Hxx, gr_add_opp_r.
}
specialize (H1 H); clear H.
unfold hv, hw, v in H1; simpl in H1.
apply gr_sub_move_r in H1.
now rewrite gr_add_0_l in H1.
Qed.

(* We sometimes need these axioms *)

Definition Choice := ∀ {A B} {R : A → B → Prop},
   (∀ x : A, ∃ y : B, R x y) → ∃ f : A → B, ∀ x : A, R x (f x).
Definition Decidable_Membership := ∀ G x, {x ∈ G} + {x ∉ G}.
