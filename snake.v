(* Snake lemma *)

Require Import Utf8.
Require Import Classes.RelationClasses.
Require Import Setoid.
Require ClassicalChoice.

Reserved Notation "x '∈' S" (at level 60).
Reserved Notation "x '≡' y" (at level 70).

(* Abelian Groups.

   Notes:

   -sets in groups are predicates (naive theory of sets); a value of type
    gr_set is not necessarily in the group set. To be in the group set, it
    must satisfy the predicate gr_mem, which is later syntaxified by the
    usual symbol ∈.

   -group sets are setoids: there is a specific equality (gr_eq) which is
    compatible with membership (gr_mem_compat), addition (gr_add_compat),
    and inverse (gr_inv_compat). This allows to define quotient groups,
    for example in cokernets, by changing this equality.
*)

Record AbGroup :=
  { (* data *)
    gr_set : Type;
    gr_mem : gr_set → Prop where "x ∈ G" := (gr_mem x);
    gr_eq : gr_set → gr_set → Prop where "x ≡ y" := (gr_eq x y);
    gr_zero : gr_set where "0" := (gr_zero);
    gr_add : gr_set → gr_set → gr_set where "x + y" := (gr_add x y);
    gr_inv : gr_set → gr_set where "- x" := (gr_inv x);
    (* properties *)
    gr_zero_mem : 0 ∈ G;
    gr_add_mem : ∀ x y, x ∈ G → y ∈ G → x + y ∈ G;
    gr_add_0_l : ∀ x, 0 + x ≡ x;
    gr_add_assoc : ∀ x y z, (x + y) + z ≡ x + (y + z);
    gr_inv_mem : ∀ x, x ∈ G → - x ∈ G;
    gr_add_inv_r : ∀ x, x + (- x) ≡ 0;
    gr_add_comm : ∀ x y, x + y ≡ y + x;
    gr_equiv : Equivalence gr_eq;
    gr_mem_compat : ∀ x y, x ≡ y → x ∈ G → y ∈ G;
    gr_add_compat : ∀ x y x' y', x ≡ y → x' ≡ y' → x + x' ≡ y + y';
    gr_inv_compat : ∀ x y, x ≡ y → - x ≡ - y }.

(* coq stuff: implicit and renamed arguments *)

Arguments gr_eq [_].
Arguments gr_zero [_].
Arguments gr_add [_].
Arguments gr_inv [_].
Arguments gr_zero_mem G : rename.
Arguments gr_add_mem G : rename.
Arguments gr_add_0_l G : rename.
Arguments gr_add_assoc G : rename.
Arguments gr_inv_mem G : rename.
Arguments gr_add_inv_r G : rename.
Arguments gr_add_comm G : rename.
Arguments gr_equiv G : rename.
Arguments gr_mem_compat G : rename.
Arguments gr_add_compat G : rename.
Arguments gr_inv_compat G : rename.

(* syntaxes for expressions for groups elements and sets *)

Delimit Scope group_scope with G.

Notation "0" := (gr_zero) : group_scope.
Notation "a = b" := (gr_eq a b) : group_scope.
Notation "a ≠ b" := (¬ gr_eq a b) : group_scope.
Notation "a + b" := (gr_add a b) : group_scope.
Notation "a - b" := (gr_add a (gr_inv b)) : group_scope.
Notation "- a" := (gr_inv a) : group_scope.

Notation "x '∈' S" := (gr_mem S x) (at level 60).
Notation "x '∉' S" := (¬ gr_mem S x) (at level 60).

Open Scope group_scope.

(* Homomorphism between groups *)

Record HomGr (A B : AbGroup) :=
  { H_app : gr_set A → gr_set B;
    H_mem_compat : ∀ x, x ∈ A → H_app x ∈ B;
    H_app_compat : ∀ x y,
      x ∈ A → y ∈ A → (x = y)%G → (H_app x = H_app y)%G;
    H_additive : ∀ x y,
      x ∈ A → y ∈ A → (H_app (x + y) = H_app x + H_app y)%G }.

(* coq stuff: implicit and renamed arguments *)

Arguments H_app [A] [B].
Arguments H_mem_compat _ _ f : rename.
Arguments H_app_compat _ _ f : rename.
Arguments H_additive _ _ f : rename.

(* Equality (gr_eq) in groups is an equivalence relation *)

Add Parametric Relation {G} : (gr_set G) (@gr_eq G)
 reflexivity proved by (@Equivalence_Reflexive _ (@gr_eq G) (@gr_equiv G))
 symmetry proved by (@Equivalence_Symmetric _ (@gr_eq G) (@gr_equiv G))
 transitivity proved by (@Equivalence_Transitive _ (@gr_eq G) (@gr_equiv G))
 as gr_eq_rel.

(* Coq "Morphisms": they allow to use "rewrite" in expressions containing
   inversions (-), additions (+) and memberships (∈) *)

Add Parametric Morphism {G} : (@gr_inv G)
  with signature @gr_eq G ==> @gr_eq G
  as gr_inv_morph.
Proof.
intros * Hxy.
now apply gr_inv_compat.
Qed.

Add Parametric Morphism {G} : (@gr_add G)
  with signature @gr_eq G ==> @gr_eq G ==> @gr_eq G
  as gr_add_morph.
Proof.
intros * Hxy x' y' Hxy'.
now apply gr_add_compat.
Qed.

Add Parametric Morphism {G} : (@gr_mem G)
  with signature @gr_eq G ==> iff
  as gr_mem_morph.
Proof.
intros * Hxy.
split; intros H.
-eapply gr_mem_compat; [ apply Hxy | easy ].
-eapply gr_mem_compat; [ symmetry; apply Hxy | easy ].
Qed.

(*
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

Definition M_app A B (f : HomGr A B) (x : gr_elem A) := H_app f (proj1_sig x).

Add Parametric Morphism {G H} : (M_app G H)
  with signature eq ==> gr_mem_eq G ==> @gr_eq H
  as M_app_morph.
Proof.
intros f (x, Hx) (y, Hy) Hxy.
unfold gr_mem_eq in Hxy; simpl in Hxy.
unfold M_app; simpl.
now apply H_app_compat.
Qed.
*)

(* We need that membership be decidable *)

Axiom MemDec : ∀ G x, {x ∈ G} + {x ∉ G}.

(* Miscellaneous theorems in groups elements *)

Theorem gr_add_0_r : ∀ G (x : gr_set G), (x + 0 = x)%G.
Proof.
intros.
rewrite gr_add_comm.
apply gr_add_0_l.
Qed.

Theorem gr_add_inv_l : ∀ G (x : gr_set G), (- x + x = 0)%G.
Proof.
intros.
rewrite gr_add_comm.
apply gr_add_inv_r.
Qed.

Theorem gr_inv_zero : ∀ G, (- 0 = @gr_zero G)%G.
Proof.
intros.
rewrite <- gr_add_0_l.
apply gr_add_inv_r.
Qed.

Theorem gr_sub_0_r : ∀ G (x : gr_set G), (x - 0 = x)%G.
Proof.
intros.
symmetry; rewrite <- gr_add_0_r at 1.
apply gr_add_compat; [ easy | now rewrite gr_inv_zero ].
Qed.

Theorem gr_sub_move_r : ∀ G (x y z : gr_set G),
  (x - y = z)%G ↔ (x = z + y)%G.
Proof.
intros.
split; intros Hxyz.
-now rewrite <- Hxyz, gr_add_assoc, gr_add_inv_l, gr_add_0_r.
-now rewrite Hxyz, gr_add_assoc, gr_add_inv_r, gr_add_0_r.
Qed.

Theorem gr_sub_move_l : ∀ G (x y z : gr_set G),
  (x - y = z)%G ↔ (x = y + z)%G.
Proof.
intros.
split; intros Hxyz.
-now rewrite <- Hxyz, gr_add_comm, gr_add_assoc, gr_add_inv_l, gr_add_0_r.
-now rewrite Hxyz, gr_add_comm, <- gr_add_assoc, gr_add_inv_l, gr_add_0_l.
Qed.

Theorem gr_inv_add_distr : ∀ G (x y : gr_set G), (- (x + y) = - x - y)%G.
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
apply gr_inv_compat, gr_add_comm.
Qed.

Theorem gr_inv_involutive : ∀ G (x : gr_set G), (- - x = x)%G.
Proof.
intros.
transitivity (- - x + (- x + x))%G.
-rewrite <- gr_add_0_r at 1.
 apply gr_add_compat; [ easy | ].
 now rewrite gr_add_inv_l.
-now rewrite <- gr_add_assoc, gr_add_inv_l, gr_add_0_l.
Qed.

Theorem gr_eq_inv_l : ∀ G (x y : gr_set G), (- x = y)%G ↔ (x = - y)%G.
Proof.
intros.
split; intros Hxy.
-rewrite <- Hxy; symmetry; apply gr_inv_involutive.
-rewrite Hxy; apply gr_inv_involutive.
Qed.

(* Theorems on homomorphisms *)

Theorem H_zero : ∀ A B (f : HomGr A B), (H_app f 0 = 0)%G.
Proof.
intros.
assert (H1 : (@gr_zero A + 0 = 0)%G) by apply A.
assert (H2 : (H_app f 0 + H_app f 0 = H_app f 0)%G). {
  rewrite <- H_additive; [ | apply A | apply A ].
  apply f; [ apply A; apply A | apply A | easy ].
}
assert (H3 : (H_app f 0 + H_app f 0 - H_app f 0 = H_app f 0 - H_app f 0)%G). {
  apply gr_add_compat; [ apply H2 | easy ].
}
assert (H4 : (H_app f 0 + H_app f 0 - H_app f 0 = 0)%G). {
  rewrite H3; apply gr_add_inv_r.
}
rewrite <- H4.
now rewrite gr_add_assoc, gr_add_inv_r, gr_add_0_r.
Qed.

Theorem H_inv : ∀ A B (f : HomGr A B) x,
  x ∈ A → (H_app f (- x) = - H_app f x)%G.
Proof.
intros * Hx.
assert (H1 : (x - x = 0)%G) by apply A.
assert (H2 : (H_app f (x - x) = H_app f 0)%G). {
  apply H_app_compat; [ now apply A, A | apply A | apply H1 ].
}
assert (H3 : (H_app f x + H_app f (- x) = H_app f 0)%G). {
  rewrite <- H2.
  symmetry; apply H_additive; [ easy | now apply A ].
}
assert (H4 : (H_app f x + H_app f (- x) = 0)%G). {
  rewrite H3; apply H_zero.
}
symmetry; rewrite <- gr_add_0_l.
apply gr_sub_move_l.
now symmetry.
Qed.

(* The trivial group *)

Inductive Gr0_set := G0 : Gr0_set.

Theorem Gr0_add_0_l : ∀ x, (λ _ _ : Gr0_set, G0) G0 x = x.
Proof.
now intros x; destruct x.
Qed.

Definition Gr0 :=
   {| gr_set := Gr0_set;
      gr_mem _ := True;
      gr_eq := eq;
      gr_zero := G0;
      gr_add _ _ := G0;
      gr_inv x := x;
      gr_zero_mem := I;
      gr_add_mem _ _ _ _ := I;
      gr_add_0_l := Gr0_add_0_l;
      gr_add_assoc _ _ _ := eq_refl G0;
      gr_inv_mem _ H := H;
      gr_add_inv_r _ := eq_refl;
      gr_add_comm _ _ := eq_refl G0;
      gr_equiv := eq_equivalence;
      gr_mem_compat _ _ _ _ := I;
      gr_add_compat _ _ _ _ _ _ := eq_refl;
      gr_inv_compat _ _ H := H |}.

(* Group image *)

Theorem Im_zero_mem {G H} : ∀ (f : HomGr G H),
  ∃ a : gr_set G, a ∈ G ∧ (H_app f a = 0)%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | apply H_zero ].
Qed.

Theorem Im_add_mem {G H} : ∀ f (x y : gr_set H),
  (∃ a : gr_set G, a ∈ G ∧ (H_app f a = x)%G)
  → (∃ a : gr_set G, a ∈ G ∧ (H_app f a = y)%G)
  → ∃ a : gr_set G, a ∈ G ∧ (H_app f a = x + y)%G.
Proof.
intros f y y' (x & Hxg & Hx) (x' & Hx'g & Hx').
exists (gr_add x x').
split; [ now apply G | ].
rewrite H_additive; [ | easy | easy ].
now apply gr_add_compat.
Qed.

Theorem Im_inv_mem {G H} : ∀ (f : HomGr G H) (x : gr_set H),
  (∃ a : gr_set G, a ∈ G ∧ (H_app f a = x)%G)
  → ∃ a : gr_set G, a ∈ G ∧ (H_app f a = - x)%G.
Proof.
intros f x (y & Hy & Hyx).
exists (gr_inv y).
split; [ now apply gr_inv_mem | ].
rewrite <- Hyx.
now apply H_inv.
Qed.

Theorem Im_mem_compat {G H} : ∀ f (x y : gr_set H),
  (x = y)%G
  → (∃ a, a ∈ G ∧ (H_app f a = x)%G)
  → ∃ a, a ∈ G ∧ (H_app f a = y)%G.
intros * Hxy (z & Hz & Hfz).
exists z.
split; [ easy | now rewrite Hfz ].
Qed.

Definition Im {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero;
     gr_eq := @gr_eq H;
     gr_mem := λ b, ∃ a, a ∈ G ∧ (H_app f a = b)%G;
     gr_add := @gr_add H;
     gr_inv := @gr_inv H;
     gr_zero_mem := Im_zero_mem f;
     gr_add_mem := Im_add_mem f;
     gr_add_0_l := gr_add_0_l H;
     gr_add_assoc := gr_add_assoc H;
     gr_inv_mem := Im_inv_mem f;
     gr_add_inv_r := gr_add_inv_r H;
     gr_add_comm := gr_add_comm H;
     gr_equiv := gr_equiv H;
     gr_mem_compat := Im_mem_compat f;
     gr_add_compat := gr_add_compat H;
     gr_inv_compat := gr_inv_compat H |}.

(* Group kernel *)

Theorem Ker_zero_mem {G H} : ∀ (f : HomGr G H), 0%G ∈ G ∧ (H_app f 0 = 0)%G.
Proof.
intros f.
split; [ apply gr_zero_mem | apply H_zero ].
Qed.

Theorem Ker_add_mem {G H} : ∀ (f : HomGr G H) (x y : gr_set G),
  x ∈ G ∧ (H_app f x = 0)%G
  → y ∈ G ∧ (H_app f y = 0)%G → (x + y)%G ∈ G ∧ (H_app f (x + y) = 0)%G.
Proof.
intros f x x' (Hx, Hfx) (Hx', Hfx').
split; [ now apply gr_add_mem | ].
rewrite H_additive; [ | easy | easy ].
rewrite Hfx, Hfx'.
apply gr_add_0_r.
Qed.

Theorem Ker_inv_mem {G H} : ∀ (f : HomGr G H) (x : gr_set G),
  x ∈ G ∧ (H_app f x = 0)%G → (- x)%G ∈ G ∧ (H_app f (- x) = 0)%G.
Proof.
intros f x (Hx & Hfx).
split; [ now apply gr_inv_mem | ].
rewrite H_inv; [ | easy ].
rewrite Hfx.
apply gr_inv_zero.
Qed.

Theorem Ker_mem_compat {G H} : ∀ (f : HomGr G H) x y,
  (x = y)%G → x ∈ G ∧ (H_app f x = 0)%G → y ∈ G ∧ (H_app f y = 0)%G.
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
     gr_mem := λ a, a ∈ G ∧ (H_app f a = gr_zero)%G;
     gr_add := @gr_add G;
     gr_inv := @gr_inv G;
     gr_zero_mem := Ker_zero_mem f;
     gr_add_mem := Ker_add_mem f;
     gr_add_0_l := gr_add_0_l G;
     gr_add_assoc := gr_add_assoc G;
     gr_inv_mem := Ker_inv_mem f;
     gr_add_inv_r := gr_add_inv_r G;
     gr_add_comm := gr_add_comm G;
     gr_equiv := gr_equiv G;
     gr_mem_compat := Ker_mem_compat f;
     gr_add_compat := gr_add_compat G;
     gr_inv_compat := gr_inv_compat G |}.

(* Group cokernel

   x ∈ Coker f ↔ x ∈ H/Im f
   quotient group is H with setoid, i.e. set with its own equality *)

Definition Coker_eq {G H} (f : HomGr G H) x y := (x - y)%G ∈ Im f.

Theorem Coker_add_0_l {G H} : ∀ (f : HomGr G H) x, Coker_eq f (0 + x)%G x.
Proof.
intros.
unfold Coker_eq.
exists 0%G.
split; [ apply gr_zero_mem | ].
rewrite gr_add_0_l, gr_add_inv_r.
simpl; apply H_zero.
Qed.

Theorem Coker_add_assoc {G H} : ∀ (f : HomGr G H) x y z,
  Coker_eq f (x + y + z)%G (x + (y + z))%G.
Proof.
intros.
unfold Coker_eq.
exists 0%G.
split; [ apply gr_zero_mem | ].
rewrite H_zero.
symmetry; simpl.
apply gr_sub_move_r.
rewrite gr_add_0_l.
apply gr_add_assoc.
Qed.

Theorem Coker_add_inv_r {G H} : ∀ (f : HomGr G H) x, Coker_eq f (x - x)%G 0%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | ].
now rewrite H_zero, gr_add_inv_r, gr_sub_0_r.
Qed.

Theorem Coker_add_comm {G H} : ∀ (f : HomGr G H) x y,
  Coker_eq f (x + y)%G (y + x)%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | ].
rewrite H_zero.
symmetry.
simpl; apply gr_sub_move_l.
now rewrite gr_add_0_r, gr_add_comm.
Qed.

Theorem Coker_eq_refl {G H} (f : HomGr G H) : Reflexive (Coker_eq f).
Proof.
intros x.
exists 0%G.
split; [ apply gr_zero_mem | ].
rewrite gr_add_inv_r.
simpl; apply H_zero.
Qed.

Theorem Coker_eq_symm {G H} (f : HomGr G H) : Symmetric (Coker_eq f).
Proof.
intros x y Hxy.
destruct Hxy as (z & Hz & Hfz).
exists (- z)%G.
split; [ now apply gr_inv_mem | ].
rewrite H_inv; [ | easy ].
rewrite Hfz.
simpl; rewrite gr_inv_add_distr, gr_add_comm.
apply gr_add_compat; [ | easy ].
apply gr_inv_involutive.
Qed.

Theorem Coker_eq_trans {G H} (f : HomGr G H) : Transitive (Coker_eq f).
Proof.
intros x y z Hxy Hyz.
simpl in Hxy, Hyz.
destruct Hxy as (t & Ht & Hft).
destruct Hyz as (u & Hu & Hfu).
exists (t + u)%G.
split; [ now apply gr_add_mem | ].
rewrite H_additive; [ | easy | easy ].
rewrite Hft, Hfu.
simpl; rewrite gr_add_assoc.
apply gr_add_compat; [ easy | ].
now rewrite <- gr_add_assoc, gr_add_inv_l, gr_add_0_l.
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
apply gr_mem_compat with (x := (x - H_app f z)%G).
-rewrite Hfz.
 simpl; apply gr_sub_move_r.
 now rewrite gr_add_comm, gr_add_assoc, gr_add_inv_l, gr_add_0_r.
-simpl; apply gr_add_mem; [ easy | ].
 apply gr_inv_mem.
 now apply f.
Qed.

Theorem Coker_add_compat {G H} : ∀ (f : HomGr G H) x y x' y',
  Coker_eq f x y → Coker_eq f x' y' → Coker_eq f (x + x')%G (y + y')%G.
Proof.
intros f x y x' y' (z & Hz & Hfz) (z' & Hz' & Hfz').
exists (z + z')%G.
split.
-now apply gr_add_mem.
-rewrite H_additive; [ | easy | easy ].
 rewrite Hfz, Hfz'; simpl.
 rewrite gr_add_assoc; symmetry.
 rewrite gr_add_assoc; symmetry.
 apply gr_add_compat; [ easy | ].
 rewrite gr_add_comm, gr_add_assoc.
 apply gr_add_compat; [ easy | ].
 rewrite gr_add_comm; symmetry.
 apply gr_inv_add_distr.
Qed.

Theorem Coker_inv_compat {G H} :∀ (f : HomGr G H) x y,
  Coker_eq f x y → Coker_eq f (- x)%G (- y)%G.
Proof.
intros * (z & Hz & Hfz).
unfold Coker_eq; simpl.
exists (- z)%G.
split; [ now apply gr_inv_mem | ].
rewrite H_inv; [ | easy ].
rewrite Hfz.
simpl; apply gr_inv_add_distr.
Qed.

Definition Coker {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero;
     gr_eq := Coker_eq f;
     gr_mem := gr_mem H;
     gr_add := @gr_add H;
     gr_inv := @gr_inv H;
     gr_zero_mem := @gr_zero_mem H;
     gr_add_mem := @gr_add_mem H;
     gr_add_0_l := Coker_add_0_l f;
     gr_add_assoc := Coker_add_assoc f;
     gr_inv_mem := gr_inv_mem H;
     gr_add_inv_r := Coker_add_inv_r f;
     gr_add_comm := Coker_add_comm f;
     gr_equiv := Coker_equiv f;
     gr_mem_compat := Coker_mem_compat f;
     gr_add_compat := Coker_add_compat f;
     gr_inv_compat := Coker_inv_compat f |}.

(* Exact sequence *)

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
  ∀ x, (H_app h (H_app f x) = H_app k (H_app g x))%G.

(* Functor HomGr A B → HomGr (KerA) (KerB) *)

Theorem KK_mem_compat {A B A' B'} : ∀ (a : HomGr A A') (b : HomGr B B') f f',
  diagram_commutes f a b f'
  → ∀ x : gr_set (Ker a), x ∈ Ker a → H_app f x ∈ Ker b.
intros * Hc * (Hx & Hax).
split; [ now apply f | ].
rewrite Hc.
transitivity (H_app f' 0%G); [ | apply H_zero ].
apply f'; [ apply a, Hx | apply A' | apply Hax ].
Qed.

Theorem KK_app_compat {A B A'} : ∀ (f : HomGr A B) (a : HomGr A A'),
  ∀ x y : gr_set (Ker a),
  x ∈ Ker a → y ∈ Ker a → (x = y)%G → (H_app f x = H_app f y)%G.
Proof.
intros * Hx Hy Hxy.
simpl in Hx, Hy.
now apply f.
Qed.

Theorem KK_additive {A B A'} : ∀ (f : HomGr A B) (a : HomGr A A'),
  ∀ x y : gr_set (Ker a),
  x ∈ Ker a → y ∈ Ker a → (H_app f (x + y) = H_app f x + H_app f y)%G.
Proof.
intros * Hx Hx'; simpl in Hx, Hx'.
now apply f.
Qed.

Definition HomGr_Ker_Ker {A B A' B'}
    {f : HomGr A B} {f' : HomGr A' B'} (a : HomGr A A') (b : HomGr B B')
    (Hc : diagram_commutes f a b f') :=
  {| H_app (x : gr_set (Ker a)) := H_app f x : gr_set (Ker b);
     H_mem_compat := KK_mem_compat a b f f' Hc;
     H_app_compat := KK_app_compat f a;
     H_additive := KK_additive f a |}.

(* Functor f:HomGr A B → g:HomGr B C → HomGr (CoKer f) (Coker g) *)

Theorem CC_mem_compat {A B A' B'} :
  ∀ (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  ∀ x : gr_set (Coker a), x ∈ Coker a → H_app f' x ∈ Coker b.
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
     → @gr_eq (Coker b) (H_app f' x) (H_app f' y)%G.
Proof.
intros * Hc * Hx Hy Hxy.
simpl in Hx, Hy, x, y, Hxy; simpl.
destruct Hxy as (z & Hz & Haz).
simpl; unfold Coker_eq; simpl.
exists (H_app f z).
split; [ now apply f | ].
rewrite Hc.
transitivity (H_app f' (x - y)%G).
-apply H_app_compat; [ now apply a | | easy ].
 apply A'; [ easy | now apply A' ].
-rewrite H_additive; [ | easy | now apply A' ].
 apply gr_add_compat; [ easy | now apply H_inv ].
Qed.

Theorem CC_additive {A B A' B'} :
  ∀ (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  ∀ x y : gr_set (Coker a),
  x ∈ Coker a
  → y ∈ Coker a
  → @gr_eq (Coker b) (H_app f' (x + y))%G (H_app f' x + H_app f' y)%G.
Proof.
intros * Hx Hy; simpl in Hx, Hy.
exists 0%G.
split; [ apply B | ].
rewrite H_zero; symmetry.
simpl; apply gr_sub_move_r.
rewrite gr_add_0_l.
now apply H_additive.
Qed.

Definition HomGr_Coker_Coker {A B A' B'}
    {f : HomGr A B} {f' : HomGr A' B'} (a : HomGr A A') (b : HomGr B B')
    (Hc : diagram_commutes f a b f') :=
  {| H_app (x : gr_set (Coker a)) := H_app f' x : gr_set (Coker b);
     H_mem_compat := CC_mem_compat f' a b;
     H_app_compat := CC_app_compat f f' a b Hc;
     H_additive := CC_additive f' a b |}.

(* Morphism g in snake lemma is surjective *)

Theorem g_is_surj {B C C' g} (c : HomGr C C') {cz : HomGr C Gr0} :
   Im g == Ker cz
   → ∀ x : gr_set (Ker c), ∃ y, x ∈ C → y ∈ B ∧ (H_app g y = x)%G.
Proof.
intros * sg x.
destruct (MemDec C x) as [H2| H2]; [ | now exists 0%G ].
enough (H : x ∈ Im g). {
  simpl in H.
  destruct H as (y & Hy & Hyx).
  now exists y.
}
apply sg.
split; [ easy | ].
now destruct (H_app cz x).
Qed.

(* Morphism f' in snake lemma is injective *)

Theorem f'_is_inj {A' B'} {f' : HomGr A' B'} {za' : HomGr Gr0 A'} :
   Im za' == Ker f'
   → ∀ x y, x ∈ A' → y ∈ A' → (H_app f' x = H_app f' y)%G → (x = y)%G.
Proof.
intros * sf' * Hx Hy Hxy.
assert (H2 : (H_app f' x - H_app f' y = 0)%G). {
  apply gr_sub_move_r.
  now rewrite gr_add_0_l.
}
assert (H3 : (H_app f' (x - y) = 0)%G). {
  rewrite H_additive; [ | easy | now apply A' ].
  rewrite Hxy, H_inv; [ | easy ].
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
  apply H_zero.
}
apply gr_sub_move_r in H5.
rewrite H5.
apply gr_add_0_l.
Qed.

(* Morphism f' (on cokernel) in snake lemma is injective *)

Theorem f'c_is_inj
    {A A' B'} {f' : HomGr A' B'} {a : HomGr A A'} {za' : HomGr Gr0 A'} :
  Im za' == Ker f'
  → ∀ x y, x ∈ Coker a → y ∈ Coker a →
     (H_app f' x = H_app f' y)%G → (x = y)%G.
Proof.
intros * sf' * Hx Hy Hxy.
simpl; unfold Coker_eq; simpl.
exists 0; split; [ apply A | ].
eapply (f'_is_inj sf'); [ apply a, A | | ].
-apply A'; [ easy | now apply A' ].
-transitivity (H_app f' 0).
 +apply f'; [ apply a, A | apply A' | apply H_zero ].
 +rewrite H_zero; symmetry.
  rewrite H_additive; [ | easy | now apply A' ].
  rewrite Hxy, H_inv; [ | easy ].
  apply gr_add_inv_r.
Qed.

(* Property of g₁ function, inverse of snake lemma function g *)

Definition g₁_prop {B C C'} g (c : HomGr C C') g₁ :=
  ∀ x : gr_set (Ker c), x ∈ C → g₁ x ∈ B ∧ (H_app g (g₁ x) = x)%G.

(* Property of f'₁ function, inverse of snake lemma function f' *)

Definition f'₁_prop
    {A A' B C B' C'} (a : HomGr A A') (b : HomGr B B') {c : HomGr C C'}
    (f' : HomGr A' B') g₁ f'₁ :=
  ∀ x : gr_set B',
  (∃ x1 : gr_set (Ker c), x1 ∈ Ker c ∧ (x = H_app b (g₁ x1))%G)
  → f'₁ x ∈ Coker a ∧ (H_app f' (f'₁ x) = x)%G.

Theorem g₁_in_B : ∀ {B C C' g} {c : HomGr C C'} {g₁},
  g₁_prop g c g₁ → ∀ x, x ∈ C → g₁ x ∈ B.
Proof.
intros * Hg₁ * Hx.
now specialize (Hg₁ x Hx) as H.
Qed.

(* *)

Theorem exists_B'_to_Coker_a : ∀ {A A' B B' C C' g f'}
  {g' : HomGr B' C'} (a : HomGr A A') {b : HomGr B B'} {c : HomGr C C'} {g₁},
  Im f' == Ker g'
  → g₁_prop g c g₁
  → diagram_commutes g b c g'
  → ∀ y', ∃ z',
    (∃ x, x ∈ Ker c ∧ (y' = H_app b (g₁ x))%G)
    → z' ∈ Coker a ∧ (H_app f' z' = y')%G.
Proof.
intros * sg' Hg₁ Hcgg' *.
destruct (MemDec (Im b) y') as [Hy'| Hy'].
-destruct (MemDec (Im f') y') as [(z' & Hz' & Hfz')| Hfy'].
 +exists z'; now intros (x' & Hx' & Hyx').
 +exists 0%G; intros (x' & Hx' & Hyx').
  exfalso; apply Hfy', sg'; simpl.
  split.
  *destruct Hy' as (y & Hy & Hby).
   eapply B'; [ apply Hby | now apply b ].
  *transitivity (H_app g' (H_app b (g₁ x'))).
  --apply g'; [ | | easy ].
    ++destruct Hy' as (y & Hy & Hby).
      eapply B'; [ apply Hby | now apply b ].
    ++apply b, (g₁_in_B Hg₁), Hx'.
  --rewrite <- Hcgg'.
    destruct Hx' as (Hx', Hcx').
    specialize (Hg₁ x' Hx') as H2.
    destruct H2 as (Hgx', Hggx').
    transitivity (H_app c x'); [ | easy ].
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
  let d := λ x, f'₁ (H_app b (g₁ x)) in
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
    {za' : HomGr Gr0 A'} {g₁ f'₁} :
  diagram_commutes f a b f'
  → diagram_commutes g b c g'
  → Im f == Ker g
  → Im za' == Ker f'
  → Im f' == Ker g'
  → g₁_prop g c g₁
  → f'₁_prop a b f' g₁ f'₁
  → let d := λ x, f'₁ (H_app b (g₁ x)) in
     ∀ x1 x2, x1 ∈ Ker c → x2 ∈ Ker c → (x1 = x2)%G → (d x1 = d x2)%G.
Proof.
intros * Hcff' Hcgg' sf sf' sg' Hg₁ Hf'₁ * Hx1 Hx2 Hxx.
assert (Hgy1 : (H_app g (g₁ x1) = x1)%G) by apply Hg₁, Hx1.
assert (Hgy2 : (H_app g (g₁ x2) = x2)%G) by apply Hg₁, Hx2.
assert (Hgb1 : (H_app g' (H_app b (g₁ x1)) = 0)%G). {
  rewrite <- Hcgg'.
  etransitivity; [ | apply Hx1 ].
  apply c; [ apply g, Hg₁, Hx1 | apply Hx1 | apply Hgy1 ].
}
assert (Hgb2 : (H_app g' (H_app b (g₁ x2)) = 0)%G). {
  rewrite <- Hcgg'.
  etransitivity; [ | apply Hx2 ].
  apply c; [ apply g, Hg₁, Hx2 | apply Hx2 | apply Hgy2 ].
}
assert (H1 : H_app b (g₁ x1) ∈ Im f'). {
  apply sg'; split; [ apply b, (g₁_in_B Hg₁), Hx1 | easy ].
}
assert (H2 : H_app b (g₁ x2) ∈ Im f'). {
  apply sg'; split; [ apply b, (g₁_in_B Hg₁), Hx2 | easy ].
}
destruct H1 as (z'1 & Hz'1 & Hfz'1).
destruct H2 as (z'2 & Hz'2 & Hfz'2).
move z'2 before z'1; move Hz'2 before Hz'1.
assert (H3 : (H_app f' (z'1 - z'2) = H_app b (g₁ x1 - g₁ x2))%G). {
  rewrite H_additive; [ | easy | now apply A' ].
  rewrite H_additive.
  -apply gr_add_compat; [ apply Hfz'1 | ].
   rewrite H_inv; [ | easy ].
   rewrite H_inv; [ | apply Hg₁, Hx2 ].
   now rewrite Hfz'2.
  -apply (g₁_in_B Hg₁), Hx1.
  -apply B, (g₁_in_B Hg₁), Hx2.
}
assert (H4 : g₁ x1 - g₁ x2 ∈ Im f). {
  apply sf.
  split.
  -apply B; [ apply (g₁_in_B Hg₁), Hx1 | apply B, (g₁_in_B Hg₁), Hx2 ].
  -rewrite H_additive; [ | apply Hg₁, Hx1 | apply B, Hg₁, Hx2 ].
   rewrite H_inv; [ | apply Hg₁, Hx2 ].
   apply gr_sub_move_r.
   now rewrite Hgy1, Hgy2, gr_add_0_l.
}
destruct H4 as (z & Hz & Hfz).
assert (H4 : (z'1 - z'2 = H_app a z)%G). {
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
  rewrite H_zero; symmetry.
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
  rewrite H_zero; symmetry.
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
    {a : HomGr A A'} {b : HomGr B B'} {c : HomGr C C'} {za' : HomGr Gr0 A'}
    {g₁ f'₁} :
  diagram_commutes f a b f'
  → Im f == Ker g
  → Im za' == Ker f'
  → g₁_prop g c g₁
  → f'₁_prop a b f' g₁ f'₁
  → let d := λ x, f'₁ (H_app b (g₁ x)) in
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
assert (H1 : (H_app g y1 = x1)%G) by now apply Hg₁; simpl in Hx1.
assert (H2 : (H_app g y2 = x2)%G) by now apply Hg₁; simpl in Hx2.
assert (H3 : (H_app g (y1 + y2)%G = x3)%G). {
  rewrite H_additive; [ now rewrite H1, H2 | | ].
  -apply (g₁_in_B Hg₁), Hx1.
  -apply (g₁_in_B Hg₁), Hx2.
}
assert (Hy1 : y1 ∈ B) by apply (g₁_in_B Hg₁), Hx1.
assert (Hy2 : y2 ∈ B) by apply (g₁_in_B Hg₁), Hx2.
assert (Hy3 : y3 ∈ B) by (apply (g₁_in_B Hg₁), C; [ apply Hx1 | apply Hx2 ]).
assert (H4 : (y1 + y2 - y3)%G ∈ Ker g). {
  split; [ now apply B; apply B | ].
  rewrite H_additive; [ | now apply B | now apply B ].
  symmetry; apply gr_sub_move_r.
  rewrite gr_add_0_l, H_inv; [ | easy ].
  rewrite gr_inv_involutive, H3.
  apply Hg₁, C; [ apply Hx1 | apply Hx2 ].
}
assert (Hfx1 : (H_app f' z1 = H_app b y1)%G). {
  now apply Hf'₁; exists x1.
}
assert (Hfx2 : (H_app f' z2 = H_app b y2)%G). {
  now apply Hf'₁; exists x2.
}
assert (Hfx3 : (H_app f' z3 = H_app b y3)%G). {
  unfold z3, y3.
  apply Hf'₁.
  exists x3.
  split; [ now apply (Ker c)| easy ].
}
assert
  (Hfzzz :
     (H_app f' (z1 + z2 - z3) = H_app b y1 + H_app b y2 - H_app b y3)%G). {
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
  simpl; rewrite H_additive; [ | now apply A' | now apply A' ].
  apply gr_add_compat.
  -rewrite H_additive; [ now apply gr_add_compat | easy | easy ].
  -rewrite H_inv; [ now apply gr_inv_compat | easy ].
}
apply sf in H4.
destruct H4 as (z & Hz & Hzf).
assert (Hfz : (H_app f' (z1 + z2 - z3) = H_app f' (H_app a z))%G). {
  rewrite Hfzzz.
  etransitivity.
  -apply gr_add_compat; [ now symmetry; apply b | now symmetry; apply H_inv ].
  -rewrite <- H_additive; [ | now apply B | now apply B ].
   rewrite <- Hcff'.
   apply b; [ | now apply f | now apply B; apply B ].
   rewrite <- Hzf.
   now apply f.
}
apply (f'_is_inj sf') in Hfz; [ | | now apply a ].
-simpl; unfold Coker_eq; simpl.
 exists (- z).
 split; [ now apply A | ].
 rewrite H_inv; [ | easy ].
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

(* Proof exact sequence: Ker a → Ker b → Ker c *)

Theorem exact_sequence_1 {A B C A' B' C'} :
  ∀ (f : HomGr A B) (g : HomGr B C) (f' : HomGr A' B') (g' : HomGr B' C')
     (a : HomGr A A') (b : HomGr B B') (c : HomGr C C') (za' : HomGr Gr0 A')
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
 *transitivity (H_app b (H_app f x)).
 --apply b; [ | now apply f | now symmetry ].
   eapply gr_mem_compat; [ apply Hxy | now apply f ].
 --rewrite Hcff'.
   transitivity (H_app f' (@gr_zero A')); [ | apply H_zero ].
   apply f'; [ now apply a | apply A' | easy ].
 *now apply sf; exists x.
+intros y ((Hy & Hby) & Hgy).
 assert (H : y ∈ Im f) by now apply sf; split.
 destruct H as (x & Hx & Hxy).
 exists x; split; [ | easy ].
 split; [ easy | ].
 specialize (proj2 sf' (H_app a x)) as H1.
 assert (H3 : H_app a x ∈ Ker f'). {
   split; [ now apply a | ].
   rewrite <- Hcff'.
   transitivity (H_app b y); [ | easy ].
   apply b; [ now apply f | easy | easy ].
 }
 specialize (H1 H3).
 destruct H1 as (z & _ & Hzz).
 rewrite <- Hzz.
 destruct z.
 apply H_zero.
Qed.

(* Proof exact sequence: Ker b → Ker c → CoKer a *)

Theorem exact_sequence_2 {A B C A' B' C'} :
  ∀ (f : HomGr A B) (g : HomGr B C) (f' : HomGr A' B') (g' : HomGr B' C')
    (a : HomGr A A') (b : HomGr B B') (c : HomGr C C') (za' : HomGr Gr0 A')
    (g₁ : gr_set (Ker c) → gr_set B) (f'₁ : gr_set B' → gr_set (Coker a))
    (sf : Im f == Ker g) (sf' : Im za' == Ker f')
    (Hcff' : diagram_commutes f a b f')
    (Hcgg' : diagram_commutes g b c g')
    (Hg₁ : g₁_prop g c g₁) (Hf'₁ : f'₁_prop a b f' g₁ f'₁),
 let d := λ x : gr_set (Ker c), f'₁ (H_app b (g₁ x)) in
 ∀ (dm : HomGr (Ker c) (Coker a)), H_app dm = d
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
  transitivity (H_app c (H_app g y)).
  *eapply c; [ | now apply g | now apply C ].
   eapply C; [ apply Hyx | now apply g ].
  *rewrite H1.
   transitivity (H_app g' (@gr_zero B')); [ | apply H_zero ].
   apply g'; [ now apply b | apply B' | easy ].
 +simpl in Hyx.
  assert (Hgy : H_app g y ∈ Ker c). {
    split; [ now apply g | ].
    rewrite Hcgg'.
    etransitivity; [ | apply H_zero ].
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
    -rewrite H_additive; [ | apply (g₁_in_B Hg₁), Hxk | now apply B ].
     etransitivity.
     *apply gr_add_compat; [ apply Hg₁, Hxk | ].
      now simpl; apply H_inv.
     *apply gr_sub_move_r; rewrite <- Hyx.
      symmetry; apply gr_add_0_l.
  }
  apply sf in Hyk.
  destruct Hyk as (z & Hz & Haz).
  assert (Hdx : (d x = H_app a z)%G). {
    apply (f'c_is_inj sf'); [ | now apply a | ].
    -now apply (d_mem_compat Hf'₁).
    -etransitivity; [ apply Hf'₁; now exists x | ].
     rewrite <- Hcff'; symmetry.
     etransitivity.
     +apply H_app_compat; [ | | apply Haz ].
      *apply H_mem_compat, Hz.
      *apply B; [ apply (g₁_in_B Hg₁), Hxk | now apply B ].
     +rewrite H_additive; [ | apply (g₁_in_B Hg₁), Hxk | now apply B ].
      etransitivity.
      *apply gr_add_compat; [ easy | now simpl; apply H_inv ].
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
 enough (∃ y, (y ∈ B ∧ (H_app b y = 0)%G) ∧ (H_app g y = x)%G) by easy.
 apply (H_app_compat _ _ f') in Haz; [ | now apply a | ].
 +rewrite <- Hcff' in Haz.
  exists (g₁ x - H_app f z).
  split; [ split | ].
  *apply B; [ apply Hg₁, Hx | now apply B, f ].
  *rewrite H_additive; [ | apply Hg₁, Hx | now apply B, f ].
   etransitivity.
  --apply gr_add_compat; [ easy | now apply H_inv, f ].
  --apply gr_sub_move_r; rewrite gr_add_0_l; symmetry.
    now rewrite Haz; apply Hf'₁; exists x.
  *rewrite H_additive; [ | apply Hg₁, Hx | now apply B, f ].
  --etransitivity.
   ++apply gr_add_compat; [ easy | now apply H_inv, f ].
   ++apply gr_sub_move_l.
     etransitivity; [ apply Hg₁, Hx | ].
     rewrite <- gr_add_0_l at 1.
     apply gr_add_compat; [ | easy ].
     enough (H1 : H_app f z ∈ Ker g) by now simpl in H1.
     now apply sf; exists z.
 +eapply gr_mem_compat; [ apply Haz | now apply a ].
Qed.

(* Proof exact sequence: Ker c → CoKer a → Coker b *)

Theorem exact_sequence_3 {A B C A' B' C'} :
  ∀ (f : HomGr A B) (g : HomGr B C) (f' : HomGr A' B') (g' : HomGr B' C')
    (a : HomGr A A') (b : HomGr B B') (c : HomGr C C') (za' : HomGr Gr0 A')
    (Hcff' : diagram_commutes f a b f')
    (Hcgg' : diagram_commutes g b c g')
    (sf : Im f == Ker g) (sf' : Im za' == Ker f') (sg' : Im f' == Ker g')
    (g₁ : gr_set (Ker c) → gr_set B)
    (f'₁ : gr_set B' → gr_set (Coker a))
    (Hg₁ : g₁_prop g c g₁)
    (Hf'₁ : f'₁_prop a b f' g₁ f'₁),
  let d := λ x : gr_set (Ker c), f'₁ (H_app b (g₁ x)) in
  ∀ (dm : HomGr (Ker c) (Coker a)), H_app dm = d →
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
   apply gr_mem_compat with (x := d x - H_app a z).
   -transitivity (d x - (d x - z')); simpl.
    +apply gr_add_compat; [ easy | now apply gr_inv_compat ].
    +apply gr_sub_move_l.
     symmetry.
     etransitivity; [ apply gr_add_assoc | ].
     etransitivity; [ | apply gr_add_0_r ].
     apply gr_add_compat; [ easy | ].
     apply gr_add_inv_l.
   -apply A'; [ now apply Hf'₁; exists x | now apply A', a ].
 }
 simpl; split; [ easy | ].
 unfold Coker_eq; simpl.
 enough (H : ∃ y, y ∈ B ∧ (H_app b y = H_app f' z')%G). {
   destruct H as (y & Hy & Hby).
   exists y.
   split; [ easy | now rewrite gr_sub_0_r ].
 }
 simpl in z'.
 exists (g₁ x - H_app f z).
 split.
 +apply B; [ apply Hg₁, Hx | now apply B, f ].
 +apply (H_app_compat _ _ f') in Haz; [ | now apply a | ].
  *rewrite H_additive; [ | apply Hg₁, Hx | now apply B, f ].
  --etransitivity.
   ++apply gr_add_compat; [ easy | now apply H_inv, f ].
   ++etransitivity.
    **apply gr_add_compat; [ easy | ].
      apply gr_inv_compat, Hcff'.
    **apply gr_sub_move_r.
      etransitivity; [ now symmetry; apply Hf'₁; exists x | ].
      fold (d x).
      apply gr_sub_move_l.
      etransitivity.
    ---apply gr_add_compat; [ easy | now symmetry; apply H_inv ].
    ---rewrite <- H_additive; [ now symmetry | | now apply A' ].
       now apply Hf'₁; exists x.
  *apply A'; [ now apply Hf'₁; exists x | now apply A' ].
-intros z' (Hz' & y & Hy & Hby).
 simpl in z', Hz', Hby.
 rewrite gr_sub_0_r in Hby.
 simpl; unfold Coker_eq; simpl.
 rewrite Hdm.
 enough (H :
  ∃ x, x ∈ C ∧ (H_app c x = 0)%G ∧
  ∃ z, z ∈ A ∧ (H_app a z = d x - z')%G). {
   destruct H as (x & Hx).
   now exists x.
 }
 exists (H_app g y).
 split; [ now apply g | ].
 split.
 +rewrite Hcgg'.
  etransitivity.
  *apply H_app_compat; [ now apply b | | apply Hby ].
   now apply f'.
  *assert (H : H_app f' z' ∈ Im f') by now exists z'.
   now apply sg' in H; simpl in H.
 +assert (H : g₁ (H_app g y) - y ∈ Ker g). {
    split.
    -apply B; [ now apply Hg₁, g | now apply B ].
    -rewrite H_additive; [ | now apply Hg₁, g | now apply B ].
     etransitivity; [ | apply gr_add_inv_r ].
     apply gr_add_compat; [ now apply Hg₁, g | now apply H_inv ].
  }
  apply sf in H.
  destruct H as (z & Hz & Hfz).
  exists z; split; [ easy | ].
  apply (H_app_compat _ _ b) in Hfz.
  *rewrite H_additive in Hfz; [ | now apply Hg₁, g | now apply B ].
   rewrite Hcff' in Hfz.
  --apply (f'_is_inj sf'); [ now apply a | | ].
   ++apply A'; [ | now apply A' ].
     apply Hf'₁.
     exists (H_app g y); split; [ | easy ].
     split; [ now apply g | ].
     rewrite Hcgg'.
     etransitivity.
    **apply H_app_compat; [ now apply b | | apply Hby ].
      now apply f'.
    **assert (H : H_app f' z' ∈ Im f') by (exists z'; easy).
      now apply sg' in H; simpl in H.
   ++rewrite Hfz.
     symmetry; simpl; rewrite H_additive.
     apply gr_add_compat.
    **apply Hf'₁.
      exists (H_app g y); split; [ | easy ].
      split; [ now apply g | ].
      rewrite Hcgg'.
      etransitivity.
    ---apply H_app_compat; [ now apply b | | apply Hby ].
       now apply f'.
    ---assert (H : H_app f' z' ∈ Im f') by (exists z'; easy).
       now apply sg' in H; simpl in H.
    **rewrite H_inv; [ | easy ].
      rewrite H_inv; [ | easy ].
      apply gr_inv_compat.
      now symmetry.
    **apply Hf'₁; exists (H_app g y); split; [ | easy ].
      split; [ now apply g | ].
      rewrite Hcgg'.
      etransitivity.
    ---apply H_app_compat; [ now apply b | | apply Hby ].
       now apply f'.
    ---assert (H : H_app f' z' ∈ Im f') by (exists z'; easy).
       now apply sg' in H; simpl in H.
    **now apply A'.
  *now apply f.
  *apply B; [ now apply Hg₁, g | now apply B ].
Qed.

(* Proof exact sequence: CoKer a → CoKer b → Coker c *)

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
 enough (H : ∃ x, x ∈ C ∧ (H_app c x = H_app g' y')%G). {
   destruct H as (x & Hx & Hcx).
   exists x; split; [ easy | ].
   rewrite Hcx; symmetry.
   apply gr_sub_0_r.
 }
 exists (- H_app g y).
 split; [ now apply C, g | ].
 rewrite H_inv, Hcgg'; [ | now apply g ].
 apply gr_eq_inv_l.
 rewrite <- H_inv; [ | easy ].
 symmetry.
 transitivity (H_app g' (H_app f' z' - y')).
 +rewrite H_additive; [ | now apply f' | now apply B' ].
  rewrite <- gr_add_0_l at 1.
  apply gr_add_compat; [ | easy ].
  symmetry.
  assert (H : H_app f' z' ∈ Im f') by (exists z'; easy).
  now apply sg' in H; simpl in H.
 +apply g'; [ | now apply b | now symmetry ].
  apply B'; [ now apply f' | now apply B' ].
-simpl; intros y' (Hy' & x & Hx & Hcx).
 simpl in Hcx; rewrite gr_sub_0_r in Hcx.
 unfold Coker_eq; simpl.
 enough (H : ∃ y z', y ∈ B ∧ z' ∈ A' ∧ (H_app b y = H_app f' z' - y')%G). {
   destruct H as (y & z' & Hz' & Hy & Hby).
   exists z'; split; [ easy | ].
   now exists y.
 }
 assert (Hby : y' - H_app b (g₁ x) ∈ Ker g'). {
   split.
   -apply B'; [ easy | now apply B', b, Hg₁ ].
   -rewrite H_additive; [ | easy | now apply B', b, Hg₁ ].
    rewrite <- Hcx, H_inv; [ | now apply b, Hg₁ ].
    rewrite <- Hcgg'.
    etransitivity; [ | apply gr_add_inv_r ].
    apply gr_add_compat; [ easy | ].
    apply gr_inv_compat.
    apply H_app_compat; [ now apply g, Hg₁ | apply Hx | now apply Hg₁ ].
 }
 apply sg' in Hby.
 destruct Hby as (z' & Hz' & Hfz').
 exists (- g₁ x), z'.
 split; [ now apply B, Hg₁ | ].
 split; [ easy | ].
 rewrite Hfz', gr_add_comm, <- gr_add_assoc, gr_add_inv_l, gr_add_0_l.
 now apply H_inv, Hg₁.
Qed.

(* The final lemma
                f      g       cz
            A------>B------>C------>0
            |       |       |
           a|      b|      c|
            |       |       |
            v       v       v
     0----->A'----->B'----->C'
       za'      f'      g'
*)

Lemma snake :
  ∀ (A B C A' B' C' : AbGroup)
     (f : HomGr A B) (g : HomGr B C)
     (f' : HomGr A' B') (g' : HomGr B' C')
     (a : HomGr A A') (b : HomGr B B') (c : HomGr C C')
     (cz : HomGr C Gr0) (za' : HomGr Gr0 A'),
  diagram_commutes f a b f'
  → diagram_commutes g b c g'
  → exact_sequence (Seq f (Seq g (Seq cz SeqEnd)))
  → exact_sequence (Seq za' (Seq f' (Seq g' SeqEnd)))
  → ∃ (fk : HomGr (Ker a) (Ker b)) (gk : HomGr (Ker b) (Ker c))
        (fk' : HomGr (Coker a) (Coker b)) (gk' : HomGr (Coker b) (Coker c)),
     ∃ (d : HomGr (Ker c) (Coker a)),
        exact_sequence (Seq fk (Seq gk (Seq d (Seq fk' (Seq gk' SeqEnd))))).
Proof.
intros *.
intros Hcff' Hcgg' s s'.
exists (HomGr_Ker_Ker a b Hcff').
exists (HomGr_Ker_Ker b c Hcgg').
exists (HomGr_Coker_Coker a b Hcff').
exists (HomGr_Coker_Coker b c Hcgg').
destruct s as (sf & sg & _).
destruct s' as (sf' & sg' & _).
specialize (g_is_surj c sg) as H1.
specialize (ClassicalChoice.choice _ H1) as (g₁, Hg₁).
specialize (exists_B'_to_Coker_a a sg' Hg₁ Hcgg') as H2.
specialize (ClassicalChoice.choice _ H2) as (f'₁, Hf'₁).
fold (g₁_prop g c g₁) in Hg₁.
fold (f'₁_prop a b f' g₁ f'₁) in Hf'₁.
move f'₁ before g₁.
clear H1 H2.
set (d := λ x, f'₁ (H_app b (g₁ x))).
set
  (dm :=
   {| H_app := d;
      H_mem_compat := d_mem_compat Hf'₁;
      H_app_compat := d_app_compat Hcff' Hcgg' sf sf' sg' Hg₁ Hf'₁;
      H_additive := d_additive Hcff' sf sf' Hg₁ Hf'₁ |}).
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
