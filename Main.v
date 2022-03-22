
Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.Monads.Derivative.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import tactic.
Local Open Scope cat.
Local Notation "C ⊠ D" := (category_binproduct C D) (at level 38).
Local Notation "( f #, g )" := (catbinprodmor f g).


Lemma binprod_functor_cancel {C D E : category} (F : C ⊠ D ⟶ E)
      {c c'} (f f' : C ⟦ c , c' ⟧) 
      {d d' } (g g' : D ⟦ d , d' ⟧) 
  : f = f' -> g = g' -> # F (f #, g) = # F (f' #, g').
Proof.
  intros -> ->.
  apply idpath.
Qed.

Lemma binprod_functor_comp {C D E : category} (F : C ⊠ D ⟶ E)
      {c c' c''} (f : C ⟦ c , c' ⟧) (f' : C ⟦ c' , c'' ⟧)
      {d d' d''} (g : D ⟦ d , d' ⟧) (g' : D ⟦ d' , d'' ⟧)
  : # F ((f · f') #, (g · g')) = # F (f #, g) · # F (f' #, g').
Proof.
  etrans; [|apply  functor_comp].
  apply idpath.
Qed.

Lemma binprod_functor_compr {C D E : category} (F : C ⊠ D ⟶ E)
      c
      {d d' d''} (g : D ⟦ d , d' ⟧) (g' : D ⟦ d' , d'' ⟧)
  : # F (identity c #, (g · g')) = # F (identity c #, g) · # F (identity c #, g').
Proof.
  etrans; [|apply binprod_functor_comp].
  rewrite id_right.
  apply idpath.
Qed.
Lemma binprod_functor_compl {C D E : category} (F : C ⊠ D ⟶ E)
      d
      {c c' c''} (f : C ⟦ c , c' ⟧) (f' : C ⟦ c' , c'' ⟧)
  : # F (f · f' #, identity d) = # F (f #, identity d) · # F (f' #, identity d).
Proof.
  etrans; [|apply binprod_functor_comp].
  rewrite id_right.
  apply idpath.
Qed.

Lemma binprod_functor_comp_lr {C D E : category} (F : C ⊠ D ⟶ E)
      {c c'} (f : C ⟦ c , c' ⟧)
      {d d'} (g : D ⟦ d , d' ⟧)
  : # F (f #, g) = # F (f #, identity _) · # F (identity _ #, g).
Proof.
  apply pathsinv0.
  etrans; [apply pathsinv0, functor_comp|].
  apply maponpaths.
  apply dirprod_paths;[apply id_right|apply id_left].
Qed.

Lemma binprod_functor_comp_rl {C D E : category}
      (F : C ⊠ D ⟶ E)
      {c c'} (f : C ⟦ c , c' ⟧)
      {d d'} (g : D ⟦ d , d' ⟧)
  : # F (f #, g) = # F (identity _ #, g) · # F (f #, identity _).
Proof.
  apply pathsinv0.
  etrans; [apply pathsinv0, functor_comp|].
  apply maponpaths.
  apply dirprod_paths;[apply id_left|apply id_right].
Qed.

Lemma binprod_functor_comp_swap {C D E : category} (F : C ⊠ D ⟶ E)
      {c c'} (f : C ⟦ c , c' ⟧)
      {d d'} (g : D ⟦ d , d' ⟧)
  : # F (f #, identity _) · # F (identity _ #, g) =
    # F (identity _ #, g) · # F (f #, identity _)  .
Proof.

  etrans;[apply pathsinv0, binprod_functor_comp_lr|].
  apply binprod_functor_comp_rl.
Qed.

Lemma binprod_functor_id {C D E : category} (F : C ⊠ D ⟶ E)
      c d
  : # F (identity c #, identity d) = identity (F _).
Proof.
  apply (functor_id F).
  Qed.



  (* Notation "a ⇥ b" := (precategory_morphisms a b) (a custom obj, b custom obj, at level 56). *)
  (* functor_on_objects *)


Definition mk_algebra_ob {C : precategory} { F : C ⟶ C } {X} (f : F X --> X)
  : algebra_ob F
  := tpair (fun x => F x --> x) X f .

Definition bincoproducts_sym {C : category} (BP : BinCoproducts C) : BinCoproducts C.
  intros a b.
  use make_BinCoproduct.
  - apply (BP b a).
  - apply BinCoproductIn2. 
  - apply BinCoproductIn1. 
  - cbn.
    intros c f g.
    apply make_isBinCoproduct. apply homset_property.
    clear.
    intros.
    assert (h := isBinCoproduct_BinCoproduct C (BP b a) c g f).
    eapply unique_exists; revgoals.
    intros k [h1 h2].
    apply (path_to_ctr _ _ h).
    + split; assumption.
    + intros.
      apply isapropdirprod; apply (homset_property C).
    + assert (h' := (pr2 (iscontrpr1 h))) .
      cbn in h'.
      destruct h'. 
      split; assumption.
Defined.


Section wesh.

  (*
  Declare Custom Entry obj. Declare Custom Entry mor.
  Notation "| x |" := (x) (x custom obj).
  Notation "< x >" := (x) (x custom mor).
  Notation "| x |" := (identity x) (x custom obj, in custom mor).
  Notation "{ x }" := (x) (in custom obj, x constr).
  Notation "{ x }" := (x) (in custom mor, x constr).
  Notation "( x )" := (x) (in custom mor).
  Notation "x y" := (functor_on_objects x y)  (in custom obj at level 1, right associativity).
  Notation "x y" := (# x y)  (in custom mor at level 1, right associativity).
  Infix "·" := (compose)  (in custom mor at level 40, left associativity).
  Notation "x" := x (in custom obj at level 0, x global).
  Notation "x" := x (in custom mor at level 0, x global).

  Notation "{ x = y }" := (x = y) (x custom mor, y custom mor).
*)
  Notation "'μ^' R x " := (μ (functor_with_μ_from_Monad_data _ (Monad_data_from_Monad _ R)) x)
                             (R ident, x custom obj, in custom mor at level 1 ,
                             format "'μ^' R  x").
  Notation "'η^' R x " := (η (Monad_data_from_Monad _ R) x) (R ident, x custom obj, in custom mor at level 1,
                                                            format "'η^' R  x").


  Context {C : category}
          (BC : BinCoproducts C)
          (ℸ : C ⊠ oppositeCategory C ⟶ C).


  Context (Σ : C ⟶ C).
  (* Check (fun (c : C) => < Σ c >). *)
  Let UΣ := (forget_algebras Σ).
  Context (LΣ : C ⟶ FunctorAlg Σ  )(Σ_adj : are_adjoints LΣ UΣ).

  Let S := Monad_from_adjunction Σ_adj.

  Definition universal_Smap_alg {X Y : C}(f : X --> Y)(g : Σ Y --> Y) : algebra_mor Σ | LΣ X |
    (mk_algebra_ob g) :=
    φ_adj_inv Σ_adj (B := mk_algebra_ob g) f.

  Definition universal_Smap {X Y : C}(f : X --> Y)(g : Σ Y --> Y) : | S X | --> Y :=
    # UΣ ( universal_Smap_alg f g).

  Notation "[ f ; g ]^S" := (universal_Smap f g) (in custom mor).

  Definition liftΣS {X : C} (f : Σ X --> X) : S X --> X :=
    < [ | X | ; f ]^S >.

  Notation "[ f ]^S" := (liftΣS f) (in custom mor).

  Definition ΣSa X : |Σ S X| --> S X := alg_map _ (LΣ X).





  Lemma η_universal_Smap  {X Y : C}(f : X --> Y)(g : Σ Y --> Y) :
    { η^S X · [ f ; g ]^S = f}.
  Admitted.


  (* Definition e_ΣS X : Σ X --> S X := < Σ η^S X > · ΣSa. *)

  Definition is_algebra_mor (F : C ⟶ C) {X Y}(f : F X --> X)(g : F Y --> Y)(h : X --> Y) :=
    # F h · g = f · h.

  Definition is_Σ_algebra_mor {X Y} (f : Σ X --> X)(g : Σ Y --> Y)(h : X --> Y) :=
    is_algebra_mor Σ f g h.

  Lemma is_Σ_S_algebra_mor {X Y}(f : Σ X --> X)(g : Σ Y --> Y)(h : X --> Y) :
    is_Σ_algebra_mor f g h <-> is_algebra_mor S <[f]^S> <[g]^S>  h.
    Admitted.


  Lemma universal_Smap_is_Σ_algebra_mor 
        {X Y : C}(f : X --> Y)(g : Σ Y --> Y) :
    is_Σ_algebra_mor (ΣSa _) g <[f ; g]^S>.
  Admitted.

  Lemma μ_is_universal {X} :
    {μ^S X = [ {ΣSa X} ]^S}.
    cbn.
    rewrite (functor_id LΣ).
    apply pathsinv0.
    apply id_left.
  Qed.

  Lemma μ_is_Σ_algebra_mor 
        {X : C} :
    is_Σ_algebra_mor (ΣSa (S X)) (ΣSa X) <μ^S X>.
  rewrite μ_is_universal.
  apply universal_Smap_is_Σ_algebra_mor.
  Qed.


  Lemma is_Σ_algebra_mor_comp {X Y Z} {f : Σ X --> X}
        (g : Σ Y --> Y)
        {h : Σ Z --> Z}
        (u : X --> Y)
        (v : Y --> Z) :
    is_Σ_algebra_mor f g u ->
    is_Σ_algebra_mor g h v ->
    is_Σ_algebra_mor f h (u · v).
  Admitted.

  Lemma universal_Smap_unique 
        {X Y : C}(g : Σ Y --> Y) (h1 h2 : | S X | --> Y) :
    { η^S X · h1 = η^S X · h2 } ->
    is_Σ_algebra_mor (ΣSa X) g h1 ->
    is_Σ_algebra_mor (ΣSa X) g h2 ->
    h1 = h2.
    Admitted.
    
  Lemma S_universal_comp {X Y Z : C}(f : X --> Y)(g : Σ Y --> Y)(u : Z --> S X) : 
    { [u ; {ΣSa X} ]^S · [f ; g]^S = [ u · [ f ; g]^S ; g]^S}.
  Proof.
    Admitted.

  Lemma S_universal_Smap {X Y Z : C}(f : X --> Y)(g : Σ Y --> Y)(u : Z --> X) : 
    { S u · [f ; g]^S = [u · f ; g]^S}.
  Proof.
    Admitted.
  Lemma universal_Smap_eq {X Y : C}(f : X --> Y)(g : Σ Y --> Y) : 
    { [ f ; g]^S = S f · [ g ]^S }.
    apply pathsinv0.
    etrans; [eapply S_universal_Smap|].
    rewrite id_right.
    apply idpath.
  Qed.






  (* Notation "'Γ_{' a } b" := (Γ (make_dirprod b a)) (at level 10). *)

  Context (T : Monad C).
  Context {δ : S ∙ T ⟹ T ∙ S} (d_laws : monad_dist_laws δ) .

  Definition lift_Talg {X} (x : T X --> X) : |T S X| --> S X := δ X · # S x.
  Notation "[ x ]^T" := (lift_Talg x) (in custom mor).

  Notation M := (monad_comp d_laws).

  Definition mk_M_alg {X} (s : Σ X --> X)(t : T X --> X) : M X --> X := < S t  · [ s ]^S >.
  Notation "[ s ; t ]^M" := (mk_M_alg s t) (in custom mor).


  (* Context (OC : Initial C). *)
  (* Context (T0 : isInitial C (T OC)) . *)

  Let O : C ⊠ C ⟶ C := bincoproduct_functor BC.

  (* Notation "X '_{' a } b" := (functor_on_objects (functor_data_from_functor _ _ X) (make_catbinprod b a)) *)
  (*   (X ident, in custom obj at level 0, right associativity, *)
  (*                              format "X '_{' a '}'  b"). *)


  Notation "'O_{' a } b" := (functor_on_objects (functor_data_from_functor _ _ O) (make_catbinprod b a))
    (in custom obj at level 1, right associativity).
  
  Notation "'ℸ_{' a } b" := (functor_on_objects (functor_data_from_functor _ _ ℸ) (make_catbinprod b a))
    (in custom obj at level 1, right associativity).
    
  Definition Oe X : | O_{ X } X| --> X := BinCoproductArrow (BC X X) (identity X)
                                                       (identity X).
  

  Notation "'ℸ_{' f } g" := (# (functor_data_from_functor _ _ ℸ) (catbinprodmor (D := oppositeCategory C) g f))  
    (in custom mor at level 1, right associativity). 
  Notation "'O_{' f } g" := (# (functor_data_from_functor _ _ O) (catbinprodmor g f))  
    (in custom mor at level 1, right associativity). 

  (* TODO: Cf nlab: Algebra for a profunctor? *)
  Definition is_ℸS_algebra_mor {X Y} (f : X --> | ℸ_{S X} X |)(g : Y --> | ℸ_{S Y} Y |)
             (u : X --> Y) :=
    { f · ℸ_{ |S X |} u = u · g · ℸ_{ S u} | Y | }.

  Lemma Oe_nat {X X'} (u : X --> X') :   {O_{ u} u · {Oe X'} = {Oe X} · u}.
  Admitted.


  Definition O_dist (R : Monad C) (x y : C) : | O_{y} R x | --> | R O_{y} x | :=
   deriv_dist y (bincoproducts_sym BC) R x.


  (*
  Lemma (binprod_functor_comp O) {a a' a'' b b' b''} (f : C ⟦ a , a' ⟧)(g : C ⟦ a' , a'' ⟧)
        (k : b --> b') (h : b' --> b'') :
     (* { ℸ_{ f · g } | b |   = ℸ_{ g } Γ_{ f } b }. *)
     { O_{ f · g } (k · h)  =  O_{ f } k · O_{ g } h }.
    Check binprod_functor_comp O f g k h.
    Admitted.

  Lemma (binprod_functor_cancel O) {a a' b b'} (f f' : C ⟦ a , a' ⟧)(g g': C ⟦ b , b' ⟧) :
    f = f' -> g = g' -> { O_{ f } g = O_{ f'} g' }.
    intros -> ->.
    apply idpath.
  Qed.

  Lemma O_id a a' : { O_{|a|} |a'| = |O_{a} a'| }.
    apply (functor_id O).
  Qed.
  Lemma (binprod_functor_cancel ℸ) {a a' b b'} (f f' : C ⟦ a , a' ⟧)(g g': C ⟦ b , b' ⟧) :
    f = f' -> g = g' -> { ℸ_{ f } g = ℸ_{ f'} g' }.
    intros -> ->.
    apply idpath.
  Qed.

  Lemma (binprod_functor_comp ℸ) {a a' a'' b b' b''} (f : C ⟦ a , a' ⟧)(g : C ⟦ a' , a'' ⟧)
        (k : b --> b') (h : b' --> b'') :
     (* { ℸ_{ f · g } | b |   = ℸ_{ g } Γ_{ f } b }. *)
     { ℸ_{ f · g } (k · h)  =  ℸ_{ g } k · ℸ_{ f } h }.
    Admitted.

  Lemma (binprod_functor_comp ℸ)l {a a' a'' b b'} (f : C ⟦ a , a' ⟧)(g : C ⟦ a' , a'' ⟧)
        (k : b --> b')  :
     (* { ℸ_{ f · g } | b |   = ℸ_{ g } Γ_{ f } b }. *)
     { ℸ_{ f · g } k  =  ℸ_{| {_}|} k · ℸ_{ g } | b' | · ℸ_{ f } | b'|  }.
    Admitted.

  Lemma (binprod_functor_comp ℸ)r {a a' a'' b } (f : C ⟦ a , a' ⟧)(g : C ⟦ a' , a'' ⟧):
        (* (k : C ⟦b , b'⟧)  : *)
     (* { ℸ_{ f · g } | b |   = ℸ_{ g } Γ_{ f } b }. *)
     { ℸ_{ | b | } (f · g)  =  ℸ_{ | b | } f · ℸ_{ | b | } g  }.
    Admitted.

  Lemma (binprod_functor_comp ℸ)r' {a a' a'' b b'} (f : C ⟦ a , a' ⟧)(g : C ⟦ a' , a'' ⟧)
        (k : C ⟦b , b'⟧)  :
     (* { ℸ_{ f · g } | b |   = ℸ_{ g } Γ_{ f } b }. *)
     { ℸ_{ k } (f · g)  =  ℸ_{ k } f · ℸ_{ | b | } g  }.
    Admitted.
*)

  (*
Au lieu de
Γ_𝑌 (Σ(𝑋 )) → 𝑆𝑇 (Γ_𝑆𝑇𝑌 𝑋  + 𝑋 + 𝑌 )
on considere le mate
 Σ(ℸ_STY(𝑋 )×X) → ℸ_Y O_Y 𝑆𝑇(X)

Γ_𝑌 (Σ(𝑋 )) → 𝑆𝑇 (Γ_𝑆𝑇𝑌 𝑋  + Y ) = 𝑆𝑇 O_Y (Γ_𝑆𝑇𝑌 𝑋 )
Voire, en supprimant le  + X dans le codomaine,
 Σ(ℸ_STY(𝑋 )) → ℸ_Y 𝑆𝑇(X+Y)
 Σ(ℸ_MY(𝑋 )) → ℸ_Y O_Y MX
   *)
  Context (d : ∏ (X Y : C), |  Σ ℸ_{ M Y } X |  --> | ℸ_{ Y } M O_{ Y } X | ).

  Context (d_nat : ∏ X X' Y Y' (f : C ⟦ X, X' ⟧) (g : C ⟦ Y, Y' ⟧),
              { {d X Y' } · ℸ_{ g } M O_{ |Y'| } f = Σ ℸ_{ M g } f · {d X' Y} · ℸ_{|Y|} M O_{g} | X'| }
          ).

  Lemma d_nat2  {X  Y Y'}  (g : C ⟦ Y, Y' ⟧) :
              { {d X Y' } · ℸ_{ g } | M O_{ Y' } X | = Σ ℸ_{ M g } |X| · {d X Y} · ℸ_{|Y|} M O_{g} | X| } .
    etrans; [| apply d_nat].
    apply cancel_precomposition.
    apply (binprod_functor_cancel ℸ).
    apply pathsinv0.
    rewrite binprod_functor_id.
    apply functor_id.
    apply idpath.
  Qed.

  (* Lemma (binprod_functor_comp ℸ) {a a' a'' b b' b''} *)
  (*       (f : a --> a')(g : a' --> a'') *)
  (*       (h : b --> b')(k : b' --> b'') *)
  (*   : *)
  (*    (* { ℸ_{ f · g } | b |   = ℸ_{ g } Γ_{ f } b }. *) *)
  (*    { ℸ_{ g } h · ℸ { f } k   =    }. *)
  (*   Admitted. *)
    (* Check fun  {a a' a'' b} (f : C ⟦ a , a' ⟧)(g : C ⟦ a' , a'' ⟧) => *)
    (*  (* { ℸ_{ f · g } | b |   = ℸ_{ g } Γ_{ f } b }. *) *)
    (*  < ℸ_{ f · g } | b | >. *)




(*     Definition ofCourse {A : Type} (x : A) := True. *)
(* Ltac failIfId := match goal with *)
(*                  | |-  ofCourse (identity _) => fail 1 *)
(*                  | |- _ => exact I *)
(*                  end. *)
  Definition ℸl {a a' b} (f : C ⟦ a , a' ⟧) := < ℸ_{f} |b|>.
  Definition ℸr {a a' b} (f : C ⟦ a , a' ⟧) := < ℸ_{|b|} f>.
  
  Lemma ℸ_splitlr {a a' b b' } (f : C ⟦ a , a' ⟧)(g : C ⟦ b , b' ⟧):
    (* ofCourse f -> ofCourse g -> *)
        (* (k : C ⟦b , b'⟧)  : *)
     (* { ℸ_{ f · g } | b |   = ℸ_{ g } Γ_{ f } b }. *)
     { ℸ_{f} g  =  { ℸl  f}  · {ℸr g}  }.
    Admitted.

  Lemma ℸ_splitrl {a a' b b' } (f : C ⟦ a , a' ⟧)(g : C ⟦ b , b' ⟧):
    (* ofCourse f -> ofCourse g -> *)
        (* (k : C ⟦b , b'⟧)  : *)
     (* { ℸ_{ f · g } | b |   = ℸ_{ g } Γ_{ f } b }. *)
     { ℸ_{f} g  =  { ℸr  g}  · {ℸl f}  }.
    Admitted.

  (*
  Lemma ℸ_swap {a a' b b' } (f : C ⟦ a , a' ⟧)(g : C ⟦ b , b' ⟧):
    (* ofCourse f -> ofCourse g -> *)
        (* (k : C ⟦b , b'⟧)  : *)
     (* { ℸ_{ f · g } | b |   = ℸ_{ g } Γ_{ f } b }. *)
     { ℸ_{f} |{_}| · ℸ_{|{_}|} g =  ℸ_{|{_}|} g · ℸ_{f} |{_}|  }.
    Admitted.
*)


  (* Lemma Γ_compr {a a' a'' b} (f : a --> a')(g : a' --> a'') : *)
  (*    (* { ℸ_{ f · g } | b |   = ℸ_{ g } Γ_{ f } b }. *) *)
  (*    < ℸ_{ f · g } | b | >  = < ℸ_{ g } ℸ_{ f } b  >. *)
  (*   Admitted. *)

  (* Notation τ := (Alg_map T). *)


  Check (fun x => < η^S x > ).




(* -- ℸ (S X) - × id se releve en un foncteur $(Σ+X)-alg→Σ-alg$ *)
(* ℸa : ∀ {X Y : Set}(x : X → Y)(a : F Y → Y) → F (ℸ (S X) Y) → ℸ (S X) Y *)
(* ℸa {X}{Y} x a z = ℸf id (SX-rec a (copair id (SX-rec a x))) *)
(*     (b (Ff (ℸf (μ {X}) id ) z)) *)

  Definition ℸa {X Y}(x : X --> Y)(a : Σ Y --> Y)(τ : T Y --> Y)(t : T X --> X) : |Σ ℸ_{ S X} Y| --> |ℸ_{ S X} Y|.
  refine < Σ ℸ_{ (S [t]^T · μ^S X)} |Y| · {d _ _} · {_}  >.
  refine < ℸ_{ |S X|} (M (O_{S x · [ a ]^S} | Y | · {Oe Y} ) · {_})>.
  refine < [ a ; τ ]^M>.
  Defined.

    Lemma ℸa_nat {X Y Y'} (u : Y --> Y')
               (t : T Y --> Y)(y : Y --> X)
               (t' : T Y' --> Y')(y': Y' --> X)
               (σ : Σ X --> X)(τ : T X --> X) 
      : 
      y = u · y' ->
      (* u is a T-algebra morphism *)
      t · u = # T u · t' ->

                   is_Σ_algebra_mor 
                         (ℸa y' σ τ t')
                         (ℸa y σ τ t)
        < ℸ_{S u} |X|
        >
    .
      intros -> hu.
      unfold ℸa.
      hnf.
      cbn -[S O universal_Smap].
      rewrite !assoc.
      etrans; revgoals.
      {
        rewrite !assoc'.
        apply cancel_precomposition.
        apply cancel_precomposition.
        apply pathsinv0.
        apply (binprod_functor_comp_swap ℸ).
      }
      etrans; revgoals.
      {
        apply cancel_precomposition.
        rewrite !assoc.
        apply cancel_postcomposition.
        apply pathsinv0.
        apply d_nat2.
      }
      rewrite !assoc.
      rewrite <- !(functor_comp Σ).
      rewrite !assoc'.
      apply map_on_two_paths.
      - apply maponpaths.
        etrans; [apply pathsinv0,(binprod_functor_comp ℸ)|].
        etrans; [|apply (binprod_functor_comp ℸ)].
        apply (binprod_functor_cancel ℸ); [apply idpath|].
        cbn -[S O].
        etrans.
        {
          rewrite assoc'.
          apply (@cancel_precomposition C).
          apply pathsinv0.
          apply (nat_trans_ax (μ S)).
        }
        rewrite !assoc.
        apply cancel_postcomposition.
        etrans;[ |apply (functor_comp S)].
        etrans;[ apply pathsinv0, (functor_comp S)|].
        apply maponpaths.
          (* {[t ]^T · S u = T S u · [t' ]^T} *)

        admit.
      - apply cancel_precomposition.
        etrans; [ | apply (binprod_functor_comp ℸ)].
        apply (binprod_functor_cancel ℸ); revgoals.
        { apply pathsinv0, id_right. }
        rewrite !assoc.
        apply cancel_postcomposition.
        etrans;[|apply (functor_comp M)].
        apply (maponpaths (# M)).
        rewrite !assoc.
        apply cancel_postcomposition.
        etrans ; [ | apply binprod_functor_comp].
        apply binprod_functor_cancel; [  apply pathsinv0, id_right|].
        rewrite assoc.
        apply cancel_postcomposition.
        apply functor_comp.
        Admitted.

        Lemma ℸa_nat2 {X X' Y} (u : X --> X')
               (t : T Y --> Y)(y : Y --> X)(y' : Y --> X')
               (σ : Σ X --> X)(τ : T X --> X) 
               (σ' : Σ X' --> X')(τ' : T X' --> X') 
      : 
      y' = y · u ->
                   is_Σ_algebra_mor 
                         (ℸa y σ τ t)
                         (ℸa y' σ' τ' t)
        < ℸ_{| S Y|} u
        >.
        intros ->.
        hnf.
        unfold ℸa.
        rewrite !assoc.
        Admitted.




    Definition ℸ_Σalg {X} (a : T X --> X) : C ⟦ | Σ ℸ_{ S S X} S X |, | ℸ_{ S S X} S X | ⟧.
      eapply ℸa.
      - apply identity.
      - apply ΣSa.
      - exact < [ a ]^T >.
      - exact < [ a ]^T >.
    Defined.


    Definition ℸ_Σalg_SS {X} (a : T X --> X) : C ⟦ | Σ ℸ_{ S S S X} S X |, | ℸ_{ S S S X} S X | ⟧.
      apply ℸa.
      - apply (μ S).
      - apply ΣSa.
      - exact < [a]^T>.
      - exact < [[a]^T]^T>.
    Defined.

    Ltac splitℸ :=
          change < ℸ_{ {?f} } | {?b} |> with (ℸl (b := b) f);
    change < ℸ_{ |{?b}| } | {?f} |> with (ℸr (b := b) f);
    rewrite !ℸ_splitlr;
    unfold ℸl, ℸr.

    (* Compatibilite: cf compatST.json *)
    Lemma lift_Talg_double {X}(t : T X --> X) : { [ [ t ]^T ]^T · μ^S X = T μ^S X · [t]^T }.
      Admitted.

  Ltac bifunct_cancel F :=
    repeat (etrans; [ | apply (binprod_functor_comp F)]);
    repeat (etrans; [ apply pathsinv0, (binprod_functor_comp F) | ]);
    (* rewrite <- ?(binprod_functor_comp F); *)
    rewrite ?id_right, ?id_left;
    apply (binprod_functor_cancel F); try apply idpath.

  (* tentative de generalisation *)
  Lemma  ℸμ_is_Σ_alg_mor_gen {X Y : C}(tX : T X --> X)(tY : T Y --> Y)(u : X --> S Y): 
     is_Σ_algebra_mor (ℸa u (ΣSa Y) < [tY ]^T > tX)
   (ℸa < [u; {ΣSa Y} ]^S > (ΣSa Y) < [tY ]^T > < [tX ]^T > : C ⟦ | Σ ℸ_{ {S ∙ S} X} S Y |, | ℸ_{ {S ∙ S} X} S Y | ⟧)
   < ℸ_{ μ^S X} | S Y | >.
  Proof.
    hnf.
    cbn -[S O universal_Smap].
    unfold ℸa.
    rewrite <- μ_is_universal.
    rewrite !assoc.
    rewrite !(binprod_functor_compl ℸ).
    rewrite !assoc.
    cbn -[S O universal_Smap].
    apply pathsinv0.
  (* rewrite (Monad_law2 (T := S) X). *)
etrans.
{
  do 2 apply cancel_postcomposition.
  repeat rewrite assoc'.
  do 2 apply cancel_precomposition.
  repeat rewrite assoc.
  apply (binprod_functor_cancel ℸ);[|apply idpath].
  etrans.
  {
  etrans;[ apply (functor_comp M)|].
  cbn -[S M O].
  apply cancel_postcomposition.
  apply (maponpaths).
  apply (binprod_functor_cancel O).
  apply idpath.
  rewrite μ_is_universal.
  apply pathsinv0.
  apply universal_Smap_eq.

  (*
  etrans;[|apply (functor_id M)].
  apply maponpaths.
  etrans;[|apply (binprod_functor_id O)].
  apply (binprod_functor_cancel O).
  apply idpath.
  apply Monad_law2.
*)
  }
  apply idpath.
}
etrans.
{
  repeat rewrite assoc'.
  do 2 apply cancel_precomposition.
  repeat rewrite assoc.
  (* remove this after copying the goal *)
  etrans.
  {
    rewrite assoc'.
    apply cancel_precomposition.
    apply (binprod_functor_comp_swap ℸ).
    
  }
  rewrite assoc.
  apply cancel_postcomposition.
  apply (binprod_functor_comp_swap ℸ).
  (* (* copy the result in the proof editor *) *)
  (* norm_graph. *)
}
rewrite !assoc.
etrans.
{
  do 2 apply cancel_postcomposition.
  repeat rewrite assoc'.
  apply cancel_precomposition.
  repeat rewrite assoc.
  (* remove this after copying the goal *)
  (* duplicate_goal. *)
  apply d_nat2.
  (* (* copy the result in the proof editor *) *)
  (* norm_graph. *)
  (* admit. *)
}
rewrite !assoc.
assert (eq1 :
         { ℸ_{ |S S X|} M O_{ μ^S X} |S Y| · ℸ_{ | S S X |} (M O_{ [u; {ΣSa Y} ]^S} |S Y| · M {Oe | S Y |}) · ℸ_{ | S S X |} [{ΣSa Y}; [tY ]^T ]^M = ℸ_{ |S S X| } S T (O_{ S [u; {ΣSa Y} ]^S · μ^S Y} |S Y| · {Oe | S Y |}) · ℸ_{ |S S X| } [{ΣSa Y}; [tY ]^T ]^M }).
{
  rewrite <- !(binprod_functor_compl ℸ).
  apply (binprod_functor_cancel ℸ);[|apply idpath].
  cbn -[S M O universal_Smap].
  apply cancel_postcomposition.
  rewrite <- !(functor_comp M).
  apply (maponpaths (# M)).
  rewrite assoc.
  apply cancel_postcomposition.
  etrans;[apply pathsinv0, (binprod_functor_compr O)|].
  apply binprod_functor_cancel.
  apply idpath.
  cbn -[S universal_Smap].
  rewrite !μ_is_universal.
  etrans;[| apply pathsinv0, S_universal_Smap].
  etrans;[ apply (S_universal_comp)|].
  rewrite id_left, id_right.
  apply idpath.
}
assert (eq2 :
          {Σ ℸ_{ S [tX ]^T · μ^S X} |S Y| · Σ ℸ_{ M μ^S X} | S Y | = Σ ℸ_{ μ^S X} |S Y| · Σ ℸ_{ S [[tX ]^T ]^T · μ^S S X} |S Y|}).
{
  rewrite  <- !(functor_comp Σ).
  apply maponpaths.
  bifunct_cancel ℸ.
  cbn -[S].
  rewrite assoc.
  etrans.
  apply cancel_postcomposition.
  rewrite <- !(functor_comp S).
  apply maponpaths.
  apply pathsinv0, lift_Talg_double.
  rewrite (functor_comp S).
  rewrite !assoc'.
  apply cancel_precomposition.
  apply (Monad_law3 (T := S)).
}
etrans.
{
  do 4 apply cancel_postcomposition.
  apply eq2.
}
rewrite !assoc'.
apply cancel_precomposition.
apply cancel_precomposition.
apply cancel_precomposition.
rewrite !assoc.
apply eq1.

Qed.

(* ℸa-μ *)
           (* ℸf (μ {S X}) id (ℸa id ind z) ≡ ℸa μ ind (Ff ( ℸf μ id) z) *)
    Lemma   μ_T_Σalg_mor {X} (a : T X --> X): is_Σ_algebra_mor (ℸ_Σalg a) (ℸ_Σalg_SS a) < ℸ_{ μ^S S X} | S X | >.
    unfold ℸ_Σalg, ℸ_Σalg_SS.
    assert (h := ℸμ_is_Σ_alg_mor_gen <[a]^T> a <|S X|>).
    cbn -[S universal_Smap] in h.
    rewrite μ_is_universal.
    exact h.
    Qed.

  Definition c {X}(a : T X --> X)(b : X --> | ℸ_{ S X } X |) : S X --> | ℸ_{S S X} S X |.
  refine < [ { _ } ; { _ }]^S >.
  - exact < b · ℸ_{ μ^S X }  η^S X   >.
  - apply ℸ_Σalg.
    assumption.
  Defined.

  (* eta_is_alg.json *)
  Lemma η_is_alg {X}(a : T X --> X)(b : X --> | ℸ_{ S X } X |) :
    is_ℸS_algebra_mor b (c a b) < η^S X >.
  Proof.
    unfold c.
    unfold ℸ_Σalg.
    unfold ℸa.
    etrans; revgoals.
    {
      apply cancel_postcomposition.
      apply pathsinv0.
      apply η_universal_Smap.
    }

    rewrite !assoc'.
    apply cancel_precomposition.
    bifunct_cancel ℸ.
    apply pathsinv0.
    apply (Monad_law2 (T := S)).
    Qed.

  (* same diagram as before, except that .. *)
  Lemma η_is_almost_alg {X}(a : T X --> X)
        (b : X --> | ℸ_{ S X } X |) :
                                                     (* here it is η^S S X instead of S η^S X *)
         { b · ℸ_{ | S X |} η^S X = η^S X · {c a b} · ℸ_{ η^S S X} | S X |  }.
    unfold c.
    unfold ℸ_Σalg.
    unfold ℸa.
    etrans; revgoals.
    {
      apply cancel_postcomposition.
      apply pathsinv0.
      apply η_universal_Smap.
    }

    rewrite !assoc'.
    apply cancel_precomposition.
    bifunct_cancel ℸ.
    apply pathsinv0.
    apply (Monad_law1 (T := S)).
  Qed.
  Definition c' {X}(a : T X --> X)(b : X --> | ℸ_{ S X } X |) : 
    C ⟦ | S X |, | ℸ_{ S S X} S X | ⟧.
    refine (_ · < ℸ_{ μ^S X} | S X | >).
    refine <[ {_} ; {_} ]^S>.
    - refine (b · < ℸ_{|S X|} η^S X >).
    - eapply ℸa.
      apply η.
      apply ΣSa.
      exact < [a ]^T>.
      exact a.
      Defined.

  Lemma η_liftΣS {X : C}(f : Σ X --> X) : { η^S X · [ f ]^S = | X | }.
    apply η_universal_Smap.
    Qed.
  Lemma liftΣS_assoc {X : C} (s : Σ X -->  X) :
  {S [s ]^S · [s ]^S = μ^S X · [s ]^S}.
    Admitted.

  Lemma universal_Smap_identity {X} :
    { [η^S X; {ΣSa X} ]^S = {identity (S X)} }.
    eapply universal_Smap_unique.
    - cbn -[S universal_Smap].
    rewrite id_right.
    apply η_universal_Smap.
    - apply universal_Smap_is_Σ_algebra_mor.
    - hnf.
      cbn -[S].
      etrans.
      apply cancel_postcomposition.
      apply functor_id.
      rewrite id_left, id_right.
      apply idpath.
  Qed.

  (* TODO: voir si on peut generaliser et factoriser avec μ_T_Σalg_mor *)
  (* dalethmu_is_sigma_mor.json *)
  Lemma ℸμ_is_Σ_alg_mor {X : C}(t : T X --> X):
    is_Σ_algebra_mor (ℸa < η^S X > (ΣSa X) < [t ]^T > t)
  (ℸ_Σalg t) < ℸ_{ μ^S X} | S X | >.
  Proof.
        unfold ℸ_Σalg, ℸ_Σalg_SS.
    assert (eq : <[η^S X; {ΣSa X} ]^S> = identity (S X) ).
    {
      apply universal_Smap_identity.
    }
    generalize ( ℸμ_is_Σ_alg_mor_gen t t <η^S X>).
    rewrite <- eq.
    intro hh.
    exact hh.
Qed.



  Lemma c_c'_eq {X} a b : @c X a b = c' a b.
    unfold c,c'.
    eapply universal_Smap_unique.
    - rewrite η_universal_Smap.
      rewrite assoc.
      rewrite η_universal_Smap.
      rewrite assoc'.
      apply cancel_precomposition.
      bifunct_cancel ℸ.
      cbn -[S].
      apply pathsinv0, id_right.
    - apply universal_Smap_is_Σ_algebra_mor.
    - eapply is_Σ_algebra_mor_comp.
      + apply universal_Smap_is_Σ_algebra_mor.
      + apply ℸμ_is_Σ_alg_mor.
  Qed.


  (* TODO: voir si on peut appliquer ca plus loin *)
  
Lemma c_η_μ {X}(a : T X --> X)(b : X --> | ℸ_{ S X } X |) : 
    { {c a b} · ℸ_{η^S S X} | S X | · ℸ_{μ^S X} | S X | = {c a b}}.
  Proof.
    rewrite c_c'_eq.
    unfold c'.
    rewrite !assoc'.
    etrans.
    - apply cancel_precomposition.
      rewrite assoc.
      etrans.
      {
      apply cancel_postcomposition.
      etrans;[ apply pathsinv0 , (binprod_functor_compr ℸ)|].
      apply (binprod_functor_cancel ℸ).
      apply idpath.
      apply (Monad_law1).
      }
      apply cancel_postcomposition.
      apply (binprod_functor_id ℸ (S X) (S X)).
    - rewrite id_left.
      apply idpath.
      Qed.


  (*
μ morphisme d'algebre, cf coalgebra-param.json

SSX    --->   SX
 |             |
 |             |
 v             v
ℸ_SSSX SSX   ℸ_SSX SX
 |             |
 v             v
    ℸ_SSSX SX

  *)
  Lemma μ_is_alg {X}(a : T X --> X)(b : X --> | ℸ_{ S X } X |) :
    is_ℸS_algebra_mor (c < [a ]^T> (c a b))(c a b) < μ^S X >.
    (* { μ^S X · {c a b} · ℸ_{ S (μ^S X) } | S X | = *)
    (* {c < [a ]^T> (c a b)} · ℸ_{ | S S S X |} μ^S X }. *)
  red.
  apply pathsinv0.
    unfold c.
    cbn -[universal_Smap S O].
    unshelve eapply universal_Smap_unique.
    - apply ℸ_Σalg_SS.
      exact a.
    - rewrite !assoc.
      cbn -[universal_Smap S O].
      etrans; revgoals.
      {
        apply cancel_postcomposition.
        apply pathsinv0.
        apply (η_universal_Smap (X := S X)).
      }
      etrans.
      {
        apply cancel_postcomposition.
        apply cancel_postcomposition.
        apply (Monad_law1 (T := S)).
      }
      rewrite id_left.
      etrans;[|apply assoc].
      eapply (pathscomp0 (b := _ · <ℸ_{ μ^S S X} | S X |>)); revgoals.
      {
        
      apply cancel_precomposition.
      etrans; [ | apply ((binprod_functor_comp ℸ))].
      cbn -[S].
      rewrite id_left.
      apply (maponpaths (fun u => < ℸ_{ {_} } u >)).
      apply pathsinv0.
        apply (Monad_law1 (T := S)).
      }
      unshelve eapply universal_Smap_unique.
      + cbn -[S].
        apply ℸ_Σalg_SS.
        exact a.

      + rewrite !assoc.
        rewrite 2!η_universal_Smap.
        rewrite 2!assoc'.
        apply cancel_precomposition.
        etrans;[|apply (binprod_functor_comp ℸ)].
        etrans;[apply pathsinv0,(binprod_functor_comp ℸ)|].
        cbn -[S].
        apply maponpaths.
        apply maponpaths.
        apply (Monad_law3 (T := S)).
      +
        eapply is_Σ_algebra_mor_comp.
        apply universal_Smap_is_Σ_algebra_mor.
        unfold ℸ_Σalg.
        apply ℸa_nat.
        apply pathsinv0,id_right.
        apply lift_Talg_double.
      + eapply is_Σ_algebra_mor_comp.
        apply universal_Smap_is_Σ_algebra_mor.
        apply μ_T_Σalg_mor.
    - eapply is_Σ_algebra_mor_comp.
      eapply is_Σ_algebra_mor_comp.
      apply μ_is_Σ_algebra_mor.
      apply universal_Smap_is_Σ_algebra_mor.
      apply ℸa_nat.
      apply pathsinv0,id_right.
      apply lift_Talg_double.
    - eapply is_Σ_algebra_mor_comp.
      apply universal_Smap_is_Σ_algebra_mor.
      apply ℸa_nat2.
      apply pathsinv0, id_left.
      Qed.



  (* cf json *)
  Definition nice_models {X} (s : Σ X --> X)(t : T X --> X)(g : X --> |ℸ_{X} X|) :=
    is_Σ_algebra_mor s <Σ ℸ_{[s;t]^M} | X| · {d X X} · ℸ_{|X|} S T {Oe X} · ℸ_{|X|} [s ; t]^M> g.
     (* { Σ g · Σ ℸ_{[s;t]^M} | X| · {d X X} · ℸ_{|X|} S T {Oe X} · ℸ_{|X|} [s ; t]^M = s · g }. *)

  (*
  Lemma f_eq {X}(s : Σ X --> X)(t : T X --> X)(f : X --> |ℸ_{S X} X|) :
    (* cf hyp_dalethS_alg_mor.json pour cette hypothese *)
    is_ℸS_algebra_mor (c t f) f < [s]^S > -> { f = η^S X · {c t f} · ℸ_{S η^S X} | {_} | · ℸ_{| {_}|} [ s ]^S }.
    Proof.
      intro halg.
      etrans; revgoals.
      {
        apply cancel_postcomposition.
        apply η_is_alg.
      }
      cbn -[S liftΣS].
    assert (h : isMonic < ℸ_{S [s]^S} |X|>) by admit.
    apply h.
    clear h.
    assert (h : isEpi < [s]^S >) by admit.
    apply h.
    clear h.

    etrans; revgoals.
    {
      apply halg.
    }
    etrans
*)

  (* Ca correspond au diagramme  f = Γ_{[s]^S} X · Γ_{η^S X} X · f (lemme D.6 du pdf
pour le commit 07f9d4d9b55eb4794305f3ebc5 ) *)
  Lemma additionnal_diag {X}(s : Σ X --> X)(t : T X --> X)(f : X --> |ℸ_{S X} X|) :
    (* cf hyp_dalethS_alg_mor.json pour cette hypothese *)
    is_ℸS_algebra_mor (c t f) f < [s]^S > ->
        {f · ℸ_{ η^S X} |X| · ℸ_{ [s ]^S} |X| = f }.

    intro halg.
    assert (h : isMonic < ℸ_{S [s]^S} |X|>) by admit.
    apply h.
    clear h.
    assert (h : isEpi < [s]^S >) by admit.
    apply h.
    clear h.
    rewrite !assoc.
    cbn -[S liftΣS].
    etrans; revgoals.
    {
      apply halg.
    }
    (* cf d6.json *)

assert(eq : { ℸ_{ [s ]^S} |X| · ℸ_{S [s ]^S} |X| = ℸ_{     [s ]^S} |X| · ℸ_{μ^S X} |X| }).
{
  bifunct_cancel ℸ.
  apply liftΣS_assoc.
}
etrans.
{
  repeat rewrite assoc'.
  do 3 apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { ℸ_{ η^S X} |X| · ℸ_{[s ]^S} |X| = ℸ_{ S [ s ]^S} |X| · ℸ_{ η^S S X} |X| }).
{
  bifunct_cancel ℸ.
  apply (nat_trans_ax (η S)).
}
etrans.
{
  apply cancel_postcomposition.
  repeat rewrite assoc'.
  do 2 apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { [s ]^S · f · ℸ_{ S [s ]^S} |X| = {c t f} · ℸ_{ |S S X|} [s]^S }).
{
  apply pathsinv0.
  apply halg.
}
etrans.
{
  do 2 apply cancel_postcomposition.
  apply eq.
}
clear eq.
assert(eq : { ℸ_{ |S S X| } [s]^S · ℸ_{ η^S S X} |X | = ℸ_{ η^S S X} |S X| · ℸ_{ |S X |} [s]^S }).
{
  bifunct_cancel ℸ.
  cbn -[S].
  rewrite id_left, id_right.
  apply idpath.
}
etrans.
{
  apply cancel_postcomposition.
  repeat rewrite assoc'.
  apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { ℸ_{ |S X| } [s]^S · ℸ_{μ^S X} |X| = ℸ_{ μ^S X} |S X| · ℸ_{ |S S X| } [s ]^S }).
{
  bifunct_cancel ℸ.
  cbn -[S].
  rewrite id_left, id_right.
  apply idpath.
}
etrans.
{
  repeat rewrite assoc'.
  do 2 apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { {c t f} · ℸ_{ η^S S X} |S X| · ℸ_{ μ^S X} |S X| = {c t f} }).
{
  apply c_η_μ.
}
etrans.
{
  apply cancel_postcomposition.
  apply eq.
}
clear eq.
 apply idpath.
 Admitted.





  Lemma appendixd {X} (s : Σ X --> X)(t : T X --> X)(f : X --> |ℸ_{S X} X|)
    (g := f · < ℸ_{ η^S X } |X|>):
    (* cf hyp_dalethS_alg_mor.json pour cette hypothese *)
    is_ℸS_algebra_mor (c t f) f < [s]^S >
    -> nice_models s t g.
    intro halg.
    generalize halg.
    unfold nice_models, is_ℸS_algebra_mor, is_algebra_mor.
    unfold g.
    intro eq.
    (* unshelve refine (let eq' := _ in let y := eq = eq' in _). *)
    (* norm_graph. *)
    (* assert (eq' ) *)
    apply  is_Σ_S_algebra_mor.
    unfold is_algebra_mor.
    rewrite !assoc.
    rewrite (functor_comp S).
    assert (h : isMonic < ℸ_{[s]^S} |X|>) by admit.
    apply h.
    clear h.
    etrans; revgoals.
    {
      rewrite !assoc'.
      do 2 apply cancel_precomposition.
      etrans; [ |apply (binprod_functor_comp ℸ)].
      etrans; revgoals.
      {
      apply (binprod_functor_cancel ℸ).
      apply idpath.
      apply pathsinv0.
      apply(nat_trans_ax (η S) _ _ <[s]^S>).
      }
      apply pathsinv0.
      apply (binprod_functor_comp ℸ).
    }
    etrans;revgoals.
    {
    rewrite !assoc.
    apply cancel_postcomposition.
    apply eq.
    }
    clear eq.
    eapply universal_Smap_unique.
    -  rewrite !assoc.
       cbn -[S universal_Smap O].
(* See appendixd.json *) 
assert(eq : { η^S X · S f = f · η^S ℸ_{ S X} X }).
{
  apply pathsinv0.
  apply (nat_trans_ax (η S)).
}
etrans.
{
  do 3 apply cancel_postcomposition.
  apply eq.
}
clear eq.
assert(eq : { η^S ℸ_{ S X} X · S ℸ_{ η^S X} |X| = ℸ_{ η^S X} |X| · η^S ℸ_{ X} X }).
{
  apply pathsinv0.
  apply (nat_trans_ax (η S)).
}
etrans.
{
  do 2 apply cancel_postcomposition.
  repeat rewrite assoc'.
  apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { η^S ℸ_{ X} X · [Σ ℸ_{ [s; t ]^M} |X |· {d X X} · ℸ_{| X|} S T {Oe X} · ℸ_{ |X|} [s; t ]^M ]^S = | ℸ_{ X} X | }).
{
  apply η_liftΣS.
}
etrans.
{
  apply cancel_postcomposition.
  repeat rewrite assoc'.
  do 2 apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { | ℸ_{ X} X | · ℸ_{     [s ]^S} |X| = ℸ_{     [s ]^S} |X| }).
{
  apply id_left.
}
etrans.
{
  repeat rewrite assoc'.
  do 2 apply cancel_precomposition.
  repeat rewrite assoc.
  apply id_left.
}
repeat rewrite assoc.
clear eq.
assert(eq : { f · ℸ_{ η^S X} |X| · ℸ_{     [s ]^S} |X| = f }).
{
  (*
  I don't know!
   *)
  eapply additionnal_diag.
  eassumption.
}
etrans.
{

  apply eq.
}
clear eq.
assert(eq : { f = f · ℸ_{ |S X|} η^S X · ℸ_{ |S X|} [s ]^S }).
{
  apply pathsinv0.
    etrans;[|apply id_right].
  etrans;[apply assoc'|].
  apply cancel_precomposition.
  etrans.
  apply pathsinv0.
  apply (binprod_functor_compl ℸ).
  etrans; [| apply (binprod_functor_id ℸ)].
  apply (binprod_functor_cancel ℸ).
  apply η_liftΣS.
  apply idpath.
}
etrans.
{

  apply eq.
}
clear eq.
assert(eq : { f · ℸ_{ |S X|} η^S X = η^S X · {c t f} · ℸ_{ η^S S X} |S X| }).
{
  apply η_is_almost_alg.
}
etrans.
{
  apply cancel_postcomposition.
  apply eq.
}
clear eq.
assert(eq : { ℸ_{ η^S S X} |S X| · ℸ_{| S X|} [s ]^S = ℸ_{| S S X|} [s ]^S · ℸ_{ η^S S X} |X| }).
{
  apply pathsinv0.
  apply (binprod_functor_comp_swap ℸ).
}
etrans.
{
  repeat rewrite assoc'.
  do 2 apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
 apply idpath.
 Admitted.

