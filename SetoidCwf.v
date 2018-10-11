(* -*- coq-prog-args : ("-allow-sprop")-*-  *)

Require Import MiniHoTT.


Inductive sUnit : SProp := stt.

Record sSigma {A:SProp} (P : A -> SProp) : SProp := { sπ1 : A; sπ2 : P sπ1 }.

Notation "{ x : A 's&' P }" := (@sSigma A (fun x => P)) (at level 0, x at level 99) : type_scope.  Notation "( x ;; y )" := (Build_sSigma _ _ x y).  Notation "x ..1" := (@sπ1 _ _ x) (at level 3, format "x '..1'").  Notation "x ..2" := (@sπ2 _ _ x) (at level 3, format "x '..2'").

Record Subset {A:Type} (P : A -> SProp) := { val : A; in_subset : P val }.

Notation "{ x : A 's|' P }" := (@Subset A (fun x => P)) (at level 0, x at level 99) : type_scope.  Notation "( x 's|' y )" := (Build_Subset _ _ x y).

Arguments val {_ _} _.  Arguments in_subset {_ _} _.

Record sBox (A:SProp) : Prop := sbox { sunbox : A }.



Module Type CwF.
  Parameter Con : Type.
  Parameter Ty  : Con -> Type.
  Parameter Tms : Con -> Con -> Type.
  Parameter Tm  : forall (Γ : Con), Ty Γ -> Type.

  Parameter nil  : Con.
  Parameter cons : forall (Γ : Con), Ty Γ -> Con.
  Notation "∙" := nil.
  Notation "( x , y )" := (cons x y).

  Parameter TyS : forall {Γ Δ}, Tms Γ Δ -> Ty Δ -> Ty Γ.
  Notation " A [ σ ]T " := (TyS σ A) (at level 3).
  Parameter TmS  : forall {Γ Δ A}(σ : Tms Γ Δ), Tm Δ A -> Tm Γ A[σ]T.
  Notation " t [ σ ]t " := (TmS σ t) (at level 3).

  Parameter ε    : forall {Γ}, Tms Γ nil.
  Parameter id   : forall {Γ}, Tms Γ Γ.
  Parameter comp : forall {Γ Δ Σ}, Tms Δ Σ -> Tms Γ Δ -> Tms Γ Σ.
  Parameter ext  : forall {Γ Δ A}(σ : Tms Γ Δ), Tm Γ A[σ]T -> Tms Γ (Δ, A).
  Notation "( x ,s y )" := (ext x y).
  Infix "∘" := comp (at level 42, right associativity).
  Parameter π₁   : forall {Γ Δ A}, Tms Γ (Δ, A) -> Tms Γ Δ.
  Parameter π₂   : forall {Γ Δ A}(σ : Tms Γ (Δ, A)), Tm Γ A[π₁ σ]T.

  Parameter idl     : forall {Γ Δ}{σ : Tms Γ Δ}, id ∘ σ = σ.
  Parameter idr     : forall {Γ Δ}{σ : Tms Γ Δ}, σ ∘ id = σ.
  Parameter ass     : forall {Γ Δ Σ Ξ}{σ : Tms Σ Ξ}{δ : Tms Δ Σ}{ν : Tms Γ Δ},
      σ ∘ (δ ∘ ν) = (σ ∘ δ) ∘ ν.
  Parameter TyId    : forall {Γ}{A : Ty Γ}, TyS id A = A.
  Parameter TyComp  : forall {Γ Δ Σ}{A : Ty Σ}{σ : Tms Δ Σ}{δ : Tms Γ Δ},
      TyS δ (TyS σ A) = TyS (comp σ δ) A.
  Parameter π₁β     : forall {Γ Δ A}{σ : Tms Γ Δ}{t : Tm Γ A[σ]T}, π₁ (σ ,s t) = σ.
  Parameter π₂β     : forall {Γ Δ A}{σ : Tms Γ Δ}{t : Tm Γ (TyS σ A)},
      transport (fun σ => Tm Γ A[σ]T) π₁β (π₂ (σ ,s t)) = t.
  Parameter extComp : forall {Γ Δ Σ}{δ : Tms Γ Δ}{σ : Tms Σ Γ}{A : Ty Δ}{a : Tm Γ A[δ]T},
      (δ ,s a) ∘ σ = (δ ∘ σ ,s TyComp # a[σ]t).
  Parameter extη    : forall {Γ Δ A}{σ : Tms Γ (Δ, A)}, (π₁ σ ,s π₂ σ) = σ.

  Definition TmId   : forall {Γ A} (t : Tm Γ A), TyId # t[id]t = t.
    intros Γ A t. refine (ap _ π₂β^ @ _).
    pose proof (apD π₂ (idr^ @ @extComp _ _ _ id id _ (TyId^ # t))).

    rewrite (transport_compose (Tm Γ) (fun σ => A[σ]T)).
    rewrite <- transport_pp.
  Abort.


  (* Definitions *)
  Definition wk {Γ}{A : Ty Γ} : Tms (Γ, A) Γ := π₁ id.
  Definition vz {Γ}{A : Ty Γ} : Tm (Γ, A) (TyS wk A) := π₂ id.
  Definition vs {Γ}{A B : Ty Γ}(t : Tm Γ A) : Tm (Γ, B) (TyS wk A) := TmS wk t.
  Definition drop {Γ Δ}{A : Ty Γ}(σ : Tms Γ Δ) : Tms (Γ, A) Δ := σ ∘ wk.
  Definition keep {Γ Δ}{A : Ty Δ}(σ : Tms Γ Δ) : Tms (Γ, A[σ]T) (Δ, A)
    := (drop σ ,s TyComp # vz).
  Notation " σ ^^ A " := (@keep _ _ A σ) (at level 30).
  Definition ext' {Γ} {A : Ty Γ} (t : Tm Γ A) : Tms Γ (Γ , A)
    := (id ,s TyId^ # t).
  Notation "<< t >>" := (ext' t) (at level 1000).

  (* Universe *)
  Parameter U   : forall {Γ}, Ty Γ.
  Parameter El  : forall {Γ}, Tm Γ U -> Ty Γ.
  Parameter US  : forall {Γ Δ}{σ : Tms Γ Δ}, TyS σ U = U.
  Parameter ElS : forall {Γ Δ}{σ : Tms Γ Δ}{A : Tm Δ U},
      (El A)[σ]T = El (transport (Tm Γ) US A[σ]t).

  (* Π types *)
  Parameter Π   : forall {Γ}(A : Ty Γ), Ty (Γ, A) -> Ty Γ.
  Parameter lam  : forall {Γ A B}, Tm (Γ, A) B -> Tm Γ (Π A B).
  Parameter app  : forall {Γ A B}, Tm Γ (Π A B) -> Tm (Γ, A) B.

  Parameter ΠS : forall {Γ Δ}{σ : Tms Γ Δ}{A : Ty Δ}{B : Ty (Δ, A)},
      TyS σ (Π A B) = Π (TyS σ A) (TyS (keep σ) B).
  Parameter lamS : forall {Γ Δ}{δ : Tms Γ Δ}{A : Ty Δ}{B : Ty (Δ, A)}{t : Tm (Δ, A) B},
      transport (Tm Γ) ΠS (TmS δ (lam t)) = lam (TmS (keep δ) t).
  Parameter Πβ : forall {Γ}{A : Ty Γ}{B : Ty (Γ, A)}{t : Tm (Γ, A) B}, app (lam t) = t.


  Definition app' {Γ} {A} {B} (t : Tm Γ (Π A B)) (u : Tm Γ A) : Tm Γ B[<<u>>]T
    := (app t)[_]t.


  (* π₁∘ *)
  Definition π₁_comp {Γ Δ Θ}{A : Ty Δ}{δ : Tms Γ (Δ , A)}{ρ : Tms Θ Γ}
    : π₁ δ ∘ ρ = π₁ (δ ∘ ρ).
    etransitivity. symmetry. eapply π₁β.
    eapply ap. etransitivity.
    symmetry. eapply extComp.
    eapply (ap (fun z => z ∘ ρ)), extη.
  Defined.

  Definition π₁idβ {Γ Δ}{ρ : Tms Γ Δ}{A : Ty Δ}{t : Tm Γ A[ρ]T}
    : π₁ id ∘ (ρ ,s t) = ρ.
    etransitivity. eapply π₁_comp.
    etransitivity. 2: eapply π₁β.
    eapply ap, idl.
  Defined.

  Definition ap_π₂ {Γ Δ} {A : Ty Δ} {ρ₀ ρ₁ : Tms Γ (Δ , A)} (ρ₂ : ρ₀ = ρ₁)
    : ap (fun ρ => A[π₁ ρ]T) ρ₂ # π₂ ρ₀ = π₂ ρ₁.
    destruct ρ₂; reflexivity.
  Defined.

  Definition ap_π₂' {Γ Δ} {A : Ty Δ} {ρ₀ ρ₁ : Tms Γ (Δ , A)} (ρ₂ : ρ₀ = ρ₁)
    : π₂ ρ₀ = ap (fun ρ => A[π₁ ρ]T) ρ₂^ # π₂ ρ₁.
    destruct ρ₂; reflexivity.
  Defined.

  Notation "'TyS'' A" := (fun σ => TyS σ A) (at level 30).

  Definition π₂_subst {Γ Δ Θ} {A : Ty Δ} {δ : Tms Γ (Δ , A)} {ρ : Tms Θ Γ}
    : TyComp @ ap (fun σ => A[σ]T) π₁_comp # (π₂ δ)[ ρ ]t =  π₂ (δ ∘ ρ).
    (* : TyComp @ ap10 (ap TyS π₁_comp) A # (π₂ δ)[ ρ ]t =  π₂ (δ ∘ ρ). *)
    etransitivity. 2: exact (ap_π₂ (ap (fun z => z ∘ _) extη)).
    rewrite transport_pp. rewrite <- (@π₂β _ _ A (π₁ δ ∘ ρ) (TyComp # (π₂ δ) [ρ ]t)).
    eapply moveL_transport_p. etransitivity.
    2: exact (ap_π₂ extComp^).
    rewrite (transport_compose (Tm Θ) (TyS' A)).
    rewrite !(ap_compose (π₁) (TyS' A)).
    rewrite <- !transport_pp. eapply ap10, ap.
    rewrite concat_p_pp. refine (_ @@ 1 @ _). exact (ap_pp _ _ _)^.
    refine (1 @@ (ap_V _ _)^ @ _ @ _).
    exact (ap_pp _ _ _)^. eapply ap.
    unfold π₁_comp. rewrite concat_p_pp. rewrite concat_pV, concat_1p.
    rewrite ap_pp. rewrite concat_pp_p. rewrite concat_pV. apply concat_p1.
  Defined.

End CwF.



Module SetoidModel : CwF.
  Set Primitive Projections.


  Record Setoid :=
    { carrier : Type;
      eq : carrier -> carrier -> SProp;
      refl : forall x, eq x x;   
      sym : forall {x y}, eq x y -> eq y x;
      trans : forall {x y z}, eq x y -> eq y z -> eq x z;
    }.

  Arguments eq {_} _ _.
  Arguments refl {_} _.
  Arguments sym {_ _ _} _.
  Arguments trans {_ _ _ _} _ _.

  Coercion carrier : Setoid >-> Sortclass.

  Notation " γ ~ γ' " := (eq γ γ') (at level 20).


  Record SetoidMap (Γ Δ : Setoid) :=
    { map : Γ -> Δ;
      map_eq : forall γ γ', γ ~ γ' -> map γ ~ map γ'
    }.

  Arguments map {_ _} _ _.
  Arguments map_eq {_ _} _ {_ _} _.

  Notation "A ⇨ B" := (SetoidMap A B) (at level 80).

  Coercion map : SetoidMap >-> Funclass.

  Record SetoidFam (Γ : Setoid) :=
    { Fam : Γ -> Setoid;
      ι : forall γ γ', γ ~ γ' -> Fam γ ⇨ Fam γ'; 
      coh1 : forall γ x, ι γ γ (refl γ) x ~ x;   
      coh3 : forall x y z (p : x ~ y) (q : y ~ z) u,
          ι y z q (ι x y p u) ~ ι x z (trans p q) u;
    }.

  Arguments ι {_ _ _ _} _.
  Arguments coh1 {_ _ _} _.
  Arguments coh3 {_ _ _ _ _} _ _ _.

  Coercion Fam : SetoidFam >-> Funclass.

  Definition coh2 {Γ} {A : SetoidFam Γ} {γ γ' : Γ} (p : γ ~ γ') (x : A γ)
    : ι (sym p) (ι p x) ~ x.
  Proof.
    eapply trans. eapply coh3.
    exact (@coh1 Γ _ _ _).
  Defined.

  Definition coh2' {Γ} {A : SetoidFam Γ} {γ γ' : Γ} (p : γ ~ γ') (x : A γ')
    : ι p (ι (sym p) x) ~ x.
  Proof.
    eapply trans. eapply coh3.
    exact (@coh1 Γ _ _ x).
  Defined.

  Record SetoidFam' (Γ : Setoid) :=
    { Fam' : Γ -> Type ;
      eq'   : forall {γ γ'}, γ ~ γ' -> Fam' γ -> Fam' γ' -> SProp ;
      coe'  : forall {γ γ'}, γ ~ γ' -> Fam' γ -> Fam' γ' ;
      coh'   : forall {γ γ'} (p : γ ~ γ') x, eq' p x (coe' p x) ;
      Frefl': forall γ x, eq' (refl γ) x x ;
      Fsym' : forall γ γ' (p : γ ~ γ') x y, eq' p x y -> eq' (sym p) y x ;
      Ftrans' : forall γ γ' γ'' (p : γ ~ γ') (q : γ' ~ γ'') x y z,
          eq' p x y -> eq' q y z -> eq' (trans p q) x z ;
    }.

  Arguments coe' {Γ s γ γ'} p x.


  Record Section Γ (A : SetoidFam Γ) :=
    { tm : forall γ, A γ;
      resp : forall γ γ' (p : γ ~ γ'), ι p (tm γ) ~ tm γ'
    }.

  Arguments tm {Γ A} s γ.
  Arguments resp {Γ A s γ γ'} p.
  Coercion tm : Section >-> Funclass.

  Definition Con : Type := Setoid.
  Definition Ty  : Con -> Type := SetoidFam.
  Definition Tms : Con -> Con -> Type := SetoidMap.
  Definition Tm  : forall (Γ : Con), Ty Γ -> Type := Section.

  Definition nil : Con :=
    (Build_Setoid unit (fun _ _ => sUnit) (fun _ => stt)
                  (fun _ _ _ => stt) (fun _ _ _ _ _ => stt)).

  Definition cons : forall (Γ : Con), Ty Γ -> Con.
  Proof.
    intros Γ A. refine (Build_Setoid {γ : Γ & A γ}
                         (fun x y => { p : x.1 ~ y.1 s& ι p x.2 ~ y.2})
                         _ _ _).
    - intro w. exists (refl w.1). exact (coh1 w.2).
    - intros w z p. exists (sym p..1).
      eapply trans.
      2: exact (coh2 p..1 w.2).
      apply map_eq. eapply sym. exact p..2.
    - intros x y z p q. exists (trans p..1 q..1).
      eapply trans. 2: exact q..2.
      eapply trans. eapply sym, coh3.
      eapply map_eq. exact p..2.
  Defined.
  Notation "∙" := nil.
  Notation "( x , y )" := (cons x y).

  Definition Π  : forall {Γ}(A : Ty Γ), Ty (Γ, A) -> Ty Γ.
  Proof.
    intros Γ A B. unshelve econstructor.
    - intro γ. unshelve econstructor.
      + refine ({f : forall (x : A γ), B (γ; x) s| _}).
        refine (forall x y (p : eq x y), eq (ι _ (f x)) (f y)). cbn.
        exact (refl γ;; trans (coh1 x) p).
      + intros f g.
        refine (forall x y (p : eq x y), eq (ι _ (val f x)) (val g y)).
        exact (refl γ;; trans (coh1 x) p).
      + intros f x. apply (in_subset f).
      + cbn; intros f g e x y p.
        eapply trans. eapply (in_subset g).
        eapply trans. 2: unshelve eapply (in_subset f).
        3: exact p. apply sym. eapply e.
      + cbn; intros f g h e1 e2 x y p.
        eapply trans. 2: eapply e2. eapply map_eq.
        eapply trans. 2: unshelve eapply e1.
        3: exact (sym p).
        eapply sym. eapply (in_subset f).
    - intros γ γ' p; cbn. unshelve econstructor; cbn.
      + cbn; intros [f Hf]. unshelve econstructor.
        * intro x. unshelve refine (ι _ (f (ι (sym p) x))).
          cbn. exists p. apply coh2'.
        * intros x y q; cbn.
          eapply trans.
          2: unshelve eapply map_eq, (Hf (ι (sym p) x) (ι (sym p) y)).
          2: eapply map_eq, q.
          eapply trans. eapply coh3.
          eapply trans. 2: eapply sym, coh3.
          apply refl.
      + cbn; intros [f Hf] [g Hg] e x y q; cbn in *.
        eapply trans. 2: unshelve eapply map_eq, e.
        2: exact (ι (sym p) x). 2: apply map_eq, q.
        eapply trans. eapply coh3.
        eapply trans. 2: eapply sym, coh3.
        eapply refl.
    - cbn; intros γ [f Hf] x y p; cbn in *.
      eapply trans. eapply coh3.
      eapply trans. 2: unshelve eapply (Hf (ι (refl γ) x) y).
      2: exact (trans (coh1 x) p). apply refl.
    - cbn; intros γ γ' γ'' p p' [f Hf] x y q; cbn.
      eapply trans. eapply coh3.
      eapply trans. eapply coh3.
      simple refine (let X := Hf (ι (sym p) (ι (sym p') x))
                                 (ι (sym (trans p p')) y) _ in _). {
        eapply trans. eapply coh3.
        eapply map_eq, q. }
      clearbody X.
      eapply trans. 2: eapply map_eq, X.
      eapply trans. 2: eapply sym, coh3.
      apply refl.
  Defined.

  Definition TyS : forall {Γ Δ}, Tms Γ Δ -> Ty Δ -> Ty Γ.
  Proof.
    intros Γ Δ σ A. unshelve econstructor.
    - exact (fun γ => A (σ γ)).
    - intros γ γ' p; cbn. unshelve econstructor.
      + eapply ι. eapply map_eq, p.
      + intros x y q; cbn.
        eapply map_eq, q.
    - cbn; intros γ x. exact (@coh1 Δ _ _ x).
    - cbn; intros x y z p q u. exact (coh3 (Γ:=Δ)_ _ u).
  Defined.

  Definition ε : forall {Γ}, Tms Γ nil.
  Proof.
    intros Γ. unshelve econstructor.
    all: intros; repeat constructor.
  Defined.

  Definition id  : forall {Γ}, Tms Γ Γ.
  Proof.
    intros Γ. unshelve econstructor.
    exact idmap. intros γ γ' H; exact H.
  Defined.

  Definition comp : forall {Γ Δ Σ}, Tms Δ Σ -> Tms Γ Δ -> Tms Γ Σ.
  Proof.
    intros Γ Δ Σ σ δ. unshelve econstructor.
    exact (fun γ => σ (δ γ)).
    intros γ γ' p; cbn. eapply map_eq, map_eq, p.
  Defined.

  Definition ext  : forall {Γ Δ A}(σ : Tms Γ Δ), Tm Γ (TyS σ A) -> Tms Γ (Δ, A).
  Proof.
    intros Γ Δ A σ t. unshelve econstructor.
    - intro γ. exists (σ γ). exact (t γ).
    - cbn; intros γ γ' p. unshelve eexists.
      eapply map_eq, p. eapply (resp (s:=t)).
  Defined.
  Notation "( x ,s y )" := (ext x y).
  Infix "∘" := comp (at level 42, right associativity).

  Definition π₁ : forall {Γ Δ A}, Tms Γ (Δ, A) -> Tms Γ Δ.
  Proof.
    intros Γ Δ A σ. unshelve econstructor.
    - exact (fun γ => (σ γ).1).
    - intros γ γ' p; cbn. exact (map_eq σ p)..1.
  Defined.

  Definition π₂  : forall {Γ Δ A}(σ : Tms Γ (Δ, A)), Tm Γ (TyS (π₁ σ) A).
  Proof.
    intros Γ Δ A σ. unshelve econstructor.
    - exact (fun γ => (σ γ).2).
    - intros γ γ' p; cbn. exact (map_eq σ p)..2.
  Defined.

  Definition lam : forall {Γ A B}, Tm (Γ, A) B -> Tm Γ (Π A B).
  Proof.
    intros Γ A B t. unshelve econstructor.
    - intro γ; cbn. exists (fun x => t (γ; x)).
      intros; apply resp.
    - intros γ γ' p x y q; cbn.
      eapply trans. eapply coh3.
      eapply resp.
  Defined.

  Definition app : forall {Γ A B}, Tm Γ (Π A B) -> Tm (Γ, A) B.
  Proof.
    intros Γ A B t. unshelve econstructor.
    - intros [γ x]; cbn. exact (val (t γ) x).
    - intros [γ x] [γ' x'] p; cbn.
      (* pose proof ((t γ').2).  cbn in X. (ι p.1 x) x' p.2). *)
      eapply trans. 2: exact (resp (s:=t) p..1 _ _ p..2).
      cbn. set (t γ) in *. clearbody c.
      destruct c as [c1 c2]. cbn. clear t.
      eapply sym. eapply trans. eapply coh3.
      eapply trans. 2: eapply map_eq.
      2: unshelve eapply (c2 ((ι (sym p..1)) ((ι p..1) x)) x).
      2: eapply coh2. eapply sym.
      exact (coh3 _ _ _).
  Defined.

  Definition TmS : forall {Γ Δ A}(σ : Tms Γ Δ), Tm Δ A -> Tm Γ (TyS σ A).
  Proof.
    intros Γ Δ A σ t. unshelve econstructor.
    - exact (fun γ => (t (σ γ))).
    - intros γ γ' p; cbn. exact (resp (map_eq σ p)).
  Defined.

  Definition TyId : forall {Γ}{A : Ty Γ}, TyS id A = A.
  Proof.
    reflexivity.
  Defined.

  Definition TyComp : forall {Γ Δ Σ}{A : Ty Σ}{σ : Tms Δ Σ}{δ : Tms Γ Δ}, TyS δ (TyS σ A) = TyS (comp σ δ) A.
  Proof.
    reflexivity.
  Defined.

  Definition idl : forall {Γ Δ}{σ : Tms Γ Δ}, comp id σ = σ.
  Proof.
    reflexivity.
  Defined.

  Definition idr : forall {Γ Δ}{σ : Tms Γ Δ}, comp σ id = σ.
  Proof.
    reflexivity.
  Defined.

  Definition ass : forall {Γ Δ Σ Ξ}{σ : Tms Σ Ξ}{δ : Tms Δ Σ}{ν : Tms Γ Δ}, comp σ (comp δ ν) = comp (comp σ δ) ν.
  Proof.
    reflexivity.
  Defined.


  Definition π₁β : forall {Γ Δ A}{σ : Tms Γ Δ}{t : Tm Γ (TyS σ A)}, π₁ (ext σ t) = σ.
  Proof.
    reflexivity.
  Defined.

  Definition π₂β : forall {Γ Δ A}{σ : Tms Γ Δ}{t : Tm Γ (TyS σ A)}, transport (fun σ => Tm Γ (TyS σ A)) π₁β (π₂ (ext σ t)) = t.
  Proof.
    reflexivity.
  Defined.

  Definition extη : forall {Γ Δ A}{σ : Tms Γ (Δ, A)}, ext (π₁ σ) (π₂ σ) = σ.
  Proof.
    reflexivity.
  Defined.

  Definition extComp : forall {Γ Δ Σ}{δ : Tms Γ Δ}{σ : Tms Σ Γ}{A : Ty Δ}{a : Tm Γ (TyS δ A)}, comp (ext δ a) σ = ext (comp δ σ) (transport (Tm Σ) TyComp (TmS σ a)).
  Proof.
    reflexivity.
  Defined.

  Definition wk {Γ}{A : Ty Γ} : Tms (Γ, A) Γ := π₁ id.
  Definition vz {Γ}{A : Ty Γ} : Tm (Γ, A) (TyS wk A) := π₂ id.
  Definition vs {Γ}{A B : Ty Γ}(t : Tm Γ A) : Tm (Γ, B) (TyS wk A) := TmS wk t.
  Definition drop {Γ Δ}{A : Ty Γ}(σ : Tms Γ Δ) : Tms (Γ, A) Δ := comp σ wk.
  Definition keep {Γ Δ}{A : Ty Δ}(σ : Tms Γ Δ) : Tms (Γ, (TyS σ A)) (Δ, A) := ext (drop σ) (transport (Tm _) TyComp vz).

  Definition ΠS : forall {Γ Δ}{σ : Tms Γ Δ}{A : Ty Δ}{B : Ty (Δ, A)}, TyS σ (Π A B) = Π (TyS σ A) (TyS (keep σ) B).
  Proof.
    reflexivity.
  Defined.

  Definition lamS : forall{Γ Δ}{δ : Tms Γ Δ}{A : Ty Δ}{B : Ty (Δ, A)}{t : Tm (Δ, A) B}, transport (Tm Γ) ΠS (TmS δ (lam t)) = lam (TmS (keep δ) t).
  Proof.
    reflexivity.
  Defined.

  Definition Πβ : forall {Γ}{A : Ty Γ}{B : Ty (Γ, A)}{t : Tm (Γ, A) B}, app (lam t) = t.
  Proof.
    reflexivity.
  Defined.

  (* Todo: provide a better universe *)
  Definition U  : forall {Γ}, Ty Γ.
    intros Γ. unshelve econstructor.
    - intros _. exact nil.
    - cbn. intros; apply id.
    - cbn. intros; econstructor.
    - cbn. intros; econstructor.
  Defined.

  Definition El : forall {Γ}, Tm Γ U -> Ty Γ.
    intros Γ _. unshelve econstructor.
    - intros _. exact nil.
    - cbn. intros; apply id.
    - cbn. intros; econstructor.
    - cbn. intros; econstructor.
  Defined.

  Definition US : forall {Γ Δ}{σ : Tms Γ Δ}, TyS σ U = U.
  Proof.
    reflexivity.
  Defined.

  Definition ElS : forall {Γ Δ}{σ : Tms Γ Δ}{A : Tm Δ U}, TyS σ (El A) = El (transport (Tm Γ) US (TmS σ A)).
  Proof.
    reflexivity.
  Defined.



  Definition ext' {Γ} {A : Ty Γ} (t : Tm Γ A) : Tms Γ (Γ , A)
    := (id ,s transport (Tm Γ) TyId^ t).

  Notation " A [ σ ]T " := (TyS σ A) (at level 3).
  Notation " σ ^^ A " := (@keep _ _ A σ) (at level 30).
  Notation "<< t >>" := (ext' t) (at level 1000).
  Notation " t [ σ ]t " := (TmS σ t) (at level 3).

  Definition app' {Γ} {A} {B} (t : Tm Γ (Π A B)) (u : Tm Γ A) : Tm Γ B[<<u>>]T
    := (app t)[_]t.

  (* π₁∘ *)
  Definition π₁_comp {Γ Δ Θ}{A : Ty Δ}{δ : Tms Γ (Δ , A)}{ρ : Tms Θ Γ}
    : π₁ δ ∘ ρ = π₁ (δ ∘ ρ).
    etransitivity. symmetry. eapply π₁β.
    eapply ap. etransitivity.
    symmetry. eapply extComp.
    eapply (ap (fun z => z ∘ ρ)), extη.
  Defined.

  (* π₁idβ *)
  Definition π₁idβ {Γ Δ}{ρ : Tms Γ Δ}{A : Ty Δ}{t : Tm Γ A[ρ]T}
    : π₁ id ∘ (ρ ,s t) = ρ.
    etransitivity. eapply π₁_comp.
    etransitivity. 2: eapply π₁β.
    eapply ap, idl.
  Defined.

  Definition Eq {Γ} (A: Ty Γ) (t u : Tm _ A) : Ty Γ.
  Proof.
    unshelve econstructor.
    - intros γ; unshelve econstructor.
      + exact (sBox (t γ ~ u γ)).
      + exact (fun _ _ => sUnit).
      + now intro.
      + now intro.
      + now intro.
    - intros γ γ' p; cbn. unshelve econstructor; cbn.
      + intros [q]. apply sbox.
        eapply trans. 2: exact (resp (s:=u) p).
        eapply trans. eapply sym. exact (resp (s:=t) p).
        apply map_eq. exact q.
      + trivial.
    - cbn. exact (fun _ _ => stt).
    - cbn. exact (fun _ _ _ _ _ _ => stt).
  Defined.


  Definition ref {Γ} {A: Ty Γ} (t : Tm _ A) : Tm _ (Eq A t t).
  Proof.
    unshelve econstructor.
    - cbn; intros. apply sbox. apply refl.
    - cbn; intros. constructor.
  Defined.

  Definition transport {Γ} {A: Ty Γ} {t u : Tm _ A} (e : Tm _ (Eq A t u))
             (P : Ty (Γ, A)) (α : Tm Γ (P[<<t>>]T))
    : Tm _ (P[<<u>>]T).
  Proof.
    unshelve econstructor.
    - intros γ; cbn. eapply ι. 2: exact (α γ).
      cbn. exists (refl _). eapply trans. eapply coh1. exact (sunbox _ (e γ)).
    - intros γ γ' p; cbn.
      eapply trans.
      2: eapply (map_eq _ (resp (s:=α) p)). cbn.
      eapply trans. eapply coh3.
      eapply sym.
      exact (@coh3 (Γ, A) P ((<<t>>) γ) (γ'; t γ') (γ'; u γ') (p;; @resp Γ A t γ γ' p) (@refl Γ γ';; @trans (A γ') _ _ _ (@coh1 Γ A γ' (t γ')) (sunbox _ (e γ'))) (α γ)).
  Defined.

  Definition paths_Tm Γ A (t u : Tm Γ A) (p : tm t = tm u) : t = u.
  Proof.
    destruct t, u; cbn in p. destruct p. reflexivity.
  Defined.


  Definition ap_π₂ {Γ Δ} {A : Ty Δ} {ρ₀ ρ₁ : Tms Γ (Δ , A)} (ρ₂ : ρ₀ = ρ₁)
    : ap (fun ρ => A[π₁ ρ]T) ρ₂ # π₂ ρ₀ = π₂ ρ₁.
    destruct ρ₂; reflexivity.
  Defined.

  Definition ap_π₂' {Γ Δ} {A : Ty Δ} {ρ₀ ρ₁ : Tms Γ (Δ , A)} (ρ₂ : ρ₀ = ρ₁)
    : π₂ ρ₀ = ap (fun ρ => A[π₁ ρ]T) ρ₂^ # π₂ ρ₁.
    destruct ρ₂; reflexivity.
  Defined.
  Notation "'TyS'' A" := (fun σ => TyS σ A) (at level 30).

  Definition π₂_subst {Γ Δ Θ} {A : Ty Δ} {δ : Tms Γ (Δ , A)} {ρ : Tms Θ Γ}
    : TyComp @ ap (fun σ => A[σ]T) π₁_comp # (π₂ δ)[ ρ ]t =  π₂ (δ ∘ ρ).
    reflexivity.
  Defined.

  
  Definition transport_weakly_computes {Γ} (A: Ty Γ) (t : Tm Γ A)
             (P : Ty (Γ, A)) (α : Tm Γ P[<<t>>]T)
    : Tm _ (Eq _ (transport (ref t) P α) α).
  Proof.
    unshelve econstructor.
    - intro; cbn. apply sbox. apply coh1.
    - intros γ γ' p. cbn. econstructor.
  Defined.

  Section Funext.
    Context {Γ} (A : Ty Γ)(B : Ty (Γ , A)) (f g : Tm Γ (Π A B))
            (e : Tm Γ (Π A (Eq B (app f) (app g)))).

    Definition funext : Tm Γ (Eq (Π A B) f g).
    Proof.
      unshelve econstructor.
      - cbn. intros γ;apply sbox;intros x y p.
        eapply trans.
        2: exact (sunbox _ (val (e γ) y)).
        exact (in_subset (f γ) _ _ p).
      - intros γ γ' p; cbn. constructor.
    Defined.


    Context (x₀ : Tm Γ A).

    Local Definition Bx₀ : Ty Γ
      := (B[<<x₀>>]T).

    Local Definition σfx₀ : Tms Γ (Γ, Bx₀)
      := (<<app' f _>>).

    Local Definition σgx₀ : Tms Γ (Γ, Bx₀)
      := (<<app' g _>>).


    Context (P : Ty (Γ, Bx₀)) (u : Tm Γ (P[σfx₀]T)).

    Local Definition t1 : Tm Γ (P[σgx₀]T)
      := @transport Γ Bx₀ (app' f x₀) (app' g x₀) (app' e x₀) P u.

    Local Definition P' : Ty (Γ, Π A B).
    Proof.
      refine (P[_]T).
      unshelve eapply ext. apply wk.
      (* Γ, f |- f x₀ : B x₀ *)
      exact (app' (ΠS # (vz (A:=Π A B))) (x₀[_]t)).
    Defined.

    Local Definition t2 : Tm _ (P[σgx₀]T)
      := @transport Γ (Π A B) f g funext P' u.

    Time Definition eq1 : t1 = t2 := @eq_refl _ t1.

    Time Definition eq2 : t1 = t2 := @eq_refl _ t2.
  End Funext.

End SetoidModel.













