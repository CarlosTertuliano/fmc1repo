
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hp,
  intro hpn,
  apply hpn,
  assumption,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hnp,
  by_contra hboom, --como usar o (RAA)
  apply hnp,
  assumption,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  -- separando a conjunção
  intro hnp,
  by_contra hboom,
  apply hnp,
  assumption,
  -- organizando cada uma das demonstrações separadamente
  intro hp,
  intro hpn,
  apply hpn,
  assumption,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro p_q,
  cases p_q,
  -- Caso P
  right,
  assumption,
  -- Caso Q
  left,
  assumption,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro peq,
  cases peq,
  split,
  -- Demonstre Q
  assumption,
  -- Demonstre P
  assumption,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro Hp_q,
  intro Hp,
  cases Hp_q,
  -- Caso ¬P
  have Hboom : false := Hp_q Hp,
  contradiction,

  -- Caso Q
  assumption,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro Hp_q,
  intro Np,
  cases Hp_q,  
  -- Caso P
  have Hp : false := Np Hp_q,
  contradiction,
  
  -- Caso Q
  assumption,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro Hpq,
  intro Nq,
  intro Hp,
  have Hq : Q := Hpq Hp,
  contradiction, 
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro HNqp,
  intro Hp,
  by_contra Hboom,
  have HNp : ¬P := HNqp Hboom,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  -- Demonstrar Right
  intro Hpq,
  intro Nq,
  intro Hp,
  have Hq : Q := Hpq Hp,
  contradiction,

  -- Demonstrar Left
  intro HNqp,
  intro Hp,
  by_contra Hboom,
  have HNp : ¬P := HNqp Hboom,
  contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro NT,
  have p_or_p : P ∨ ¬P,  
  right,
  intro Hp,
  apply NT,
  left,
  assumption,
  apply NT,
  assumption,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro Hpqp,
  intro HNp,
  apply HNp,
  have Hpq: P → Q,
  intro Hp,
  contradiction,
  apply Hpqp,
  assumption,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro Hp_or_q,
  intro Hnot_p_and_q,
  cases Hnot_p_and_q,
  cases Hp_or_q,
  -- Caso P
  have Hp : false := Hnot_p_and_q_left Hp_or_q,
  assumption,
  -- Caso Q
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro Hp_and_q,
  intro HNp_or_q,
  cases Hp_and_q,
  cases HNp_or_q,
  -- Caso ¬P
  contradiction,
  -- Caso ¬Q
  have Hp : false := HNp_or_q Hp_and_q_right,
  assumption,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro HNp_or_q,
  split,
  -- Demonstre ¬P
  intro Hp,
  have p_or_q : P ∨ Q,
  left,
  assumption,
  have Np_or_q : false := HNp_or_q p_or_q,
  assumption,

  -- Demonstre ¬Q
  intro Hq,
  have p_or_q : P ∨ Q,
  right,
  assumption,
  apply HNp_or_q,
  assumption,

  -- Duas formas diferente de fechar essa demonstração, também poderia ser usado o contradiction
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro Hnp_and_nq,
  intro Hp_or_q,
  cases Hnp_and_nq,
  cases Hp_or_q,
  -- Caso P
  apply Hnp_and_nq_left,
  assumption,
  -- Caso Q
  have Hboom : false := Hnp_and_nq_right Hp_or_q,
  assumption,

  -- Também com duas formas de fechar além do contradiction
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro HNp_and_q,
  by_cases Hp : P,
  -- Caso P
  left, -- Demonstre ¬Q
  intro Hq,
  apply HNp_and_q,
  split,
  -- Demonstre P
  assumption,
  -- Demonstre Q
  assumption,
  
  -- Caso ¬P
  right,
  assumption,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro Hnq_or_np,
  intro Hp_and_q,
  cases Hp_and_q,
  cases Hnq_or_np,
  -- Caso ¬Q
  apply Hnq_or_np,
  assumption,

  -- Caso ¬P
  have hboom : false := Hnq_or_np Hp_and_q_left,
  assumption,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro HNp_and_q,
  by_cases Hp : P,
  -- Caso P
  left, -- Demonstre ¬Q
  intro Hq,
  apply HNp_and_q,
  split,
  -- Demonstre P
  assumption,
  -- Demonstre Q
  assumption,
  
  -- Caso ¬P
  right,
  assumption,

  intro Hnq_or_np,
  intro Hp_and_q,
  cases Hp_and_q,
  cases Hnq_or_np,
  -- Caso ¬Q
  apply Hnq_or_np,
  assumption,

  -- Caso ¬P
  have hboom : false := Hnq_or_np Hp_and_q_left,
  assumption,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,

  intro HNp_or_q,
  split,
  -- Demonstre ¬P
  intro Hp,
  have p_or_q : P ∨ Q,
  left,
  assumption,
  have Np_or_q : false := HNp_or_q p_or_q,
  assumption,

  -- Demonstre ¬Q
  intro Hq,
  have p_or_q : P ∨ Q,
  right,
  assumption,
  apply HNp_or_q,
  assumption,

  intro Hnp_and_nq,
  intro Hp_or_q,
  cases Hnp_and_nq,
  cases Hp_or_q,
  -- Caso P
  apply Hnp_and_nq_left,
  assumption,
  -- Caso Q
  have Hboom : false := Hnp_and_nq_right Hp_or_q,
  assumption,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro Hp_and__q_or_r,
  cases Hp_and__q_or_r,
  cases Hp_and__q_or_r_right,
  -- Caso Q
  left,
  split,
  assumption,
  assumption,
  -- Caso R
  right,
  split,
  assumption,
  assumption,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro Hand_or_and,
  split,
  -- Demonstre P
  cases Hand_or_and,

  -- Caso P ∧ Q
  cases Hand_or_and,
  assumption,

  -- Caso P ∧ R
  cases Hand_or_and,
  assumption,
  
  -- Demonstre Q ∨ R
  cases Hand_or_and,
  -- Caso P ∧ Q
  cases Hand_or_and,
  left,
  assumption,

  -- Caso P ∧ R
  cases Hand_or_and,
  right,
  assumption,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro HP_or_and,
  split,
  -- Demonstre P ∨ Q
  cases HP_or_and,
  -- Caso P
  left,
  assumption,
  -- Caso Q ∧ R
  cases HP_or_and,
  right,
  assumption,

  -- Demonstre P ∨ R
  cases HP_or_and,
  -- Caso P
  left,
  assumption,
  -- Caso Q ∧ R
  cases HP_or_and,
  right,
  assumption,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro Hor_and_or,
  cases Hor_and_or,
  cases Hor_and_or_left,
  -- Caso P
  left,
  assumption,
  -- Caso Q
  cases Hor_and_or_right,
    -- Caso P
    left,
    assumption,
  right,
  split,
  -- Demonstre Q
  assumption,
  -- Demonstre R
  assumption,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro Hp_and_q_imp_r,
  intro Hp,
  intro Hq,
  apply Hp_and_q_imp_r,
  split,
  -- Demonstre P
  assumption,
  -- Demonstre Q
  assumption,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro Hp_imp_q_imp_r,
  intro Hp_and_q,
  cases Hp_and_q,
  apply Hp_imp_q_imp_r,
  assumption,
  assumption,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro Hp,
  assumption,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro Hp,
  left,
  assumption,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro Hq,
  right,
  assumption,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro Hp_and_q,
  cases Hp_and_q, 
  assumption,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro Hp_and_q,
  cases Hp_and_q, 
  assumption,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro p_and_p,
  cases p_and_p,
  assumption,

  intro Hp,
  split,
  assumption,
  assumption,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro Hp_or_p,
  cases Hp_or_p,
  assumption,
  assumption,

  intro Hp,
  right,
  assumption,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro Hn_exist_P,
  intro x,
  intro Hnp,
  apply Hn_exist_P,
  existsi x,
  assumption,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro H_all_np,
  intro H_exist_P,
  cases H_exist_P with u hu,
  apply H_all_np u,
  assumption,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro Hn_all_p,
  by_contradiction H_exist_nP,
  exfalso,
  apply Hn_all_p,
  intro u,
  by_contradiction HnP,
  apply H_exist_nP,
  existsi u,
  assumption,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro H_exist_nP,
  cases H_exist_nP with u HnP,
  intro H_all_P,
  have Hu := H_all_P u,
  apply HnP,
  assumption,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  intro Hn_all_p,
  by_contradiction H_exist_nP,
  exfalso,
  apply Hn_all_p,
  intro u,
  by_contradiction HnP,
  apply H_exist_nP,
  existsi u,
  assumption,

  intro H_exist_nP,
  cases H_exist_nP with u HnP,
  intro H_all_P,
  have Hu := H_all_P u,
  apply HnP,
  assumption,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  intro Hn_exist_P,
  intro x,
  intro Hnp,
  apply Hn_exist_P,
  existsi x,
  assumption,

  intro H_all_np,
  intro H_exist_P,
  cases H_exist_P with u hu,
  apply H_all_np u,
  assumption,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro H_exist_P,
  cases H_exist_P with u HP,
  intro H_all_nP,
  have Hu := H_all_nP u,
  apply Hu,
  assumption,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro H_all_P,
  intro H_exist_nP,
  cases H_exist_nP with u HP,
  have Hu := H_all_P u,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro Hn_exist_nP,
  intro u,
  by_contradiction Hboom,
  apply Hn_exist_nP,
  existsi u,
  assumption,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro Hn_forall_nP,
  by_contradiction Hboom,
  apply Hn_forall_nP,
  intro u,
  intro Hu,
  apply Hboom,
  existsi u,
  assumption,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  intro H_all_P,
  intro H_exist_nP,
  cases H_exist_nP with u HP,
  have Hu := H_all_P u,
  contradiction,

   intro Hn_exist_nP,
  intro u,
  by_contradiction Hboom,
  apply Hn_exist_nP,
  existsi u,
  assumption,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  intro H_exist_P,
  cases H_exist_P with u HP,
  intro H_all_nP,
  have Hu := H_all_nP u,
  apply Hu,
  assumption,

  intro Hn_forall_nP,
  by_contradiction Hboom,
  apply Hn_forall_nP,
  intro u,
  intro Hu,
  apply Hboom,
  existsi u,
  assumption,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro H_exist_p_and_q,
  
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
