theory Propagation_Properties

imports
  Timely_Progress
begin 


lemma take_step_PR_p_preserves_inv_imps_work_sum:
  "dataflow_topology summary (-+-) \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   \<exists>(t :: 't::  {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) loc. t \<in>#\<^sub>z c_work c loc \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary PR) c)"
  apply (frule Executable.enum_dataflow_topology.PR_next[where less_t=cless, simplified, unfolded enum_dataflow_topology_def])
     apply assumption
  subgoal
    using linorder_order_ccompare by fast
   apply (clarsimp simp add:)
   apply (erule extension)
  apply (clarsimp split: prod.splits)
  subgoal for t loc loc' t'
    apply (rule Propagate.dataflow_topology.p_preserves_inv_imps_work_sum[where loc=loc and t=t'])
      apply assumption+
    defer
     apply simp
    apply (subst (asm) take_step_enum_dataflow_topology_take_step[symmetric])
     apply (simp add: enum_dataflow_topology_def)
    apply auto
    done
  done

lemma take_step_PR_p_preserves_inv_implications_nonneg:
  "dataflow_topology su (-+-) \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   \<exists>(t :: 't::  {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) loc. t \<in>#\<^sub>z c_work c loc \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg (take_step su PR c)"
  apply (frule Executable.enum_dataflow_topology.PR_next[where less_t=cless, simplified, unfolded enum_dataflow_topology_def])
     apply assumption
  subgoal
    using linorder_order_ccompare by auto
   apply clarsimp
  apply (erule extension)
  apply (elim exE)
    apply (subst take_step_enum_dataflow_topology_take_step)
     apply (simp add: enum_dataflow_topology_def)
   apply (rule Propagate.dataflow_topology.p_preserves_inv_implications_nonneg[of _ _ c])
         apply assumption+
  done

lemma take_step_PR_p_preserves_inv:
  "dataflow_topology summary (-+-) \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   \<exists>(t :: 't::  {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) loc. t \<in>#\<^sub>z c_work c loc \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg ((take_step summary PR) c) \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg ((take_step summary PR) c) \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary PR) c)"
  apply (frule Executable.enum_dataflow_topology.PR_next[where less_t=cless, simplified, unfolded enum_dataflow_topology_def])
  apply assumption
   subgoal
     using linorder_order_ccompare by auto
  apply (erule extension)
   apply clarsimp
  subgoal for t loc loc' t'
    apply (intro conjI)
    subgoal
      apply (rule Propagate.dataflow_topology.p_preserves_inv_implications_nonneg)
         apply assumption+
        apply (clarsimp split: prod.splits)
        apply (subst (asm) take_step_enum_dataflow_topology_take_step[symmetric])
         apply (simp add: enum_dataflow_topology_def)
        apply auto
      done
    subgoal
   apply (subst (asm) take_step_enum_dataflow_topology_take_step[symmetric])
         apply (simp add: enum_dataflow_topology_def)
        apply (auto split: prod.splits)
      using dataflow_topology.iiws_imp_iipwn dataflow_topology.p_preserves_inv_imps_work_sum apply blast
      done
 subgoal
   apply (subst (asm) take_step_enum_dataflow_topology_take_step[symmetric])
         apply (simp add: enum_dataflow_topology_def)
        apply (auto split: prod.splits)
      using dataflow_topology.iiws_imp_iipwn dataflow_topology.p_preserves_inv_imps_work_sum apply blast
      done
    done
  done

lemma propagate_all_terminates:
  assumes "dataflow_topology su (-+-)"
    and "Propagate.dataflow_topology.inv_imps_work_sum su (-+-) c"
    and "Propagate.dataflow_topology.inv_implications_nonneg (c :: ('loc :: {enum,linorder}, 't :: {order_ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) configuration)"
    and "\<forall> loc. su loc loc = {}\<^sub>A"
    and "dataflow_topology_from_tree.inv_imp_plus_work_nonneg c"
  shows "propagate_all su c \<noteq> None"
  unfolding propagate_all_def
  apply simp
  apply (rule wf_rel_while_option_Some[where
        R = "inv_image {(x, y). x < y} (Termination.dataflow_topology.neg_order su dataflow_topology_from_tree.followed_by)" and
        P = "\<lambda>c. Propagate.dataflow_topology.inv_imps_work_sum su dataflow_topology_from_tree.followed_by c \<and>
             Propagate.dataflow_topology.inv_implications_nonneg c \<and> dataflow_topology_from_tree.inv_imp_plus_work_nonneg c"])
     apply (rule wf_inv_image, rule wellorder_class.wf)
  subgoal for s
    apply (clarsimp simp: inv_image_def split: prod.splits)
    apply (rule dataflow_topology.propagation_termination[OF assms(1)])
      defer 
      apply force
     apply force
    subgoal for t loc
      apply (simp add: dataflow_topology.next_propagate'_def[OF assms(1)])
      apply (rule exI[of _ loc])
      apply (rule exI[of _ t])
      apply (intro conjI impI)
      subgoal
        apply (rule mymin_code_in_worklist)
          apply assumption+
        using assms not_none apply auto
        done
      subgoal
        apply (intro allI impI)
        apply (elim exE)
        subgoal for t' loc
        apply (rule mymin_code_is_minimum)
           apply assumption+
          done
        done
      subgoal
        apply (cases s)
        apply clarsimp
        apply (rule ext)
        apply (auto split: )
         apply (subgoal_tac "su loc loc = {}\<^sub>A")
        apply simp
        using assms apply simp
        apply (simp add: dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.zmset_of_lemma)
        done
      done
    done
  subgoal
    apply safe
    subgoal
      apply (rule take_step_PR_p_preserves_inv_imps_work_sum[OF assms(1)])
        apply assumption+
      using assms(4) apply simp
      apply (metis trimono_spec_defs(3) worklist_is_empty_def zequal_equal zmultiset_nonemptyE)
      done
    subgoal
      apply (rule take_step_PR_p_preserves_inv_implications_nonneg[OF assms(1)])
         apply assumption+
      using assms apply auto
      apply (metis worklist_is_empty_def zequal_equal zmultiset_nonemptyE)
      done
    subgoal
      apply (drule take_step_PR_p_preserves_inv[OF assms(1)])
          apply assumption+
      apply (metis trimono_spec_defs(3) worklist_is_empty_def zequal_equal zmultiset_nonemptyE)
      using assms apply auto
      done
    done
  using assms apply auto
  done


section \<open>Invariant Preservation Under Progress take_step\<close>
lemma take_step_CM_p_preserves_inv_imps_work_sum:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   d \<noteq> 0 \<Longrightarrow>
   \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary (CM loc t d)) c)"
  apply (frule Executable.enum_dataflow_topology.CM_next[where delta=d, simplified, unfolded enum_dataflow_topology_def])
    apply assumption+
  apply (elim exE)
  apply (subst take_step_enum_dataflow_topology_take_step)
   apply (simp add: enum_dataflow_topology_def)
  apply (rule Propagate.dataflow_topology.cm_preserves_inv_imps_work_sum)
    apply assumption+
  done

lemma take_step_CM_p_preserves_inv:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   d \<noteq> 0 \<Longrightarrow>
   \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg ((take_step summary (CM loc t d)) c) \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg ((take_step summary (CM loc t d)) c) \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary (CM loc t d)) c)"
  apply (frule Executable.enum_dataflow_topology.CM_next[where delta=d, simplified, unfolded enum_dataflow_topology_def])
    apply assumption+
  apply (elim exE)
  apply (subst (1 2) take_step_enum_dataflow_topology_take_step)
   apply (simp add: enum_dataflow_topology_def)
  apply (intro conjI)
    apply (rule Propagate.dataflow_topology.cm_preserves_inv_implications_nonneg)
      apply assumption+
   apply (rule Propagate.dataflow_topology.iiws_imp_iipwn)
    apply assumption+
   apply (subst take_step_enum_dataflow_topology_take_step[symmetric])
    apply (simp add: enum_dataflow_topology_def)
   apply (rule take_step_CM_p_preserves_inv_imps_work_sum)
      apply assumption+
   apply auto[1]
  apply (rule take_step_CM_p_preserves_inv_imps_work_sum)
     apply assumption+
  apply auto
  done

lemma change_multiplicities_preserves_inv:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   (\<forall> d \<in> snd ` snd ` set xs. d \<noteq> 0) \<Longrightarrow>
   (\<forall> (l, t, d) \<in> set xs. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c l) \<and> t' \<le> t) \<Longrightarrow>
   change_multiplicities summary xs c = c' \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c' \<and>
   dataflow_topology_from_tree.inv_imp_plus_work_nonneg c' \<and>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c'"
  apply (induct xs arbitrary: c c')
   apply simp
  subgoal premises prems for a xs c c'
    using prems(2-) apply -
    apply (simp split: prod.splits)
    subgoal for l b t' d t
      apply (subst (asm) change_multiplicities_simps(2)[where summary=summary])
      apply (frule take_step_CM_p_preserves_inv[where loc=l and t=t'])
           apply assumption+
       apply force
      apply (elim conjE)
      using prems(1) apply -
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      back
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply blast
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply fastforce
      apply (drule meta_mp)
       apply auto
      done
    done
  done


lemma take_step_PR_preserves_c_pts[simp]:
  "c_pts (take_step summary PR c) = c_pts c"
  by (simp_all split: prod.splits if_splits)


end
