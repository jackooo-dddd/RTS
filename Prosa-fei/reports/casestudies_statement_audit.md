# CaseStudies statement audit (A+B)

- total cases: 37
- clean: 34
- flagged: 3

## Flagged files

### 2009-RTSS-Lemma1
- Coq: `dataset_casestudy\2009-RTSS-Lemma1\Lemma1.v`  Lean: `CaseStudies/2009-RTSS-Lemma1.lean`
- Coq decls: 17 (defs=16, thms=1, hyps=66) | Lean decls: 1 (defs=0, thms=1, variable-lines=11)
- ∀/forall: coq=11 lean=3 | →/->: coq=31 lean=3
- Coq theorems: ['Lemma1_09']
- Lean theorems: ['Lemma1_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn', 'hp_busy', 'is_carry_in_job', 'task_has_carry_in_job']
- **FLAGS**: ['B:binder_shortfall coq(∀+→)=42 lean(∀+→+vars)=17']
- info: ['no_sorry (already-proved)']

### 2009-RTSS-Theorem2
- Coq: `dataset_casestudy\2009-RTSS-Theorem2\Theorem2.v`  Lean: `CaseStudies/2009-RTSS-Theorem2.lean`
- Coq decls: 23 (defs=22, thms=1, hyps=76) | Lean decls: 1 (defs=0, thms=1, variable-lines=17)
- ∀/forall: coq=12 lean=0 | →/->: coq=32 lean=5
- Coq theorems: ['Theorem2']
- Lean theorems: ['Theorem2']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_arbitrary_ci', 'interference_bound_arbitrary_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn_arbitrary', 'f_chi', 'chi_is_least_solution', 'hp_busy', 'H_phi_satisfy', 'R_phi_term', 'max_R_phi_term', 'H_satisfy', 'R_term', 'max_R_term']
- **FLAGS**: ['B:binder_shortfall coq(∀+→)=44 lean(∀+→+vars)=22']
- info: ["opaque-variables=['H_satisfy', 'R_term', 'max_R_term']", 'no_sorry (already-proved)']

### 2014-RTCSA-Theorem3
- Coq: `dataset_casestudy\2014-RTCSA-Theorem3\theorem3.v`  Lean: `CaseStudies/2014-RTCSA-Theorem3.lean`
- Coq decls: 12 (defs=11, thms=1, hyps=75) | Lean decls: 1 (defs=0, thms=1, variable-lines=14)
- ∀/forall: coq=18 lean=2 | →/->: coq=37 lean=4
- Coq theorems: ['Theorem3_14']
- Lean theorems: ['Theorem3_14']
- Coq defs: ['x_p', 'x_delta', 'W_NC', 'W_CI', 'interference_bound_arbitrary_ci', 'interference_bound_arbitrary_nc', 'total_interference_bound_CI', 'total_interference_bound_NC', 'total_interference_bound_rtcsa14', 'hp_busy', 'valid_CI_taskset']
- **FLAGS**: ['B:binder_shortfall coq(∀+→)=55 lean(∀+→+vars)=20']
- info: ["opaque-variables=['x_p', 'x_delta', 'W_CI', 'total_interference_bound_CI', 'total_interference_bound_NC', 'total_interference_bound_rtcsa14', 'valid_CI_taskset']", 'no_sorry (already-proved)']

## Clean files

- 2003-RTS-Lemma2
- 2003-RTS-Theorem4
- 2003-RTS-Theorem5
- 2003-RTS-Theorem6
- 2005-ECRTS-Lemma4
- 2007-RTSS-Theorem1
- 2007-RTSS-Theorem2
- 2007-RTSS-Theorem3
- 2007-RTSS-Theorem4
- 2009-RTSS-Extend1_1
- 2009-RTSS-Extend1_10
- 2009-RTSS-Extend1_2
- 2009-RTSS-Extend1_3
- 2009-RTSS-Extend1_4
- 2009-RTSS-Extend1_5
- 2009-RTSS-Extend1_6
- 2009-RTSS-Extend1_7
- 2009-RTSS-Extend1_8
- 2009-RTSS-Extend1_9
- 2009-RTSS-Lemma2-1
- 2009-RTSS-Lemma2-2
- 2009-RTSS-Lemma3
- 2009-RTSS-Lemma4
- 2009-RTSS-Lemma5
- 2009-RTSS-Theorem1
- 2009-TPDS-Theorem3
- 2010-RTS-Theorem1
- 2010-RTS-Theorem2
- 2014-RTCSA-Lemma4
- 2014-RTCSA-Lemma5
- 2015-BOOK-Lemma18.1
- 2015-BOOK-Theorem18.6
- 2015-RTAS-Lemma8
- 2015-RTCSA-Theorem1

## Full detail

### 2003-RTS-Lemma2
- Coq: `dataset_casestudy\2003-RTS-Lemma2\RTS_Lemma2.v`  Lean: `CaseStudies/2003-RTS-Lemma2.lean`
- Coq decls: 7 (defs=6, thms=1, hyps=37) | Lean decls: 1 (defs=0, thms=1, variable-lines=22)
- ∀/forall: coq=7 lean=5 | →/->: coq=24 lean=10
- Coq theorems: ['Lemma2_03']
- Lean theorems: ['Lemma2_03']
- Coq defs: ['utilization', 'total_utilization', 'max_utilization', 'consecutive_jobs_of_same_task', 'periodic_task_model', 'taskset_schedulable']
- flags: (clean)

### 2003-RTS-Theorem4
- Coq: `dataset_casestudy\2003-RTS-Theorem4\theorem4.v`  Lean: `CaseStudies/2003-RTS-Theorem4.lean`
- Coq decls: 7 (defs=6, thms=1, hyps=37) | Lean decls: 1 (defs=0, thms=1, variable-lines=22)
- ∀/forall: coq=6 lean=3 | →/->: coq=22 lean=7
- Coq theorems: ['Theorem4_03']
- Lean theorems: ['Theorem4_03']
- Coq defs: ['utilization', 'total_utilization', 'max_utilization', 'consecutive_jobs_of_same_task', 'periodic_task_model', 'taskset_schedulable']
- flags: (clean)

### 2003-RTS-Theorem5
- Coq: `dataset_casestudy\2003-RTS-Theorem5\theorem5.v`  Lean: `CaseStudies/2003-RTS-Theorem5.lean`
- Coq decls: 7 (defs=6, thms=1, hyps=38) | Lean decls: 1 (defs=0, thms=1, variable-lines=23)
- ∀/forall: coq=6 lean=3 | →/->: coq=23 lean=8
- Coq theorems: ['Theorem5_03']
- Lean theorems: ['Theorem5_03']
- Coq defs: ['utilization', 'total_utilization', 'max_utilization', 'consecutive_jobs_of_same_task', 'periodic_task_model', 'taskset_schedulable']
- flags: (clean)
- info: ['no_sorry (already-proved)']

### 2003-RTS-Theorem6
- Coq: `dataset_casestudy\2003-RTS-Theorem6\theorem6.v`  Lean: `CaseStudies/2003-RTS-Theorem6.lean`
- Coq decls: 7 (defs=6, thms=1, hyps=41) | Lean decls: 1 (defs=0, thms=1, variable-lines=22)
- ∀/forall: coq=6 lean=3 | →/->: coq=24 lean=7
- Coq theorems: ['Theorem6_03']
- Lean theorems: ['Theorem6_03']
- Coq defs: ['utilization', 'total_utilization', 'max_utilization', 'consecutive_jobs_of_same_task', 'periodic_task_model', 'taskset_schedulable']
- flags: (clean)

### 2005-ECRTS-Lemma4
- Coq: `dataset_casestudy\2005-ECRTS-Lemma4\Lemma4.v`  Lean: `CaseStudies/2005-ECRTS-Lemma4.lean`
- Coq decls: 1 (defs=0, thms=1, hyps=20) | Lean decls: 1 (defs=0, thms=1, variable-lines=16)
- ∀/forall: coq=2 lean=2 | →/->: coq=9 lean=4
- Coq theorems: ['Lemma4_05']
- Lean theorems: ['Lemma4_05']
- flags: (clean)

### 2007-RTSS-Theorem1
- Coq: `dataset_casestudy\2007-RTSS-Theorem1\Theorem1.v`  Lean: `CaseStudies/2007-RTSS-Theorem1.lean`
- Coq decls: 3 (defs=2, thms=1, hyps=53) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=7 lean=7 | →/->: coq=21 lean=12
- Coq theorems: ['Theorem1_07']
- Lean theorems: ['Theorem1_07']
- Coq defs: ['interference_bound_generic', 'total_interference_bound_fp']
- flags: (clean)

### 2007-RTSS-Theorem2
- Coq: `dataset_casestudy\2007-RTSS-Theorem2\Theorem2.v`  Lean: `CaseStudies/2007-RTSS-Theorem2.lean`
- Coq decls: 1 (defs=0, thms=1, hyps=14) | Lean decls: 1 (defs=0, thms=1, variable-lines=10)
- ∀/forall: coq=1 lean=1 | →/->: coq=7 lean=3
- Coq theorems: ['theorem_2']
- Lean theorems: ['theorem_2']
- flags: (clean)
- info: ['no_sorry (already-proved)']

### 2007-RTSS-Theorem3
- Coq: `dataset_casestudy\2007-RTSS-Theorem3\Theorem3.v`  Lean: `CaseStudies/2007-RTSS-Theorem3.lean`
- Coq decls: 1 (defs=0, thms=1, hyps=26) | Lean decls: 1 (defs=0, thms=1, variable-lines=22)
- ∀/forall: coq=3 lean=3 | →/->: coq=11 lean=6
- Coq theorems: ['Theorem3_07']
- Lean theorems: ['Theorem3_07']
- flags: (clean)

### 2007-RTSS-Theorem4
- Coq: `dataset_casestudy\2007-RTSS-Theorem4\Theorem4.v`  Lean: `CaseStudies/2007-RTSS-Theorem4.lean`
- Coq decls: 3 (defs=2, thms=1, hyps=29) | Lean decls: 1 (defs=0, thms=1, variable-lines=18)
- ∀/forall: coq=1 lean=1 | →/->: coq=11 lean=4
- Coq theorems: ['Theorem4_07']
- Lean theorems: ['Theorem4_07']
- Coq defs: ['max_jobs', 'W']
- flags: (clean)

### 2009-RTSS-Extend1_1
- Coq: `dataset_casestudy\2009-RTSS-Extend1_1\Method1_1.v`  Lean: `CaseStudies/2009-RTSS-Extend1_1.lean`
- Coq decls: 14 (defs=13, thms=1, hyps=69) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=8 lean=7 | →/->: coq=27 lean=12
- Coq theorems: ['mehthod1_1_09']
- Lean theorems: ['Method1_1_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn']
- flags: (clean)
- info: ["accepted-alias={'mehthod1_1_09': 'Method1_1_09'}"]

### 2009-RTSS-Extend1_10
- Coq: `dataset_casestudy\2009-RTSS-Extend1_10\Method1_10.v`  Lean: `CaseStudies/2009-RTSS-Extend1_10.lean`
- Coq decls: 14 (defs=13, thms=1, hyps=69) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=8 lean=7 | →/->: coq=27 lean=12
- Coq theorems: ['Method1_10_09']
- Lean theorems: ['Method1_10_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn']
- flags: (clean)

### 2009-RTSS-Extend1_2
- Coq: `dataset_casestudy\2009-RTSS-Extend1_2\Method1_2.v`  Lean: `CaseStudies/2009-RTSS-Extend1_2.lean`
- Coq decls: 15 (defs=14, thms=1, hyps=77) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=14 lean=7 | →/->: coq=39 lean=12
- Coq theorems: ['Method1_2_09']
- Lean theorems: ['Method1_2_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn', 'hp_busy']
- flags: (clean)

### 2009-RTSS-Extend1_3
- Coq: `dataset_casestudy\2009-RTSS-Extend1_3\Method1_3.v`  Lean: `CaseStudies/2009-RTSS-Extend1_3.lean`
- Coq decls: 14 (defs=13, thms=1, hyps=69) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=8 lean=7 | →/->: coq=26 lean=12
- Coq theorems: ['Mehod1_3_09']
- Lean theorems: ['Method1_3_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn']
- flags: (clean)
- info: ["accepted-alias={'Mehod1_3_09': 'Method1_3_09'}"]

### 2009-RTSS-Extend1_4
- Coq: `dataset_casestudy\2009-RTSS-Extend1_4\Method1_4.v`  Lean: `CaseStudies/2009-RTSS-Extend1_4.lean`
- Coq decls: 14 (defs=13, thms=1, hyps=69) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=9 lean=7 | →/->: coq=30 lean=12
- Coq theorems: ['Method1_4_09']
- Lean theorems: ['Method1_4_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn']
- flags: (clean)

### 2009-RTSS-Extend1_5
- Coq: `dataset_casestudy\2009-RTSS-Extend1_5\Method1_5.v`  Lean: `CaseStudies/2009-RTSS-Extend1_5.lean`
- Coq decls: 14 (defs=13, thms=1, hyps=69) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=9 lean=7 | →/->: coq=28 lean=12
- Coq theorems: ['Method1_5_09']
- Lean theorems: ['Method1_5_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn']
- flags: (clean)

### 2009-RTSS-Extend1_6
- Coq: `dataset_casestudy\2009-RTSS-Extend1_6\Method1_6.v`  Lean: `CaseStudies/2009-RTSS-Extend1_6.lean`
- Coq decls: 14 (defs=13, thms=1, hyps=69) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=8 lean=7 | →/->: coq=26 lean=12
- Coq theorems: ['Method1_6_09']
- Lean theorems: ['Method1_6_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn']
- flags: (clean)

### 2009-RTSS-Extend1_7
- Coq: `dataset_casestudy\2009-RTSS-Extend1_7\Method1_7.v`  Lean: `CaseStudies/2009-RTSS-Extend1_7.lean`
- Coq decls: 14 (defs=13, thms=1, hyps=69) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=9 lean=7 | →/->: coq=27 lean=12
- Coq theorems: ['Method1_7_09']
- Lean theorems: ['Method1_7_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn']
- flags: (clean)

### 2009-RTSS-Extend1_8
- Coq: `dataset_casestudy\2009-RTSS-Extend1_8\Mehod1_8.v`  Lean: `CaseStudies/2009-RTSS-Extend1_8.lean`
- Coq decls: 14 (defs=13, thms=1, hyps=69) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=9 lean=7 | →/->: coq=27 lean=12
- Coq theorems: ['Method1_8_09']
- Lean theorems: ['Method1_8_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn']
- flags: (clean)

### 2009-RTSS-Extend1_9
- Coq: `dataset_casestudy\2009-RTSS-Extend1_9\Method1_9.v`  Lean: `CaseStudies/2009-RTSS-Extend1_9.lean`
- Coq decls: 14 (defs=13, thms=1, hyps=69) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=8 lean=7 | →/->: coq=26 lean=12
- Coq theorems: ['Method1_9_09']
- Lean theorems: ['Method1_9_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn']
- flags: (clean)

### 2009-RTSS-Lemma1
- Coq: `dataset_casestudy\2009-RTSS-Lemma1\Lemma1.v`  Lean: `CaseStudies/2009-RTSS-Lemma1.lean`
- Coq decls: 17 (defs=16, thms=1, hyps=66) | Lean decls: 1 (defs=0, thms=1, variable-lines=11)
- ∀/forall: coq=11 lean=3 | →/->: coq=31 lean=3
- Coq theorems: ['Lemma1_09']
- Lean theorems: ['Lemma1_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn', 'hp_busy', 'is_carry_in_job', 'task_has_carry_in_job']
- **FLAGS**: ['B:binder_shortfall coq(∀+→)=42 lean(∀+→+vars)=17']
- info: ['no_sorry (already-proved)']

### 2009-RTSS-Lemma2-1
- Coq: `dataset_casestudy\2009-RTSS-Lemma2-1\Lemma2_1.v`  Lean: `CaseStudies/2009-RTSS-Lemma2-1.lean`
- Coq decls: 15 (defs=14, thms=1, hyps=64) | Lean decls: 1 (defs=0, thms=1, variable-lines=36)
- ∀/forall: coq=10 lean=10 | →/->: coq=31 lean=18
- Coq theorems: ['Lemma2_09']
- Lean theorems: ['Lemma2_1_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn', 'hp_busy']
- flags: (clean)
- info: ["accepted-alias={'Lemma2_09': 'Lemma2_1_09'}"]

### 2009-RTSS-Lemma2-2
- Coq: `dataset_casestudy\2009-RTSS-Lemma2-2\Lemma2_2.v`  Lean: `CaseStudies/2009-RTSS-Lemma2-2.lean`
- Coq decls: 17 (defs=16, thms=1, hyps=65) | Lean decls: 1 (defs=0, thms=1, variable-lines=37)
- ∀/forall: coq=10 lean=10 | →/->: coq=32 lean=18
- Coq theorems: ['Lemma2_09']
- Lean theorems: ['Lemma2_2_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn', 'hp_busy', 'is_carry_in_job', 'task_has_carry_in_job']
- flags: (clean)
- info: ["accepted-alias={'Lemma2_09': 'Lemma2_2_09'}"]

### 2009-RTSS-Lemma3
- Coq: `dataset_casestudy\2009-RTSS-Lemma3\lemma3.v`  Lean: `CaseStudies/2009-RTSS-Lemma3.lean`
- Coq decls: 15 (defs=14, thms=1, hyps=85) | Lean decls: 1 (defs=0, thms=1, variable-lines=51)
- ∀/forall: coq=22 lean=18 | →/->: coq=44 lean=26
- Coq theorems: ['Lemma3_09']
- Lean theorems: ['Lemma3_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn', 'hp_busy']
- flags: (clean)

### 2009-RTSS-Lemma4
- Coq: `dataset_casestudy\2009-RTSS-Lemma4\Lemma4.v`  Lean: `CaseStudies/2009-RTSS-Lemma4.lean`
- Coq decls: 15 (defs=14, thms=1, hyps=78) | Lean decls: 1 (defs=0, thms=1, variable-lines=45)
- ∀/forall: coq=12 lean=8 | →/->: coq=35 lean=17
- Coq theorems: ['Lemma4_09']
- Lean theorems: ['Lemma4_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn', 'hp_busy']
- flags: (clean)

### 2009-RTSS-Lemma5
- Coq: `dataset_casestudy\2009-RTSS-Lemma5\Lemma5.v`  Lean: `CaseStudies/2009-RTSS-Lemma5.lean`
- Coq decls: 20 (defs=19, thms=1, hyps=73) | Lean decls: 1 (defs=0, thms=1, variable-lines=43)
- ∀/forall: coq=11 lean=10 | →/->: coq=31 lean=20
- Coq theorems: ['Lemma5_09']
- Lean theorems: ['Lemma5_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_arbitrary_ci', 'interference_bound_arbitrary_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn_arbitrary', 'f_chi', 'chi_is_least_solution', 'hp_busy', 'H_phi_satisfy', 'R_phi_term', 'max_R_phi_term']
- flags: (clean)

### 2009-RTSS-Theorem1
- Coq: `dataset_casestudy\2009-RTSS-Theorem1\Theorem1.v`  Lean: `CaseStudies/2009-RTSS-Theorem1.lean`
- Coq decls: 15 (defs=14, thms=1, hyps=78) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=11 lean=7 | →/->: coq=32 lean=11
- Coq theorems: ['Theorem1_09']
- Lean theorems: ['Theorem1_09']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn', 'hp_busy']
- flags: (clean)

### 2009-RTSS-Theorem2
- Coq: `dataset_casestudy\2009-RTSS-Theorem2\Theorem2.v`  Lean: `CaseStudies/2009-RTSS-Theorem2.lean`
- Coq decls: 23 (defs=22, thms=1, hyps=76) | Lean decls: 1 (defs=0, thms=1, variable-lines=17)
- ∀/forall: coq=12 lean=0 | →/->: coq=32 lean=5
- Coq theorems: ['Theorem2']
- Lean theorems: ['Theorem2']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_arbitrary_ci', 'interference_bound_arbitrary_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn_arbitrary', 'f_chi', 'chi_is_least_solution', 'hp_busy', 'H_phi_satisfy', 'R_phi_term', 'max_R_phi_term', 'H_satisfy', 'R_term', 'max_R_term']
- **FLAGS**: ['B:binder_shortfall coq(∀+→)=44 lean(∀+→+vars)=22']
- info: ["opaque-variables=['H_satisfy', 'R_term', 'max_R_term']", 'no_sorry (already-proved)']

### 2009-TPDS-Theorem3
- Coq: `dataset_casestudy\2009-TPDS-Theorem3\theorem3.v`  Lean: `CaseStudies/2009-TPDS-Theorem3.lean`
- Coq decls: 8 (defs=7, thms=1, hyps=32) | Lean decls: 1 (defs=0, thms=1, variable-lines=22)
- ∀/forall: coq=4 lean=3 | →/->: coq=15 lean=7
- Coq theorems: ['Theorem3_10']
- Lean theorems: ['Theorem3_10']
- Coq defs: ['utilization', 'total_utilization', 'max_utilization', 'density', 'total_density', 'max_density', 'taskset_schedulable']
- flags: (clean)

### 2010-RTS-Theorem1
- Coq: `dataset_casestudy\2010-RTS-Theorem1\theorem1.v`  Lean: `CaseStudies/2010-RTS-Theorem1.lean`
- Coq decls: 2 (defs=1, thms=1, hyps=49) | Lean decls: 1 (defs=0, thms=1, variable-lines=45)
- ∀/forall: coq=9 lean=9 | →/->: coq=19 lean=15
- Coq theorems: ['Theorem1_10']
- Lean theorems: ['Theorem1_10']
- Coq defs: ['hp_busy']
- flags: (clean)

### 2010-RTS-Theorem2
- Coq: `dataset_casestudy\2010-RTS-Theorem2\theorem2.v`  Lean: `CaseStudies/2010-RTS-Theorem2.lean`
- Coq decls: 14 (defs=13, thms=1, hyps=64) | Lean decls: 1 (defs=0, thms=1, variable-lines=34)
- ∀/forall: coq=9 lean=9 | →/->: coq=27 lean=13
- Coq theorems: ['Theorem2_10']
- Lean theorems: ['Theorem2_10']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn']
- flags: (clean)

### 2014-RTCSA-Lemma4
- Coq: `dataset_casestudy\2014-RTCSA-Lemma4\lemma4.v`  Lean: `CaseStudies/2014-RTCSA-Lemma4.lean`
- Coq decls: 18 (defs=17, thms=1, hyps=76) | Lean decls: 1 (defs=0, thms=1, variable-lines=45)
- ∀/forall: coq=21 lean=19 | →/->: coq=41 lean=27
- Coq theorems: ['Lemma4_14']
- Lean theorems: ['Lemma4_14']
- Coq defs: ['x_p', 'x_delta', 'W_NC', 'W_CI', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn', 'hp_busy', 'is_carry_in_job', 'task_has_carry_in_job']
- flags: (clean)
- info: ["opaque-variables=['x_p', 'x_delta', 'W_CI']"]

### 2014-RTCSA-Lemma5
- Coq: `dataset_casestudy\2014-RTCSA-Lemma5\lemma5.v`  Lean: `CaseStudies/2014-RTCSA-Lemma5.lean`
- Coq decls: 11 (defs=10, thms=1, hyps=83) | Lean decls: 1 (defs=0, thms=1, variable-lines=55)
- ∀/forall: coq=17 lean=19 | →/->: coq=38 lean=32
- Coq theorems: ['Lemma5_14']
- Lean theorems: ['Lemma5_14']
- Coq defs: ['x_p', 'x_delta', 'W_NC', 'W_CI', 'interference_bound_arbitrary_ci', 'interference_bound_arbitrary_nc', 'total_interference_bound_CI', 'total_interference_bound_NC', 'total_interference_bound_rtcsa14', 'hp_busy']
- flags: (clean)
- info: ["opaque-variables=['x_p', 'x_delta', 'W_CI', 'total_interference_bound_CI', 'total_interference_bound_NC', 'total_interference_bound_rtcsa14']"]

### 2014-RTCSA-Theorem3
- Coq: `dataset_casestudy\2014-RTCSA-Theorem3\theorem3.v`  Lean: `CaseStudies/2014-RTCSA-Theorem3.lean`
- Coq decls: 12 (defs=11, thms=1, hyps=75) | Lean decls: 1 (defs=0, thms=1, variable-lines=14)
- ∀/forall: coq=18 lean=2 | →/->: coq=37 lean=4
- Coq theorems: ['Theorem3_14']
- Lean theorems: ['Theorem3_14']
- Coq defs: ['x_p', 'x_delta', 'W_NC', 'W_CI', 'interference_bound_arbitrary_ci', 'interference_bound_arbitrary_nc', 'total_interference_bound_CI', 'total_interference_bound_NC', 'total_interference_bound_rtcsa14', 'hp_busy', 'valid_CI_taskset']
- **FLAGS**: ['B:binder_shortfall coq(∀+→)=55 lean(∀+→+vars)=20']
- info: ["opaque-variables=['x_p', 'x_delta', 'W_CI', 'total_interference_bound_CI', 'total_interference_bound_NC', 'total_interference_bound_rtcsa14', 'valid_CI_taskset']", 'no_sorry (already-proved)']

### 2015-BOOK-Lemma18.1
- Coq: `dataset_casestudy\2015-BOOK-Lemma18.1\Lemma18_1.v`  Lean: `CaseStudies/2015-BOOK-Lemma18.1.lean`
- Coq decls: 14 (defs=13, thms=1, hyps=64) | Lean decls: 1 (defs=0, thms=1, variable-lines=15)
- ∀/forall: coq=9 lean=6 | →/->: coq=26 lean=7
- Coq theorems: ['Lemma18_1_15']
- Lean theorems: ['Lemma18_1_15']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn']
- flags: (clean)

### 2015-BOOK-Theorem18.6
- Coq: `dataset_casestudy\2015-BOOK-Theorem18.6\Theorem18_6.v`  Lean: `CaseStudies/2015-BOOK-Theorem18.6.lean`
- Coq decls: 14 (defs=13, thms=1, hyps=63) | Lean decls: 1 (defs=0, thms=1, variable-lines=33)
- ∀/forall: coq=7 lean=7 | →/->: coq=25 lean=13
- Coq theorems: ['Theorem18_6_15']
- Lean theorems: ['Theorem18_6_15']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_gn']
- flags: (clean)

### 2015-RTAS-Lemma8
- Coq: `dataset_casestudy\2015-RTAS-Lemma8\Lemma8.v`  Lean: `CaseStudies/2015-RTAS-Lemma8.lean`
- Coq decls: 5 (defs=4, thms=1, hyps=68) | Lean decls: 1 (defs=0, thms=1, variable-lines=39)
- ∀/forall: coq=9 lean=10 | →/->: coq=26 lean=18
- Coq theorems: ['bertogna_cirinei_response_time_bound_fp']
- Lean theorems: ['bertogna_cirinei_response_time_bound_fp']
- Coq defs: ['max_jobs', 'W', 'interference_bound_generic', 'total_interference_bound_fp']
- flags: (clean)

### 2015-RTCSA-Theorem1
- Coq: `dataset_casestudy\2015-RTCSA-Theorem1\theorem1.v`  Lean: `CaseStudies/2015-RTCSA-Theorem1.lean`
- Coq decls: 17 (defs=16, thms=1, hyps=66) | Lean decls: 1 (defs=0, thms=1, variable-lines=39)
- ∀/forall: coq=14 lean=13 | →/->: coq=37 lean=28
- Coq theorems: ['Theorem1_15']
- Lean theorems: ['Theorem1_15']
- Coq defs: ['max_jobs', 'W', 'W_NC', 'interference_bound_generic', 'interference_bound_nc', 'interference_bound_delta', 'sum_largest', 'total_interference_bound_fp', 'CI_taskset', 'NC_taskset', 'total_interference_bound_ci', 'total_interference_bound_nc', 'total_interference_bound_rtcsa15', 'response_time_recurrence', 'is_response_time_solution', 'is_min_response_time']
- flags: (clean)
- info: ["opaque-variables=['total_interference_bound_rtcsa15', 'response_time_recurrence', 'is_response_time_solution', 'is_min_response_time']"]
