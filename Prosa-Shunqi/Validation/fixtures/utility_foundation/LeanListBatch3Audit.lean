import Prosa.Util.List

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.subseq_leq_size"
#check @Prosa.Util.List.subseq_leq_size
#eval IO.println "FREEZE_END Prosa.Util.List.subseq_leq_size"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.in_zip"
#check @Prosa.Util.List.in_zip
#eval IO.println "FREEZE_END Prosa.Util.List.in_zip"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.eq_ind_in_seq"
#check @Prosa.Util.List.eq_ind_in_seq
#eval IO.println "FREEZE_END Prosa.Util.List.eq_ind_in_seq"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.default_or_in"
#check @Prosa.Util.List.default_or_in
#eval IO.println "FREEZE_END Prosa.Util.List.default_or_in"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.exists_two"
#check @Prosa.Util.List.exists_two
#eval IO.println "FREEZE_END Prosa.Util.List.exists_two"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.has_all_nilp"
#check @Prosa.Util.List.has_all_nilp
#eval IO.println "FREEZE_END Prosa.Util.List.has_all_nilp"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.sorted_split"
#check @Prosa.Util.List.sorted_split
#eval IO.println "FREEZE_END Prosa.Util.List.sorted_split"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.sorted_cat"
#check @Prosa.Util.List.sorted_cat
#eval IO.println "FREEZE_END Prosa.Util.List.sorted_cat"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.nonnil_last"
#check @Prosa.Util.List.nonnil_last
#eval IO.println "FREEZE_END Prosa.Util.List.nonnil_last"

#print axioms Prosa.Util.List.subseq_leq_size
#print axioms Prosa.Util.List.in_zip
#print axioms Prosa.Util.List.eq_ind_in_seq
#print axioms Prosa.Util.List.default_or_in
#print axioms Prosa.Util.List.exists_two
#print axioms Prosa.Util.List.has_all_nilp
#print axioms Prosa.Util.List.sorted_split
#print axioms Prosa.Util.List.sorted_cat
#print axioms Prosa.Util.List.nonnil_last
