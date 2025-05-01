open HolKernel boolLib bossLib cv_transLib vfmTestLib
     vfmStateTestDefs100Theory

val () = new_theory "vfmStateTests100";

val () = List.app (ignore o save_result_thm default_limit) $
           get_result_defs "vfmStateTestDefs100";

val () = export_theory_no_docs ();
