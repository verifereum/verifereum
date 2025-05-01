open HolKernel boolLib bossLib cv_transLib vfmTestLib
     vfmStateTestDefs10Theory

val () = new_theory "vfmStateTests10";

val () = List.app (ignore o save_result_thm default_limit) $
           get_result_defs "vfmStateTestDefs10";

val () = export_theory_no_docs ();
