open HolKernel vfmTestLib vfmStateTestDefs017Theory; 
val () = new_theory "vfmStateTest017";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs017";
val () = export_theory_no_docs ();
