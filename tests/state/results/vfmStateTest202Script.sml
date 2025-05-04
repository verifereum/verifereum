open HolKernel vfmTestLib vfmStateTestDefs202Theory; 
val () = new_theory "vfmStateTest202";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs202";
val () = export_theory_no_docs ();
