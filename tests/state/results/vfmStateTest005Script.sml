open HolKernel vfmTestLib vfmStateTestDefs005Theory; 
val () = new_theory "vfmStateTest005";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs005";
val () = export_theory_no_docs ();
