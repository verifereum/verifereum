open HolKernel vfmTestLib vfmStateTestDefs000Theory; 
val () = new_theory "vfmStateTest000";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs000";
val () = export_theory_no_docs ();
