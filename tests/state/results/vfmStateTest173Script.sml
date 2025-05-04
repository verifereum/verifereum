open HolKernel vfmTestLib vfmStateTestDefs173Theory; 
val () = new_theory "vfmStateTest173";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs173";
val () = export_theory_no_docs ();
