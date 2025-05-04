open HolKernel vfmTestLib vfmStateTestDefs047Theory; 
val () = new_theory "vfmStateTest047";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs047";
val () = export_theory_no_docs ();
