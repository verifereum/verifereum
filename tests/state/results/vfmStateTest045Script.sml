open HolKernel vfmTestLib vfmStateTestDefs045Theory; 
val () = new_theory "vfmStateTest045";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs045";
val () = export_theory_no_docs ();
