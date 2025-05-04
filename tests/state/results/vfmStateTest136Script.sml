open HolKernel vfmTestLib vfmStateTestDefs136Theory; 
val () = new_theory "vfmStateTest136";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs136";
val () = export_theory_no_docs ();
