open HolKernel vfmTestLib vfmStateTestDefs155Theory; 
val () = new_theory "vfmStateTest155";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs155";
val () = export_theory_no_docs ();
