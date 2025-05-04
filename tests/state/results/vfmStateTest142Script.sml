open HolKernel vfmTestLib vfmStateTestDefs142Theory; 
val () = new_theory "vfmStateTest142";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs142";
val () = export_theory_no_docs ();
