open HolKernel vfmTestLib vfmStateTestDefs116Theory; 
val () = new_theory "vfmStateTest116";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs116";
val () = export_theory_no_docs ();
