open HolKernel vfmTestLib vfmStateTestDefs066Theory; 
val () = new_theory "vfmStateTest066";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs066";
val () = export_theory_no_docs ();
