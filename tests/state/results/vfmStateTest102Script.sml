open HolKernel vfmTestLib vfmStateTestDefs102Theory; 
val () = new_theory "vfmStateTest102";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs102";
val () = export_theory_no_docs ();
