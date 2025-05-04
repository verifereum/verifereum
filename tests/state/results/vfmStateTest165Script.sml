open HolKernel vfmTestLib vfmStateTestDefs165Theory; 
val () = new_theory "vfmStateTest165";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs165";
val () = export_theory_no_docs ();
