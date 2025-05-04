open HolKernel vfmTestLib vfmStateTestDefs002Theory; 
val () = new_theory "vfmStateTest002";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs002";
val () = export_theory_no_docs ();
