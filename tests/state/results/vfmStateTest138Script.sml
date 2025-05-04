open HolKernel vfmTestLib vfmStateTestDefs138Theory; 
val () = new_theory "vfmStateTest138";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs138";
val () = export_theory_no_docs ();
