open HolKernel vfmTestLib vfmStateTestDefs015Theory; 
val () = new_theory "vfmStateTest015";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs015";
val () = export_theory_no_docs ();
