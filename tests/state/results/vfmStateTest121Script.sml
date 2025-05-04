open HolKernel vfmTestLib vfmStateTestDefs121Theory; 
val () = new_theory "vfmStateTest121";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs121";
val () = export_theory_no_docs ();
