open HolKernel vfmTestLib vfmStateTestDefs083Theory; 
val () = new_theory "vfmStateTest083";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs083";
val () = export_theory_no_docs ();
