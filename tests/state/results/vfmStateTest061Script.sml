open HolKernel vfmTestLib vfmStateTestDefs061Theory; 
val () = new_theory "vfmStateTest061";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs061";
val () = export_theory_no_docs ();
