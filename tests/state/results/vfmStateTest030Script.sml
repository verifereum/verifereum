open HolKernel vfmTestLib vfmStateTestDefs030Theory; 
val () = new_theory "vfmStateTest030";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs030";
val () = export_theory_no_docs ();
