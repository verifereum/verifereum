open HolKernel vfmTestLib vfmStateTestDefs175Theory; 
val () = new_theory "vfmStateTest175";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs175";
val () = export_theory_no_docs ();
