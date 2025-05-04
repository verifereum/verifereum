open HolKernel vfmTestLib vfmStateTestDefs044Theory; 
val () = new_theory "vfmStateTest044";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs044";
val () = export_theory_no_docs ();
