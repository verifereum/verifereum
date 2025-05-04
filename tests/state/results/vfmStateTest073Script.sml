open HolKernel vfmTestLib vfmStateTestDefs073Theory; 
val () = new_theory "vfmStateTest073";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs073";
val () = export_theory_no_docs ();
