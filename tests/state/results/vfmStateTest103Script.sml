open HolKernel vfmTestLib vfmStateTestDefs103Theory; 
val () = new_theory "vfmStateTest103";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs103";
val () = export_theory_no_docs ();
