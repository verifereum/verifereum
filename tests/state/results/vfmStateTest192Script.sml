open HolKernel vfmTestLib vfmStateTestDefs192Theory; 
val () = new_theory "vfmStateTest192";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs192";
val () = export_theory_no_docs ();
