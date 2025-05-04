open HolKernel vfmTestLib vfmStateTestDefs046Theory; 
val () = new_theory "vfmStateTest046";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs046";
val () = export_theory_no_docs ();
