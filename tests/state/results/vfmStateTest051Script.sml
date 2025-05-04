open HolKernel vfmTestLib vfmStateTestDefs051Theory; 
val () = new_theory "vfmStateTest051";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs051";
val () = export_theory_no_docs ();
