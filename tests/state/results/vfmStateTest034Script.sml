open HolKernel vfmTestLib vfmStateTestDefs034Theory; 
val () = new_theory "vfmStateTest034";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs034";
val () = export_theory_no_docs ();
