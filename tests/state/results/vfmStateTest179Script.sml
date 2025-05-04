open HolKernel vfmTestLib vfmStateTestDefs179Theory; 
val () = new_theory "vfmStateTest179";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs179";
val () = export_theory_no_docs ();
