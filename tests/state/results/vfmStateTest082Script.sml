open HolKernel vfmTestLib vfmStateTestDefs082Theory; 
val () = new_theory "vfmStateTest082";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs082";
val () = export_theory_no_docs ();
