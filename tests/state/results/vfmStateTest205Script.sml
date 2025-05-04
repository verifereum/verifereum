open HolKernel vfmTestLib vfmStateTestDefs205Theory; 
val () = new_theory "vfmStateTest205";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs205";
val () = export_theory_no_docs ();
