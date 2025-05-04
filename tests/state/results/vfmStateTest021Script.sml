open HolKernel vfmTestLib vfmStateTestDefs021Theory; 
val () = new_theory "vfmStateTest021";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs021";
val () = export_theory_no_docs ();
