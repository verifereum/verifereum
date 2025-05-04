open HolKernel vfmTestLib vfmStateTestDefs194Theory; 
val () = new_theory "vfmStateTest194";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs194";
val () = export_theory_no_docs ();
