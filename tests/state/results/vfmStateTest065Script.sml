open HolKernel vfmTestLib vfmStateTestDefs065Theory; 
val () = new_theory "vfmStateTest065";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs065";
val () = export_theory_no_docs ();
