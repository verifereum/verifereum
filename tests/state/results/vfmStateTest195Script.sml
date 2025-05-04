open HolKernel vfmTestLib vfmStateTestDefs195Theory; 
val () = new_theory "vfmStateTest195";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs195";
val () = export_theory_no_docs ();
