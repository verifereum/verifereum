open HolKernel vfmTestLib vfmStateTestDefs178Theory; 
val () = new_theory "vfmStateTest178";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs178";
val () = export_theory_no_docs ();
