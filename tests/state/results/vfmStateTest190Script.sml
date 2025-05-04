open HolKernel vfmTestLib vfmStateTestDefs190Theory; 
val () = new_theory "vfmStateTest190";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs190";
val () = export_theory_no_docs ();
