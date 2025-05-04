open HolKernel vfmTestLib vfmStateTestDefs110Theory; 
val () = new_theory "vfmStateTest110";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs110";
val () = export_theory_no_docs ();
