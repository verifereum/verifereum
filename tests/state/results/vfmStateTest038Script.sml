open HolKernel vfmTestLib vfmStateTestDefs038Theory; 
val () = new_theory "vfmStateTest038";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs038";
val () = export_theory_no_docs ();
