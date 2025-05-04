open HolKernel vfmTestLib vfmStateTestDefs168Theory; 
val () = new_theory "vfmStateTest168";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs168";
val () = export_theory_no_docs ();
