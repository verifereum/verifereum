open HolKernel vfmTestLib vfmStateTestDefs119Theory; 
val () = new_theory "vfmStateTest119";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs119";
val () = export_theory_no_docs ();
