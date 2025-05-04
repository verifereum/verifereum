open HolKernel vfmTestLib vfmStateTestDefs041Theory; 
val () = new_theory "vfmStateTest041";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs041";
val () = export_theory_no_docs ();
