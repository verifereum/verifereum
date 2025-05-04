open HolKernel vfmTestLib vfmStateTestDefs145Theory; 
val () = new_theory "vfmStateTest145";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs145";
val () = export_theory_no_docs ();
