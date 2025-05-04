open HolKernel vfmTestLib vfmStateTestDefs001Theory; 
val () = new_theory "vfmStateTest001";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs001";
val () = export_theory_no_docs ();
