open HolKernel vfmTestLib vfmStateTestDefs072Theory; 
val () = new_theory "vfmStateTest072";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs072";
val () = export_theory_no_docs ();
