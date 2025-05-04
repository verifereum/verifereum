open HolKernel vfmTestLib vfmStateTestDefs084Theory; 
val () = new_theory "vfmStateTest084";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs084";
val () = export_theory_no_docs ();
