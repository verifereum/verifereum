open HolKernel vfmTestLib vfmStateTestDefs085Theory; 
val () = new_theory "vfmStateTest085";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs085";
val () = export_theory_no_docs ();
