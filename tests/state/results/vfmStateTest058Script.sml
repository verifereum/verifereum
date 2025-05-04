open HolKernel vfmTestLib vfmStateTestDefs058Theory; 
val () = new_theory "vfmStateTest058";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs058";
val () = export_theory_no_docs ();
