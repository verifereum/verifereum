open HolKernel vfmTestLib vfmStateTestDefs106Theory; 
val () = new_theory "vfmStateTest106";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs106";
val () = export_theory_no_docs ();
