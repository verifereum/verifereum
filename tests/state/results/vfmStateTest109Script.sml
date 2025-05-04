open HolKernel vfmTestLib vfmStateTestDefs109Theory; 
val () = new_theory "vfmStateTest109";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs109";
val () = export_theory_no_docs ();
