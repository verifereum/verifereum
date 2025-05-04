open HolKernel vfmTestLib vfmStateTestDefs028Theory; 
val () = new_theory "vfmStateTest028";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs028";
val () = export_theory_no_docs ();
