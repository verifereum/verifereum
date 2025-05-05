open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs096Theory;
val () = new_theory "vfmStateTest096";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs096") $ get_result_defs "vfmStateTestDefs096";
val () = export_theory_no_docs ();
