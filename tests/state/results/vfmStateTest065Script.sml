open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs065Theory;
val () = new_theory "vfmStateTest065";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs065") $ get_result_defs "vfmStateTestDefs065";
val () = export_theory_no_docs ();
