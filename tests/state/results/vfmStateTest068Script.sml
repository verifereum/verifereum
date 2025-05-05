open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs068Theory;
val () = new_theory "vfmStateTest068";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs068") $ get_result_defs "vfmStateTestDefs068";
val () = export_theory_no_docs ();
