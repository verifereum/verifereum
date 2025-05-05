open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs183Theory;
val () = new_theory "vfmStateTest183";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs183") $ get_result_defs "vfmStateTestDefs183";
val () = export_theory_no_docs ();
