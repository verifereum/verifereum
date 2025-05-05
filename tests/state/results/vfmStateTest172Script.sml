open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs172Theory;
val () = new_theory "vfmStateTest172";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs172") $ get_result_defs "vfmStateTestDefs172";
val () = export_theory_no_docs ();
