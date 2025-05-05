open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs169Theory;
val () = new_theory "vfmStateTest169";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs169") $ get_result_defs "vfmStateTestDefs169";
val () = export_theory_no_docs ();
