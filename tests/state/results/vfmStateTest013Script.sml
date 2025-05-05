open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs013Theory;
val () = new_theory "vfmStateTest013";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs013") $ get_result_defs "vfmStateTestDefs013";
val () = export_theory_no_docs ();
