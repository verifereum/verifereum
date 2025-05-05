open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs185Theory;
val () = new_theory "vfmStateTest185";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs185") $ get_result_defs "vfmStateTestDefs185";
val () = export_theory_no_docs ();
