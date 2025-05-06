open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1286Theory;
val () = new_theory "vfmTest1286";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1286") $ get_result_defs "vfmTestDefs1286";
val () = export_theory_no_docs ();
