open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1013Theory;
val () = new_theory "vfmTest1013";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1013") $ get_result_defs "vfmTestDefs1013";
val () = export_theory_no_docs ();
