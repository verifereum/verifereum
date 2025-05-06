open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0242Theory;
val () = new_theory "vfmTest0242";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0242") $ get_result_defs "vfmTestDefs0242";
val () = export_theory_no_docs ();
