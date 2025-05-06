open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2669Theory;
val () = new_theory "vfmTest2669";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2669") $ get_result_defs "vfmTestDefs2669";
val () = export_theory_no_docs ();
