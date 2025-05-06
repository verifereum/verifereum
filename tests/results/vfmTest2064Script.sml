open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2064Theory;
val () = new_theory "vfmTest2064";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2064") $ get_result_defs "vfmTestDefs2064";
val () = export_theory_no_docs ();
