open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0365Theory;
val () = new_theory "vfmTest0365";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0365") $ get_result_defs "vfmTestDefs0365";
val () = export_theory_no_docs ();
