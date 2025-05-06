open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0438Theory;
val () = new_theory "vfmTest0438";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0438") $ get_result_defs "vfmTestDefs0438";
val () = export_theory_no_docs ();
