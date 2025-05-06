open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0440Theory;
val () = new_theory "vfmTest0440";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0440") $ get_result_defs "vfmTestDefs0440";
val () = export_theory_no_docs ();
