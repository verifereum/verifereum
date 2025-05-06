open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0204Theory;
val () = new_theory "vfmTest0204";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0204") $ get_result_defs "vfmTestDefs0204";
val () = export_theory_no_docs ();
