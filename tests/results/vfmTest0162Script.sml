open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0162Theory;
val () = new_theory "vfmTest0162";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0162") $ get_result_defs "vfmTestDefs0162";
val () = export_theory_no_docs ();
