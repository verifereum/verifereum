open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0177Theory;
val () = new_theory "vfmTest0177";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0177") $ get_result_defs "vfmTestDefs0177";
val () = export_theory_no_docs ();
