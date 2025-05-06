open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0916Theory;
val () = new_theory "vfmTest0916";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0916") $ get_result_defs "vfmTestDefs0916";
val () = export_theory_no_docs ();
