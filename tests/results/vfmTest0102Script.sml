open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0102Theory;
val () = new_theory "vfmTest0102";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0102") $ get_result_defs "vfmTestDefs0102";
val () = export_theory_no_docs ();
