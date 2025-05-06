open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0308Theory;
val () = new_theory "vfmTest0308";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0308") $ get_result_defs "vfmTestDefs0308";
val () = export_theory_no_docs ();
