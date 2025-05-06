open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0241Theory;
val () = new_theory "vfmTest0241";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0241") $ get_result_defs "vfmTestDefs0241";
val () = export_theory_no_docs ();
