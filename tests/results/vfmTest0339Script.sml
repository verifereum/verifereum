open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0339Theory;
val () = new_theory "vfmTest0339";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0339") $ get_result_defs "vfmTestDefs0339";
val () = export_theory_no_docs ();
