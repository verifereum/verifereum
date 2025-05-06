open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0650Theory;
val () = new_theory "vfmTest0650";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0650") $ get_result_defs "vfmTestDefs0650";
val () = export_theory_no_docs ();
