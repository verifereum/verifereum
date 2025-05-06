open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0427Theory;
val () = new_theory "vfmTest0427";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0427") $ get_result_defs "vfmTestDefs0427";
val () = export_theory_no_docs ();
