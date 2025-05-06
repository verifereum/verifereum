open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0483Theory;
val () = new_theory "vfmTest0483";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0483") $ get_result_defs "vfmTestDefs0483";
val () = export_theory_no_docs ();
