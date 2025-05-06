open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0510Theory;
val () = new_theory "vfmTest0510";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0510") $ get_result_defs "vfmTestDefs0510";
val () = export_theory_no_docs ();
