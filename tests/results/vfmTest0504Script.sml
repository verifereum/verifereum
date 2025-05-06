open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0504Theory;
val () = new_theory "vfmTest0504";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0504") $ get_result_defs "vfmTestDefs0504";
val () = export_theory_no_docs ();
