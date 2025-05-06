open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0326Theory;
val () = new_theory "vfmTest0326";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0326") $ get_result_defs "vfmTestDefs0326";
val () = export_theory_no_docs ();
