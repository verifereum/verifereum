open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0747Theory;
val () = new_theory "vfmTest0747";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0747") $ get_result_defs "vfmTestDefs0747";
val () = export_theory_no_docs ();
