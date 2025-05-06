open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0264Theory;
val () = new_theory "vfmTest0264";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0264") $ get_result_defs "vfmTestDefs0264";
val () = export_theory_no_docs ();
