open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0377Theory;
val () = new_theory "vfmTest0377";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0377") $ get_result_defs "vfmTestDefs0377";
val () = export_theory_no_docs ();
