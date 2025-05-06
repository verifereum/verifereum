open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0007Theory;
val () = new_theory "vfmTest0007";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0007") $ get_result_defs "vfmTestDefs0007";
val () = export_theory_no_docs ();
