open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0857Theory;
val () = new_theory "vfmTest0857";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0857") $ get_result_defs "vfmTestDefs0857";
val () = export_theory_no_docs ();
