open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0355Theory;
val () = new_theory "vfmTest0355";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0355") $ get_result_defs "vfmTestDefs0355";
val () = export_theory_no_docs ();
