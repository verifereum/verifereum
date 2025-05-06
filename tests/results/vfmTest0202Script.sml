open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0202Theory;
val () = new_theory "vfmTest0202";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0202") $ get_result_defs "vfmTestDefs0202";
val () = export_theory_no_docs ();
