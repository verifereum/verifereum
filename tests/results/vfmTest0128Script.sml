open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0128Theory;
val () = new_theory "vfmTest0128";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0128") $ get_result_defs "vfmTestDefs0128";
val () = export_theory_no_docs ();
