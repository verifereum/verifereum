open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0361Theory;
val () = new_theory "vfmTest0361";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0361") $ get_result_defs "vfmTestDefs0361";
val () = export_theory_no_docs ();
