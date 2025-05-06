open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0847Theory;
val () = new_theory "vfmTest0847";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0847") $ get_result_defs "vfmTestDefs0847";
val () = export_theory_no_docs ();
