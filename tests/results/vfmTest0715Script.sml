open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0715Theory;
val () = new_theory "vfmTest0715";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0715") $ get_result_defs "vfmTestDefs0715";
val () = export_theory_no_docs ();
