open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0885Theory;
val () = new_theory "vfmTest0885";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0885") $ get_result_defs "vfmTestDefs0885";
val () = export_theory_no_docs ();
