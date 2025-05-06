open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0165Theory;
val () = new_theory "vfmTest0165";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0165") $ get_result_defs "vfmTestDefs0165";
val () = export_theory_no_docs ();
