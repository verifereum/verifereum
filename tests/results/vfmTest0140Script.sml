open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0140Theory;
val () = new_theory "vfmTest0140";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0140") $ get_result_defs "vfmTestDefs0140";
val () = export_theory_no_docs ();
