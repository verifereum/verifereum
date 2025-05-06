open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0974Theory;
val () = new_theory "vfmTest0974";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0974") $ get_result_defs "vfmTestDefs0974";
val () = export_theory_no_docs ();
