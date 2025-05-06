open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0890Theory;
val () = new_theory "vfmTest0890";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0890") $ get_result_defs "vfmTestDefs0890";
val () = export_theory_no_docs ();
