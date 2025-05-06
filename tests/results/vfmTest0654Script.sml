open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0654Theory;
val () = new_theory "vfmTest0654";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0654") $ get_result_defs "vfmTestDefs0654";
val () = export_theory_no_docs ();
