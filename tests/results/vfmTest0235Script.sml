open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0235Theory;
val () = new_theory "vfmTest0235";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0235") $ get_result_defs "vfmTestDefs0235";
val () = export_theory_no_docs ();
