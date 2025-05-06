open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0341Theory;
val () = new_theory "vfmTest0341";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0341") $ get_result_defs "vfmTestDefs0341";
val () = export_theory_no_docs ();
