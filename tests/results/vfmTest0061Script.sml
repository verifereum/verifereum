open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0061Theory;
val () = new_theory "vfmTest0061";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0061") $ get_result_defs "vfmTestDefs0061";
val () = export_theory_no_docs ();
