open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0972Theory;
val () = new_theory "vfmTest0972";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0972") $ get_result_defs "vfmTestDefs0972";
val () = export_theory_no_docs ();
