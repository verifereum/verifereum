open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0634Theory;
val () = new_theory "vfmTest0634";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0634") $ get_result_defs "vfmTestDefs0634";
val () = export_theory_no_docs ();
