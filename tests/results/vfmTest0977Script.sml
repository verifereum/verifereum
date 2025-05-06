open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0977Theory;
val () = new_theory "vfmTest0977";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0977") $ get_result_defs "vfmTestDefs0977";
val () = export_theory_no_docs ();
