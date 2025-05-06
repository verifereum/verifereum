open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0593Theory;
val () = new_theory "vfmTest0593";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0593") $ get_result_defs "vfmTestDefs0593";
val () = export_theory_no_docs ();
