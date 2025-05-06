open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0178Theory;
val () = new_theory "vfmTest0178";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0178") $ get_result_defs "vfmTestDefs0178";
val () = export_theory_no_docs ();
