open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0192Theory;
val () = new_theory "vfmTest0192";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0192") $ get_result_defs "vfmTestDefs0192";
val () = export_theory_no_docs ();
