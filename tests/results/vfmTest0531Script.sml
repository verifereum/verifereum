open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0531Theory;
val () = new_theory "vfmTest0531";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0531") $ get_result_defs "vfmTestDefs0531";
val () = export_theory_no_docs ();
