open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0478Theory;
val () = new_theory "vfmTest0478";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0478") $ get_result_defs "vfmTestDefs0478";
val () = export_theory_no_docs ();
