open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0120Theory;
val () = new_theory "vfmTest0120";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0120") $ get_result_defs "vfmTestDefs0120";
val () = export_theory_no_docs ();
