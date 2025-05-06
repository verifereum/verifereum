open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0566Theory;
val () = new_theory "vfmTest0566";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0566") $ get_result_defs "vfmTestDefs0566";
val () = export_theory_no_docs ();
