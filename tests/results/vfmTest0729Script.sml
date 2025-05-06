open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0729Theory;
val () = new_theory "vfmTest0729";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0729") $ get_result_defs "vfmTestDefs0729";
val () = export_theory_no_docs ();
