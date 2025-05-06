open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0795Theory;
val () = new_theory "vfmTest0795";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0795") $ get_result_defs "vfmTestDefs0795";
val () = export_theory_no_docs ();
