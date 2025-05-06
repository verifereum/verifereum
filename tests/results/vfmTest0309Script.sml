open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0309Theory;
val () = new_theory "vfmTest0309";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0309") $ get_result_defs "vfmTestDefs0309";
val () = export_theory_no_docs ();
