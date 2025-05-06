open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0434Theory;
val () = new_theory "vfmTest0434";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0434") $ get_result_defs "vfmTestDefs0434";
val () = export_theory_no_docs ();
