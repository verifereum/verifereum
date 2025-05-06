open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0205Theory;
val () = new_theory "vfmTest0205";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0205") $ get_result_defs "vfmTestDefs0205";
val () = export_theory_no_docs ();
