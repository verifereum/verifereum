open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0464Theory;
val () = new_theory "vfmTest0464";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0464") $ get_result_defs "vfmTestDefs0464";
val () = export_theory_no_docs ();
