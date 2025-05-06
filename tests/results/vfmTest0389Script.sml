open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0389Theory;
val () = new_theory "vfmTest0389";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0389") $ get_result_defs "vfmTestDefs0389";
val () = export_theory_no_docs ();
