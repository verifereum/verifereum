open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0219Theory;
val () = new_theory "vfmTest0219";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0219") $ get_result_defs "vfmTestDefs0219";
val () = export_theory_no_docs ();
