open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0903Theory;
val () = new_theory "vfmTest0903";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0903") $ get_result_defs "vfmTestDefs0903";
val () = export_theory_no_docs ();
