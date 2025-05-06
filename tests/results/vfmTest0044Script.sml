open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0044Theory;
val () = new_theory "vfmTest0044";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0044") $ get_result_defs "vfmTestDefs0044";
val () = export_theory_no_docs ();
