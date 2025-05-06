open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0726Theory;
val () = new_theory "vfmTest0726";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0726") $ get_result_defs "vfmTestDefs0726";
val () = export_theory_no_docs ();
