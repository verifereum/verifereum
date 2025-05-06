open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0222Theory;
val () = new_theory "vfmTest0222";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0222") $ get_result_defs "vfmTestDefs0222";
val () = export_theory_no_docs ();
