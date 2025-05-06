open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0950Theory;
val () = new_theory "vfmTest0950";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0950") $ get_result_defs "vfmTestDefs0950";
val () = export_theory_no_docs ();
