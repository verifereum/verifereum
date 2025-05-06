open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0573Theory;
val () = new_theory "vfmTest0573";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0573") $ get_result_defs "vfmTestDefs0573";
val () = export_theory_no_docs ();
