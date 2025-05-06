open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0181Theory;
val () = new_theory "vfmTest0181";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0181") $ get_result_defs "vfmTestDefs0181";
val () = export_theory_no_docs ();
