open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0016Theory;
val () = new_theory "vfmTest0016";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0016") $ get_result_defs "vfmTestDefs0016";
val () = export_theory_no_docs ();
