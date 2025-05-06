open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0806Theory;
val () = new_theory "vfmTest0806";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0806") $ get_result_defs "vfmTestDefs0806";
val () = export_theory_no_docs ();
