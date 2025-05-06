open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0476Theory;
val () = new_theory "vfmTest0476";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0476") $ get_result_defs "vfmTestDefs0476";
val () = export_theory_no_docs ();
