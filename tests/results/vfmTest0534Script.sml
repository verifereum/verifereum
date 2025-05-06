open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0534Theory;
val () = new_theory "vfmTest0534";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0534") $ get_result_defs "vfmTestDefs0534";
val () = export_theory_no_docs ();
