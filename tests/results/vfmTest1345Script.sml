open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1345Theory;
val () = new_theory "vfmTest1345";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1345") $ get_result_defs "vfmTestDefs1345";
val () = export_theory_no_docs ();
