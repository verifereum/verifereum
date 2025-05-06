open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1538Theory;
val () = new_theory "vfmTest1538";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1538") $ get_result_defs "vfmTestDefs1538";
val () = export_theory_no_docs ();
