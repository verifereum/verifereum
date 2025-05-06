open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2538Theory;
val () = new_theory "vfmTest2538";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2538") $ get_result_defs "vfmTestDefs2538";
val () = export_theory_no_docs ();
