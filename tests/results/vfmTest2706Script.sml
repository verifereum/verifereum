open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2706Theory;
val () = new_theory "vfmTest2706";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2706") $ get_result_defs "vfmTestDefs2706";
val () = export_theory_no_docs ();
