open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2539Theory;
val () = new_theory "vfmTest2539";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2539") $ get_result_defs "vfmTestDefs2539";
val () = export_theory_no_docs ();
