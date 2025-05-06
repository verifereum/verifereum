open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2644Theory;
val () = new_theory "vfmTest2644";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2644") $ get_result_defs "vfmTestDefs2644";
val () = export_theory_no_docs ();
