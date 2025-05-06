open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2127Theory;
val () = new_theory "vfmTest2127";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2127") $ get_result_defs "vfmTestDefs2127";
val () = export_theory_no_docs ();
