open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2065Theory;
val () = new_theory "vfmTest2065";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2065") $ get_result_defs "vfmTestDefs2065";
val () = export_theory_no_docs ();
