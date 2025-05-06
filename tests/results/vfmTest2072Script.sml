open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2072Theory;
val () = new_theory "vfmTest2072";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2072") $ get_result_defs "vfmTestDefs2072";
val () = export_theory_no_docs ();
