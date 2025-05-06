open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2052Theory;
val () = new_theory "vfmTest2052";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2052") $ get_result_defs "vfmTestDefs2052";
val () = export_theory_no_docs ();
