open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2414Theory;
val () = new_theory "vfmTest2414";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2414") $ get_result_defs "vfmTestDefs2414";
val () = export_theory_no_docs ();
