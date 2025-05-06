open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2463Theory;
val () = new_theory "vfmTest2463";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2463") $ get_result_defs "vfmTestDefs2463";
val () = export_theory_no_docs ();
