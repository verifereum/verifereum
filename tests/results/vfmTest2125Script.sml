open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2125Theory;
val () = new_theory "vfmTest2125";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2125") $ get_result_defs "vfmTestDefs2125";
val () = export_theory_no_docs ();
