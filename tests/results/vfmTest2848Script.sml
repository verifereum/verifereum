open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2848Theory;
val () = new_theory "vfmTest2848";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2848") $ get_result_defs "vfmTestDefs2848";
val () = export_theory_no_docs ();
