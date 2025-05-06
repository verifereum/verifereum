open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2417Theory;
val () = new_theory "vfmTest2417";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2417") $ get_result_defs "vfmTestDefs2417";
val () = export_theory_no_docs ();
