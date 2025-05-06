open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2734Theory;
val () = new_theory "vfmTest2734";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2734") $ get_result_defs "vfmTestDefs2734";
val () = export_theory_no_docs ();
