open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2557Theory;
val () = new_theory "vfmTest2557";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2557") $ get_result_defs "vfmTestDefs2557";
val () = export_theory_no_docs ();
