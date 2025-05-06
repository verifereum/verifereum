open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2211Theory;
val () = new_theory "vfmTest2211";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2211") $ get_result_defs "vfmTestDefs2211";
val () = export_theory_no_docs ();
