open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2553Theory;
val () = new_theory "vfmTest2553";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2553") $ get_result_defs "vfmTestDefs2553";
val () = export_theory_no_docs ();
