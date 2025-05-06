open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2488Theory;
val () = new_theory "vfmTest2488";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2488") $ get_result_defs "vfmTestDefs2488";
val () = export_theory_no_docs ();
