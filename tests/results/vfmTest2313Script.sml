open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2313Theory;
val () = new_theory "vfmTest2313";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2313") $ get_result_defs "vfmTestDefs2313";
val () = export_theory_no_docs ();
