open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2109Theory;
val () = new_theory "vfmTest2109";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2109") $ get_result_defs "vfmTestDefs2109";
val () = export_theory_no_docs ();
