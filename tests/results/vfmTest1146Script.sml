open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1146Theory;
val () = new_theory "vfmTest1146";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1146") $ get_result_defs "vfmTestDefs1146";
val () = export_theory_no_docs ();
