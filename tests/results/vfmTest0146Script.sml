open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0146Theory;
val () = new_theory "vfmTest0146";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0146") $ get_result_defs "vfmTestDefs0146";
val () = export_theory_no_docs ();
