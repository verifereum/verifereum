open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2146Theory;
val () = new_theory "vfmTest2146";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2146") $ get_result_defs "vfmTestDefs2146";
val () = export_theory_no_docs ();
