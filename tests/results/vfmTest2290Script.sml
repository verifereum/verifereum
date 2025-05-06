open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2290Theory;
val () = new_theory "vfmTest2290";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2290") $ get_result_defs "vfmTestDefs2290";
val () = export_theory_no_docs ();
