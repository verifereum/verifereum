open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2797Theory;
val () = new_theory "vfmTest2797";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2797") $ get_result_defs "vfmTestDefs2797";
val () = export_theory_no_docs ();
