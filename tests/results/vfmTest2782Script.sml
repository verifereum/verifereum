open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2782Theory;
val () = new_theory "vfmTest2782";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2782") $ get_result_defs "vfmTestDefs2782";
val () = export_theory_no_docs ();
