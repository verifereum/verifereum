open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2896Theory;
val () = new_theory "vfmTest2896";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2896") $ get_result_defs "vfmTestDefs2896";
val () = export_theory_no_docs ();
