open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0896Theory;
val () = new_theory "vfmTest0896";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0896") $ get_result_defs "vfmTestDefs0896";
val () = export_theory_no_docs ();
