open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2919Theory;
val () = new_theory "vfmTest2919";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2919") $ get_result_defs "vfmTestDefs2919";
val () = export_theory_no_docs ();
