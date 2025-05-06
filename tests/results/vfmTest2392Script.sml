open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2392Theory;
val () = new_theory "vfmTest2392";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2392") $ get_result_defs "vfmTestDefs2392";
val () = export_theory_no_docs ();
