open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1392Theory;
val () = new_theory "vfmTest1392";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1392") $ get_result_defs "vfmTestDefs1392";
val () = export_theory_no_docs ();
