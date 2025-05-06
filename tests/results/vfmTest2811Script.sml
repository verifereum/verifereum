open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2811Theory;
val () = new_theory "vfmTest2811";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2811") $ get_result_defs "vfmTestDefs2811";
val () = export_theory_no_docs ();
