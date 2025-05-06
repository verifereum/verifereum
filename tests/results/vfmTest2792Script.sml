open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2792Theory;
val () = new_theory "vfmTest2792";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2792") $ get_result_defs "vfmTestDefs2792";
val () = export_theory_no_docs ();
