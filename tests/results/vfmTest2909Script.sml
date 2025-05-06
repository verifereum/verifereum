open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2909Theory;
val () = new_theory "vfmTest2909";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2909") $ get_result_defs "vfmTestDefs2909";
val () = export_theory_no_docs ();
