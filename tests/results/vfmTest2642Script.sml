open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2642Theory;
val () = new_theory "vfmTest2642";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2642") $ get_result_defs "vfmTestDefs2642";
val () = export_theory_no_docs ();
