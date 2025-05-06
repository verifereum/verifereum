open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2855Theory;
val () = new_theory "vfmTest2855";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2855") $ get_result_defs "vfmTestDefs2855";
val () = export_theory_no_docs ();
