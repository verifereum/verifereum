open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2201Theory;
val () = new_theory "vfmTest2201";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2201") $ get_result_defs "vfmTestDefs2201";
val () = export_theory_no_docs ();
