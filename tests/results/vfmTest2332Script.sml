open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2332Theory;
val () = new_theory "vfmTest2332";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2332") $ get_result_defs "vfmTestDefs2332";
val () = export_theory_no_docs ();
