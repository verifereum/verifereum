open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2251Theory;
val () = new_theory "vfmTest2251";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2251") $ get_result_defs "vfmTestDefs2251";
val () = export_theory_no_docs ();
