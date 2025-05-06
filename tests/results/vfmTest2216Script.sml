open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2216Theory;
val () = new_theory "vfmTest2216";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2216") $ get_result_defs "vfmTestDefs2216";
val () = export_theory_no_docs ();
