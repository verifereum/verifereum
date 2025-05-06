open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2500Theory;
val () = new_theory "vfmTest2500";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2500") $ get_result_defs "vfmTestDefs2500";
val () = export_theory_no_docs ();
