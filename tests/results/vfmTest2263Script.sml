open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2263Theory;
val () = new_theory "vfmTest2263";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2263") $ get_result_defs "vfmTestDefs2263";
val () = export_theory_no_docs ();
