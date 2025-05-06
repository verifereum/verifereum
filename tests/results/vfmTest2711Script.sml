open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2711Theory;
val () = new_theory "vfmTest2711";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2711") $ get_result_defs "vfmTestDefs2711";
val () = export_theory_no_docs ();
