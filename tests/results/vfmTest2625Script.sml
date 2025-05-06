open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2625Theory;
val () = new_theory "vfmTest2625";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2625") $ get_result_defs "vfmTestDefs2625";
val () = export_theory_no_docs ();
