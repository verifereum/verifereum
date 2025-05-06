open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2350Theory;
val () = new_theory "vfmTest2350";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2350") $ get_result_defs "vfmTestDefs2350";
val () = export_theory_no_docs ();
