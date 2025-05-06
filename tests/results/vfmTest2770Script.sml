open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2770Theory;
val () = new_theory "vfmTest2770";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2770") $ get_result_defs "vfmTestDefs2770";
val () = export_theory_no_docs ();
