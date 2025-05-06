open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2749Theory;
val () = new_theory "vfmTest2749";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2749") $ get_result_defs "vfmTestDefs2749";
val () = export_theory_no_docs ();
