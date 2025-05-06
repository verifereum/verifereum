open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2489Theory;
val () = new_theory "vfmTest2489";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2489") $ get_result_defs "vfmTestDefs2489";
val () = export_theory_no_docs ();
