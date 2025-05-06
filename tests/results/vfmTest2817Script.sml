open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2817Theory;
val () = new_theory "vfmTest2817";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2817") $ get_result_defs "vfmTestDefs2817";
val () = export_theory_no_docs ();
