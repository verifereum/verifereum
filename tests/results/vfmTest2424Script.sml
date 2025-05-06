open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2424Theory;
val () = new_theory "vfmTest2424";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2424") $ get_result_defs "vfmTestDefs2424";
val () = export_theory_no_docs ();
