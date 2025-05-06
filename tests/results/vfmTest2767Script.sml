open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2767Theory;
val () = new_theory "vfmTest2767";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2767") $ get_result_defs "vfmTestDefs2767";
val () = export_theory_no_docs ();
