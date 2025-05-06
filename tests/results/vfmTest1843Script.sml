open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1843Theory;
val () = new_theory "vfmTest1843";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1843") $ get_result_defs "vfmTestDefs1843";
val () = export_theory_no_docs ();
