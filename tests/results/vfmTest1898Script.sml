open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1898Theory;
val () = new_theory "vfmTest1898";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1898") $ get_result_defs "vfmTestDefs1898";
val () = export_theory_no_docs ();
