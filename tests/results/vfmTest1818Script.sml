open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1818Theory;
val () = new_theory "vfmTest1818";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1818") $ get_result_defs "vfmTestDefs1818";
val () = export_theory_no_docs ();
