open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2818Theory;
val () = new_theory "vfmTest2818";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2818") $ get_result_defs "vfmTestDefs2818";
val () = export_theory_no_docs ();
