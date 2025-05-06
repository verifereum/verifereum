open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2552Theory;
val () = new_theory "vfmTest2552";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2552") $ get_result_defs "vfmTestDefs2552";
val () = export_theory_no_docs ();
