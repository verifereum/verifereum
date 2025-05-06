open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2352Theory;
val () = new_theory "vfmTest2352";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2352") $ get_result_defs "vfmTestDefs2352";
val () = export_theory_no_docs ();
