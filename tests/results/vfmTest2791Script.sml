open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2791Theory;
val () = new_theory "vfmTest2791";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2791") $ get_result_defs "vfmTestDefs2791";
val () = export_theory_no_docs ();
