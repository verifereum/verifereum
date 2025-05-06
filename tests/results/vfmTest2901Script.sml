open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2901Theory;
val () = new_theory "vfmTest2901";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2901") $ get_result_defs "vfmTestDefs2901";
val () = export_theory_no_docs ();
