open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2315Theory;
val () = new_theory "vfmTest2315";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2315") $ get_result_defs "vfmTestDefs2315";
val () = export_theory_no_docs ();
