open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2063Theory;
val () = new_theory "vfmTest2063";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2063") $ get_result_defs "vfmTestDefs2063";
val () = export_theory_no_docs ();
