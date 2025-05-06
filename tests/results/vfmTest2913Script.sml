open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2913Theory;
val () = new_theory "vfmTest2913";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2913") $ get_result_defs "vfmTestDefs2913";
val () = export_theory_no_docs ();
