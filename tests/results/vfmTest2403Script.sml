open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2403Theory;
val () = new_theory "vfmTest2403";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2403") $ get_result_defs "vfmTestDefs2403";
val () = export_theory_no_docs ();
