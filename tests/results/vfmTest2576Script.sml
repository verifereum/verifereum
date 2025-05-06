open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2576Theory;
val () = new_theory "vfmTest2576";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2576") $ get_result_defs "vfmTestDefs2576";
val () = export_theory_no_docs ();
