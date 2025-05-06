open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2618Theory;
val () = new_theory "vfmTest2618";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2618") $ get_result_defs "vfmTestDefs2618";
val () = export_theory_no_docs ();
