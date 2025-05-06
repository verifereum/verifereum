open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2281Theory;
val () = new_theory "vfmTest2281";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2281") $ get_result_defs "vfmTestDefs2281";
val () = export_theory_no_docs ();
