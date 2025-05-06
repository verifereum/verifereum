open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2319Theory;
val () = new_theory "vfmTest2319";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2319") $ get_result_defs "vfmTestDefs2319";
val () = export_theory_no_docs ();
