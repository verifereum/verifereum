open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2328Theory;
val () = new_theory "vfmTest2328";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2328") $ get_result_defs "vfmTestDefs2328";
val () = export_theory_no_docs ();
