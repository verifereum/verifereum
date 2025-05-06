open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2304Theory;
val () = new_theory "vfmTest2304";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2304") $ get_result_defs "vfmTestDefs2304";
val () = export_theory_no_docs ();
