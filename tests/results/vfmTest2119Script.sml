open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2119Theory;
val () = new_theory "vfmTest2119";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2119") $ get_result_defs "vfmTestDefs2119";
val () = export_theory_no_docs ();
