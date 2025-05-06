open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2171Theory;
val () = new_theory "vfmTest2171";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2171") $ get_result_defs "vfmTestDefs2171";
val () = export_theory_no_docs ();
