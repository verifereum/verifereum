open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2028Theory;
val () = new_theory "vfmTest2028";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2028") $ get_result_defs "vfmTestDefs2028";
val () = export_theory_no_docs ();
