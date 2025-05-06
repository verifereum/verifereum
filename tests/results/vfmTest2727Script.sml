open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2727Theory;
val () = new_theory "vfmTest2727";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2727") $ get_result_defs "vfmTestDefs2727";
val () = export_theory_no_docs ();
