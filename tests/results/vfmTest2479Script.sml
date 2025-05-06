open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2479Theory;
val () = new_theory "vfmTest2479";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2479") $ get_result_defs "vfmTestDefs2479";
val () = export_theory_no_docs ();
