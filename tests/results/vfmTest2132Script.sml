open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2132Theory;
val () = new_theory "vfmTest2132";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2132") $ get_result_defs "vfmTestDefs2132";
val () = export_theory_no_docs ();
