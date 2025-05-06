open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1132Theory;
val () = new_theory "vfmTest1132";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1132") $ get_result_defs "vfmTestDefs1132";
val () = export_theory_no_docs ();
