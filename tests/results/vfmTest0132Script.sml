open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0132Theory;
val () = new_theory "vfmTest0132";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0132") $ get_result_defs "vfmTestDefs0132";
val () = export_theory_no_docs ();
