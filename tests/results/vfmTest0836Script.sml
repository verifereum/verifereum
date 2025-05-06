open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0836Theory;
val () = new_theory "vfmTest0836";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0836") $ get_result_defs "vfmTestDefs0836";
val () = export_theory_no_docs ();
