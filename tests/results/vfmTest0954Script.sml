open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0954Theory;
val () = new_theory "vfmTest0954";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0954") $ get_result_defs "vfmTestDefs0954";
val () = export_theory_no_docs ();
