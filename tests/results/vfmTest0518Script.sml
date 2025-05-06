open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0518Theory;
val () = new_theory "vfmTest0518";
val thyn = "vfmTestDefs0518";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
