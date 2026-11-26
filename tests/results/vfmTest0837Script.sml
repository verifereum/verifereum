Theory vfmTest0837[no_sig_docs]
Ancestors vfmTestDefs0837
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0837_0.nsv"];
val thyn = "vfmTestDefs0837";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
