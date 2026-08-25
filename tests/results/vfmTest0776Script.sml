Theory vfmTest0776[no_sig_docs]
Ancestors vfmTestDefs0776
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0776_0.nsv"];
val thyn = "vfmTestDefs0776";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
