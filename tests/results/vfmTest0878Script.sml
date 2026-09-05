Theory vfmTest0878[no_sig_docs]
Ancestors vfmTestDefs0878
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0878_0.nsv", "result0878_1.nsv"];
val thyn = "vfmTestDefs0878";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
