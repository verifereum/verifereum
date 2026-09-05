Theory vfmTest0027[no_sig_docs]
Ancestors vfmTestDefs0027
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0027_0.nsv", "result0027_1.nsv"];
val thyn = "vfmTestDefs0027";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
