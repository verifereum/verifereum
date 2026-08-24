Theory vfmTest2753[no_sig_docs]
Ancestors vfmTestDefs2753
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2753_0.nsv", "result2753_1.nsv", "result2753_2.nsv", "result2753_3.nsv"];
val thyn = "vfmTestDefs2753";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
