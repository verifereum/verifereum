Theory vfmTest2953[no_sig_docs]
Ancestors vfmTestDefs2953
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2953_0.nsv", "result2953_1.nsv", "result2953_2.nsv", "result2953_3.nsv", "result2953_4.nsv"];
val thyn = "vfmTestDefs2953";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
