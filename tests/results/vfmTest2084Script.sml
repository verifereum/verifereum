Theory vfmTest2084[no_sig_docs]
Ancestors vfmTestDefs2084
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2084_0.nsv", "result2084_1.nsv", "result2084_2.nsv", "result2084_3.nsv", "result2084_4.nsv", "result2084_5.nsv", "result2084_6.nsv", "result2084_7.nsv", "result2084_8.nsv"];
val thyn = "vfmTestDefs2084";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
