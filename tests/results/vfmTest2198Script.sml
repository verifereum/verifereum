Theory vfmTest2198[no_sig_docs]
Ancestors vfmTestDefs2198
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2198_0.nsv", "result2198_1.nsv", "result2198_2.nsv", "result2198_3.nsv", "result2198_4.nsv", "result2198_5.nsv", "result2198_6.nsv", "result2198_7.nsv", "result2198_8.nsv", "result2198_9.nsv", "result2198_10.nsv"];
val thyn = "vfmTestDefs2198";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
