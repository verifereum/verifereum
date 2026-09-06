Theory vfmTest2264[no_sig_docs]
Ancestors vfmTestDefs2264
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2264_0.nsv", "result2264_1.nsv", "result2264_2.nsv", "result2264_3.nsv", "result2264_4.nsv", "result2264_5.nsv", "result2264_6.nsv", "result2264_7.nsv", "result2264_8.nsv", "result2264_9.nsv"];
val thyn = "vfmTestDefs2264";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
