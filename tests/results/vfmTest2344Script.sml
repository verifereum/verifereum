Theory vfmTest2344[no_sig_docs]
Ancestors vfmTestDefs2344
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2344_0.nsv", "result2344_1.nsv", "result2344_2.nsv", "result2344_3.nsv", "result2344_4.nsv", "result2344_5.nsv", "result2344_6.nsv", "result2344_7.nsv", "result2344_8.nsv", "result2344_9.nsv", "result2344_10.nsv", "result2344_11.nsv"];
val thyn = "vfmTestDefs2344";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
